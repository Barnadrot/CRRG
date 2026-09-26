#!/usr/bin/env python3
"""CRRG gate runner (Phase 1a).

Usage:  crrg_runner.py MANIFEST.json [--continue-after-lint]

Takes one submitted Lean file and a state (named in the manifest) and emits ONE machine-readable
verdict (JSON on stdout):

    {"verdict": "accept" | "reject", "reasons": [CODE, ...], "tag": ..., "checks": {...}}

Checks, in order (see RUNNER.md for what each guarantees):
  lint     the submission is meta-free and imports only allowed, meta-free modules (text check)
  compile  the submission elaborates and is kernel-checked on its own, without CRRGTools in scope
  axioms   every submitted constant uses only propext, Quot.sound, Classical.choice; no new axioms
  lineage  no constant outside CRRGCore mentions a private core name
  d1       the move's fresh claims are not definitionally equal to a learned conflict (reject) or
           to a live registered key (reject: the move must reuse that key with Child.old)
  commit   the kernel commit: State.commit S m is .ok (tag) or .error (Reject)
  r1       every definition the submission declares and a fresh child claim uses (plus any leaves
           named in the manifest) is sealed or has a typed agreement lemma

A submission that fails the lint is never compiled or executed (its later checks are "skipped"),
unless --continue-after-lint is given. That flag exists only for the negative-control suite, to
show that the lineage audit catches a forgery even if the lint were bypassed (defence in depth).

Manifest fields (paths relative to the manifest):
  submission   the submitted .lean file
  imports      extra modules the submission may import besides CRRGCore (e.g. the state's module)
  state        Lean term: the committed state S
  move         Lean term: the proposed move m : Move S (usually a name in the submission)
  r1           optional {"sealed": [namespaces], "agreements": [lemma names], "leaves": [extra]}
  guard_claim  optional: the crux-family edge the contract consumes and how it discharges EVERY guard
               field (runner/guard_fields.py; families/<family>.json). Codes: GUARD_UNKNOWN_EDGE,
               GUARD_FIELD_MISSING, GUARD_FIELD_FAILS, GUARD_JOINT_SPLIT
"""

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from guard_fields import check_guard_claim  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.dirname(HERE)  # crrg-core/
SUBMISSION_MODULE = "CRRGSubmission"
TIMEOUT = 600

# Commands that run or define metaprograms, or change the trusted code path.
FORBIDDEN_COMMANDS = [
    "elab", "elab_rules", "macro", "macro_rules", "syntax", "declare_syntax_cat",
    "run_cmd", "run_elab", "run_meta", "initialize", "builtin_initialize",
    "#eval", "#eval!", "#exit", "unsafe", "implemented_by", "extern",
]
# Modules whose import gives access to the meta framework or to the runner's own tools.
META_ROOTS = ["Lean", "Lake", "Std", "CRRGTools"]
# Options a submission may set.
ALLOWED_OPTIONS = ["maxHeartbeats", "maxRecDepth", "autoImplicit", "relaxedAutoImplicit",
                   "linter.", "pp."]


def strip_comments_and_strings(src):
    """Remove nested block comments, line comments and string literals (keeping line structure)."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth > 0:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
        elif src[i] == '"':
            i += 1
            while i < n and src[i] != '"':
                i += 2 if src[i] == "\\" else 1
            i += 1
            out.append('""')
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def imports_of(text):
    return re.findall(r"^\s*import\s+([\w.]+)", text, flags=re.M)


def module_file(mod):
    path = os.path.join(PKG, *mod.split(".")) + ".lean"
    return path if os.path.exists(path) else None


def meta_imports_reachable(mod, seen=None):
    """The meta modules reachable from `mod` through package sources (transitive)."""
    seen = set() if seen is None else seen
    if mod in seen:
        return []
    seen.add(mod)
    if mod.split(".")[0] in META_ROOTS:
        return [mod]
    path = module_file(mod)
    if path is None:
        return []  # Init and other toolchain prelude modules
    text = strip_comments_and_strings(open(path, encoding="utf-8").read())
    found = []
    for m in imports_of(text):
        found += meta_imports_reachable(m, seen)
    return found


def lint(src, allowed_imports):
    reasons, details = [], []
    text = strip_comments_and_strings(src)
    for m in imports_of(text):
        if m.split(".")[0] in META_ROOTS:
            reasons.append("META_IMPORT")
            details.append(f"imports {m}")
        elif m != "CRRGCore" and m not in allowed_imports:
            reasons.append("IMPORT_NOT_ALLOWED")
            details.append(f"imports {m}, not in the allow-list")
        else:
            bad = meta_imports_reachable(m)
            if bad:
                reasons.append("META_IMPORT")
                details.append(f"imports {m}, which reaches {sorted(set(bad))}")
    for cmd in FORBIDDEN_COMMANDS:
        pat = r"(?<![\w.'#])" + re.escape(cmd) + r"(?![\w.'!])"
        for mt in re.finditer(pat, text):
            line = text.count("\n", 0, mt.start()) + 1
            reasons.append("META_COMMAND")
            details.append(f"line {line}: {cmd}")
    for mt in re.finditer(r"\bset_option\s+([\w.]+)", text):
        opt = mt.group(1)
        if not any(opt == a or (a.endswith(".") and opt.startswith(a)) for a in ALLOWED_OPTIONS):
            line = text.count("\n", 0, mt.start()) + 1
            reasons.append("FORBIDDEN_OPTION")
            details.append(f"line {line}: set_option {opt}")
    return sorted(set(reasons)), details


def lean_path():
    out = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=PKG,
                         capture_output=True, text=True, check=True)
    return out.stdout.strip()


def run(cmd, env, cwd):
    try:
        p = subprocess.run(cmd, env=env, cwd=cwd, capture_output=True, text=True, timeout=TIMEOUT)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return None, "", "timeout"


def parse_json_messages(stdout):
    msgs = []
    for line in stdout.splitlines():
        line = line.strip()
        if line.startswith("{"):
            try:
                msgs.append(json.loads(line))
            except json.JSONDecodeError:
                pass
    return msgs


def main(argv):
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    manifest_path = os.path.abspath(argv[1])
    continue_after_lint = "--continue-after-lint" in argv
    base = os.path.dirname(manifest_path)
    man = json.load(open(manifest_path, encoding="utf-8"))
    src = open(os.path.join(base, man["submission"]), encoding="utf-8").read()
    allowed = man.get("imports", [])
    checks, reasons, tag = {}, [], None

    # guard-fields rule (crux families): data only, checked before anything runs
    if "guard_claim" in man:
        gr, gd = check_guard_claim(man["guard_claim"])
        checks["guards"] = {"ok": not gr, "reasons": gr, "details": gd}
        reasons += gr

    # (b) lint
    lr, ld = lint(src, allowed)
    checks["lint"] = {"ok": not lr, "reasons": lr, "details": ld}
    reasons += lr
    later = ["compile", "axioms", "lineage", "d1", "commit", "r1"]
    if lr and not continue_after_lint:
        for c in later:
            checks[c] = {"ok": None, "skipped": "lint failed: the submission is not executed"}
        return emit(reasons, tag, checks)

    env = dict(os.environ)
    lp = lean_path()
    work = tempfile.mkdtemp(prefix="crrg-runner-")
    try:
        # compile the submission on its own (CRRGTools is not in scope unless it imports it)
        sub = os.path.join(work, SUBMISSION_MODULE + ".lean")
        shutil.copy(os.path.join(base, man["submission"]), sub)
        env["LEAN_PATH"] = lp
        rc, out, err = run(["lean", "--json", f"--root={work}", "-o",
                            os.path.join(work, SUBMISSION_MODULE + ".olean"), sub], env, work)
        msgs = parse_json_messages(out)
        errs = [m["data"] for m in msgs if m.get("severity") == "error"]
        if rc != 0 or errs:
            code = "TIMEOUT" if rc is None else "COMPILE_ERROR"
            checks["compile"] = {"ok": False, "reasons": [code], "details": errs or [err.strip()]}
            reasons.append(code)
            for c in later[1:]:
                checks[c] = {"ok": None, "skipped": "the submission does not compile"}
            return emit(reasons, tag, checks)
        checks["compile"] = {"ok": True}

        # the runner-owned driver: one check per line
        lines = ["import CRRGTools", f"import {SUBMISSION_MODULE}", "open CRRGCore"]
        where = {}

        def add(check, text):
            lines.append(text)
            where[len(lines)] = check

        add("axioms", f"#crrg_check_axioms {SUBMISSION_MODULE}")
        add("lineage", "#crrg_check_lineage")
        add("d1", f"#crrg_admit ({man['state']}) ({man['move']})")
        add("commit", f"#eval CRRGTools.commitSummary ({man['state']}) ({man['move']})")
        r1 = man.get("r1") or {}
        add("r1", f"#crrg_check_move_defs {SUBMISSION_MODULE} ({man['state']}) ({man['move']}) "
                  f"[{', '.join(r1.get('sealed', []))}] [{', '.join(r1.get('agreements', []))}]")
        if r1:
            for leaf in r1.get("leaves", []):
                add("r1", f"#crrg_check_defs_using {leaf} [{', '.join(r1['sealed'])}] "
                          f"[{', '.join(r1.get('agreements', []))}]")
        driver = os.path.join(work, "Driver.lean")
        open(driver, "w", encoding="utf-8").write("\n".join(lines) + "\n")
        env["LEAN_PATH"] = work + os.pathsep + lp
        rc, out, err = run(["lean", "--json", driver], env, work)
        msgs = parse_json_messages(out)

        per = {c: {"errors": [], "infos": []} for c in ["axioms", "lineage", "d1", "commit", "r1"]}
        other = []
        for m in msgs:
            c = where.get(m.get("pos", {}).get("line"))
            key = "errors" if m.get("severity") == "error" else "infos"
            (per[c][key] if c else other).append(m["data"])
        if rc is None:
            reasons.append("TIMEOUT")
        if other or (rc not in (0, 1) and rc is not None):
            reasons.append("DRIVER_ERROR")
            checks["driver"] = {"ok": False, "details": other or [err.strip()]}

        def verdict(c, code):
            ok = not per[c]["errors"]
            checks[c] = {"ok": ok, "details": per[c]["errors"] or per[c]["infos"]}
            if not ok:
                checks[c]["reasons"] = [code]
                reasons.append(code)

        verdict("axioms", "AXIOM")
        verdict("lineage", "LINEAGE")
        # D1: a conflict is an error; a reuse report is an info that still rejects the move
        d1_err = per["d1"]["errors"]
        d1_reuse = [i for i in per["d1"]["infos"] if "reuse keys" in i]
        if d1_err:
            code = "D1_CONFLICT" if any("learned conflict" in e for e in d1_err) else "D1_ERROR"
            checks["d1"] = {"ok": False, "reasons": [code], "details": d1_err}
            reasons.append(code)
        elif d1_reuse:
            checks["d1"] = {"ok": False, "reasons": ["D1_REUSE"], "details": d1_reuse}
            reasons.append("D1_REUSE")
        else:
            checks["d1"] = {"ok": True, "details": per["d1"]["infos"]}
        # commit
        line = next((i for i in per["commit"]["infos"] if "CRRG-COMMIT" in i), None)
        if not checks["axioms"]["ok"] and (per["commit"]["errors"] or line is None):
            # Lean refuses to evaluate a term that depends on sorry; the move is rejected anyway
            checks["commit"] = {"ok": None, "skipped": "not evaluated: disallowed axioms",
                                "details": per["commit"]["errors"]}
        elif per["commit"]["errors"] or line is None:
            checks["commit"] = {"ok": False, "reasons": ["COMMIT_ERROR"],
                                "details": per["commit"]["errors"]}
            reasons.append("COMMIT_ERROR")
        else:
            words = line.strip('"').split()
            name = words[2].split(".")[-1]
            outcome = " ".join([name] + words[3:])
            if words[1] == "ok":
                tag = name
                checks["commit"] = {"ok": True, "tag": tag}
            else:
                code = "COMMIT_REJECT:" + name
                checks["commit"] = {"ok": False, "reasons": [code], "reject": outcome}
                reasons.append(code)
        verdict("r1", "R1")
        return emit(reasons, tag, checks)
    finally:
        shutil.rmtree(work, ignore_errors=True)


def emit(reasons, tag, checks):
    reasons = sorted(set(reasons))
    v = {"verdict": "reject" if reasons else "accept", "reasons": reasons, "tag": tag,
         "checks": checks}
    print(json.dumps(v, indent=2, ensure_ascii=False))
    return 0 if not reasons else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
