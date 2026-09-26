#!/usr/bin/env python3
"""Runs the runner on every case in runner/tests/ and compares with expect.json (exactly).

Forgery cases are also run with --continue-after-lint, and must then add LINEAGE.
Writes runner/TESTS.log and exits non-zero on any mismatch.
"""

import concurrent.futures as cf
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TESTS = os.path.join(HERE, "tests")
RUNNER = os.path.join(HERE, "crrg_runner.py")


def run(case, bypass):
    cmd = [sys.executable, RUNNER, os.path.join(TESTS, case, "manifest.json")]
    if bypass:
        cmd.append("--continue-after-lint")
    p = subprocess.run(cmd, capture_output=True, text=True)
    try:
        return json.loads(p.stdout)
    except json.JSONDecodeError:
        return {"verdict": "runner-crash", "reasons": [], "stderr": p.stderr[-2000:]}


def check(case):
    exp = json.load(open(os.path.join(TESTS, case, "expect.json"), encoding="utf-8"))
    rows = []
    got = run(case, False)
    ok = got["verdict"] == exp["verdict"] and got["reasons"] == exp["reasons"]
    if "tag" in exp:
        ok = ok and got.get("tag") == exp["tag"]
    rows.append((case, "", exp, got, ok))
    if "reasons_if_lint_bypassed" in exp:
        got2 = run(case, True)
        ok2 = got2["verdict"] == "reject" and got2["reasons"] == exp["reasons_if_lint_bypassed"]
        rows.append((case, " (lint bypassed)", {"verdict": "reject",
                     "reasons": exp["reasons_if_lint_bypassed"]}, got2, ok2))
    return rows


def main():
    cases = sorted(os.listdir(TESTS))
    with cf.ThreadPoolExecutor(max_workers=int(os.environ.get("CRRG_JOBS", "4"))) as ex:
        results = [r for rows in ex.map(check, cases) for r in rows]
    lines, fails = [], 0
    for case, suffix, exp, got, ok in results:
        fails += not ok
        want = f"{exp['verdict']} {exp['reasons']}" + (f" tag={exp['tag']}" if exp.get("tag") else "")
        have = f"{got['verdict']} {got['reasons']}" + (f" tag={got.get('tag')}" if got.get("tag") else "")
        lines.append(f"{'PASS' if ok else 'FAIL'}  {case}{suffix}: expected {want}; got {have}")
        if not ok:
            lines.append("      " + json.dumps(got.get("checks", got), ensure_ascii=False)[:3000])
    lines.append(f"\n{len(results) - fails}/{len(results)} runs as expected "
                 f"({len(cases)} cases; forgery cases also run with the lint bypassed)")
    text = "\n".join(lines)
    print(text)
    open(os.path.join(HERE, "TESTS.log"), "w", encoding="utf-8").write(text + "\n")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
