"""Guard-fields rule for crux families.

A consuming contract lists, in its manifest's "guard_claim", the shared edge (arrow) it uses and, for
EVERY guard field of that edge, how it discharges the field. Values common to several fields may be
given once, as "instance". With the synthetic family families/demo.json:

    "guard_claim": {"family": "demo", "arrow": "toy-edge",
                    "instance": {"mode": 1, "m": 11, "k": 4, "lo": 20, "hi": 30},
                    "fields": {"x_window": {"x": 25},
                               "profile": {"witness": "w-1", "minDeg": 2, "mass": 36},
                               "m_certified": {"evidence": "certificate for m"}, ...}}

The check rejects:
  GUARD_UNKNOWN_EDGE     the family or arrow is not registered
  GUARD_FIELD_MISSING    a guard field is not listed, or a data field has no evidence reference
  GUARD_FIELD_FAILS      a decidable field fails on the values the contract supplies
  GUARD_JOINT_SPLIT      a joint field is discharged by more than one witness (a list of entries,
                         or entries naming different witnesses), i.e. typed as separate existentials
"""

import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
FAMILIES = os.path.join(os.path.dirname(HERE), "families")


def _value(env, spec, key_var="var", key_value="value", key_var2="var2", key_expr="expr"):
    if key_var2 in spec:
        return env.get(spec[key_var2])
    if key_expr in spec:
        return _expr(env, spec[key_expr])
    return spec.get(key_value)


def _expr(env, text):
    # tiny, fixed expressions only: "3*w-2", "p-1"
    allowed = {k: v for k, v in env.items() if isinstance(v, int)}
    for ch in text:
        if not (ch.isalnum() or ch in "*+-_ "):
            raise ValueError(f"bad expression {text}")
    return eval(text, {"__builtins__": {}}, allowed)  # noqa: S307 (fixed grammar above)


def evaluate(check, env):
    """Evaluate a guard check against the values a contract supplies. Missing values fail."""
    if "all" in check:
        return all(evaluate(c, env) for c in check["all"])
    op = check["op"]
    if op == "odd":
        v = env.get(check["var"])
        return isinstance(v, int) and v % 2 == 1
    if op == "divides":
        v, of = env.get(check["var"]), None
        try:
            of = _expr(env, check["of"])
        except Exception:
            return False
        return isinstance(v, int) and v != 0 and of % v == 0
    lhs = env.get(check["var"])
    rhs = _value(env, check)
    if lhs is None or rhs is None:
        return False
    try:
        return {"==": lhs == rhs, "<=": lhs <= rhs, ">=": lhs >= rhs,
                "<": lhs < rhs, ">": lhs > rhs}[op]
    except TypeError:
        return False


def load_edge(family, arrow):
    path = os.path.join(FAMILIES, f"{family}.json")
    if not os.path.exists(path):
        return None
    fam = json.load(open(path, encoding="utf-8"))
    return fam.get("shared_edges", {}).get(arrow)


def check_guard_claim(claim):
    """Returns (reasons, details) for a manifest's guard_claim."""
    reasons, details = [], []
    edge = load_edge(claim.get("family", ""), claim.get("arrow", ""))
    if edge is None:
        return ["GUARD_UNKNOWN_EDGE"], [f"no edge {claim.get('arrow')} in family {claim.get('family')}"]
    fields = claim.get("fields", {})
    seen = {}   # value name -> (field id, value) across all fields (v0.11.1)
    for g in edge["guard"]:
        fid = g["id"]
        entry = fields.get(fid)
        if entry is None:
            reasons.append("GUARD_FIELD_MISSING")
            details.append(f"{fid}: not listed")
            continue
        if g["kind"] == "data":
            if not (isinstance(entry, dict) and entry.get("evidence")):
                reasons.append("GUARD_FIELD_MISSING")
                details.append(f"{fid}: data obligation without an evidence reference")
            continue
        if g["kind"] == "joint":
            if isinstance(entry, list):
                witnesses = {e.get("witness") for e in entry if isinstance(e, dict)}
                if len(entry) > 1 or len(witnesses) > 1:
                    reasons.append("GUARD_JOINT_SPLIT")
                    details.append(f"{fid}: joint guard discharged by {len(entry)} separate witnesses "
                                   f"{sorted(w for w in witnesses if w)}; one witness must satisfy all parts")
                    continue
                entry = entry[0] if entry else {}
            if not entry.get("witness"):
                reasons.append("GUARD_FIELD_MISSING")
                details.append(f"{fid}: joint guard needs one named witness")
                continue
        # v0.11.1 (independent audit, 2026-09-29, S1-02): every field is discharged on ONE instance. A field may add
        # names, but it may not override a value of the shared instance, and two fields may not give one name two values.
        inst = claim.get("instance", {})
        vals = {k: v for k, v in entry.items() if k not in ("evidence", "witness")}
        clash = sorted(k for k, v in vals.items() if k in inst and inst[k] != v)
        if clash:
            reasons.append("GUARD_INCONSISTENT")
            details.append(f"{fid}: overrides the shared instance on {', '.join(clash)}")
        for k, v in vals.items():
            if k in seen and seen[k][1] != v:
                reasons.append("GUARD_INCONSISTENT")
                details.append(f"{fid}: {k} = {v!r} disagrees with {seen[k][0]} ({k} = {seen[k][1]!r})")
            seen.setdefault(k, (fid, v))
        env = dict(inst)
        env.update({k: v for k, v in entry.items() if k != "evidence"})
        if not evaluate(g["check"], env):
            reasons.append("GUARD_FIELD_FAILS")
            details.append(f"{fid}: fails on {json.dumps(entry, sort_keys=True)}")
    extra = sorted(set(fields) - {g["id"] for g in edge["guard"]})
    if extra:
        details.append(f"unused fields ignored: {extra}")
    return sorted(set(reasons)), details
