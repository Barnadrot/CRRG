# CRRG v0.4: the closed core and the classical library

Two Lean packages that re-build CRRG's certified research state from the ground up, closing the gaps of v0.10
(the root of this repository). CRRG's rule stays the same: an agent **proposes** a typed transition, a verifier
**checks** its witness, and the certified state **commits** it or stays unchanged.

| Package | What it is | Trust base |
|---|---|---|
| [`crrg-core/`](crrg-core/) | The certified core: state, typed transitions and their commit, frontier invariant, guarded composition, the "certified easier" ladder with record-low credit, sealing, and a runner that admits submissions | Lean core only; no Mathlib, no `Classical.choice` in the headline theorems |
| [`crrg-classical/`](crrg-classical/) | The same machinery on Mathlib objects: the Dershowitz–Manna bridge, "no run earns infinitely many credits", the stall rule, the evidence ledger, crux families, and the list-bound/class-cap converse | Mathlib (pinned `c5ea00351c`) and Lean's standard axioms |

**What was verified.** Both packages were built from clean with `leanprover/lean4:v4.30.0`, with these results
(logs in each package):
- `crrg-core`: 37 headline declarations, none depending on `Classical.choice`, and no `sorry`. The runner suite
  passes 42/42 (40 cases), and both seal probes produce different seals. The log is `crrg-core/BUILD.log`.
- `crrg-classical`: 1015 build jobs. All 42 printed declarations use only `propext`, `Classical.choice` and
  `Quot.sound`, and there is no `sorry`. The log is `crrg-classical/BUILD.log`.

**Examples are synthetic.** The crux-family, lane and guard examples are made-up instances that exercise the
mechanism. They model no particular problem.

**Not included.** Applications of CRRG to specific research problems, such as adapters that re-express a result of
a seat-written proof tree as a CRRG route. Such adapters sit at "gate-level trust until gate v2": their terms are
kernel-checked, but the tree they import is not independently certified. They stay with their projects.

**Status.** This is a prototype, not yet fully closed. The open items are listed in `crrg-core/STATUS.md`:
- a refinement proof of the runner's commit loop;
- a production seal (sha256 over `lean4export`);
- detectors for propositional restatements.

One known runner issue: in `runner/guard_fields.py`, an `expr` check whose variable is missing raises
`NameError` instead of failing the field.
