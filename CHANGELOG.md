# CRRG Changelog

Audit trail for the Certified Research Reduction Graph implementation.

This file is the **plan of record** for spec conformance. Section 1 is the
conformance matrix: every normative requirement in [`Spec.md`](Spec.md), its
implementation status, and the change that last touched it. Section 2 is the
chronological change log. Section 3 records deliberate deviations from the spec
and the reason for each.

Conventions:

- **Spec references** use the section numbers as they appear in `Spec.md` after
  the v0.4 heading repair (`SPEC-01`). Where the pre-repair spec used a
  conflicting subsection number, both are given, as `§14 (12.x)`.
- **Status** is one of `DONE`, `PARTIAL`, `MISSING`, `DEFERRED` (out of scope
  for the current stage, with the gating stage named), or `DOWNSTREAM` (belongs
  to a consuming project's adapter, not to standalone CRRG).
- A requirement is only `DONE` when it is exercised by the test suite or a gate
  script, not merely when code exists.

---

## 0. Provenance

- `be47e28` Initial commit
- `a2ac02b` spec.md
- `8b521ed` Implement CRRG spec as standalone Lean 4 library — **the
  as-delivered implementation. It does not compile.** No `lake build` had been
  run against it. Six of eight core modules and all six test modules were
  rejected by the elaborator. Everything from `CHG-01` onward builds on this
  baseline.

The out-of-repo copy `../CERTIFIED_RESEARCH_REDUCTION_GRAPH_SPEC.md` is spec
**v0.1** and is deliberately left untouched as an independent validation
reference. It is *not* a mirror of `Spec.md` (v0.3, becoming v0.4): it predates
the standalone-repository architecture (§2), the typed candidate graph (§8), and
the staged implementation plan (§15). Do not reconcile the two.

---

## 1. Spec conformance matrix

### §2 Repository architecture

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 2.1 | CRRG imports no project-specific vocabulary | DONE | |
| 2.2 | Standalone repository layout | DONE | `SPEC-04` |
| 2.2 | Core is dependency-light (Lean core only) | DONE | `DEV-01` |
| 2.2 | `Test/YukonReplay/` fixture | DEFERRED | Stage B |
| 2.3 | Downstream adapter shape | DONE | `CHG-14` |
| 2.4 | Sibling-checkout development builds | DONE | `CHG-14` |
| 2.4 | Pinned-SHA integration builds | DEFERRED | needs a published CRRG SHA |

### §5 (4.x) Trust model

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 4.1 | Frozen root | DOWNSTREAM | the root is a downstream declaration |
| 4.2 | Every edge is a Lean theorem | DONE | prose arrows are not representable |
| 4.3 | Every split proves coverage | DONE | `Split.discharge` |
| 4.4 | Guards produce sibling branches | DONE | `GuardedMap` |
| 4.5 | Exceptions are never deleted | DONE | `EscapeMap` |
| 4.6 | No synthetic global percentage | MISSING | no gate forbids emitting one |

### §6 (5.x) Lean API

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 5.1 | `Goal`, `Goal.Proved`, `Edge`, `Edge.id/trans` | DONE | |
| 5.1 | `Edge` universe explicit, not inferred | MISSING | inferred `Prop`; a later data field silently changes it |
| 5.2 | `Split` with coverage proof | DONE | |
| 5.3 | `BadNode`, `BadNode.Closed` | DONE | `DEV-01` |
| 5.3 | `WitnessMap`, `WitnessSplit`, `closed_parent` | DONE | `CHG-11` |
| 5.3 | Witness / branch / task types universe-polymorphic | MISSING | pinned to `Type 0` |
| 5.4 | `EscapeMap` | DONE | |
| 5.5 | `GuardedMap` consuming both truth values | DONE | |

### §7 (6.x) Root package and live frontier

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 6.1–6.2 | Exact root goal and root seam | DOWNSTREAM | |
| 6.3 | `Frontier` package | DONE | |
| 6.4 | Replace one leaf by a child via `Edge`, siblings preserved | DONE | `CHG-10` |
| 6.4 | Replace one leaf by children via `Split`, siblings preserved | DONE | `CHG-10` |

### §8 (7.x) Typed candidate graph and promotion queue

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 7.1 | No prose edges; every candidate has an exact Lean proposition | DONE | |
| 7.2 | Candidate edges expose all composition debt (Shape A / Shape B) | MISSING | |
| 7.3 | Record carries `sourceIds`, `targetId`, `expectedTheoremName` | MISSING | only `id`, `targetProp`, `status` exist |
| 7.4 | Lifecycle `DRAFT → SEALED_UNVERIFIED → CERTIFIED` | PARTIAL | `sealedUnverified` is unreachable |
| 7.4 | Terminal states reachable and final | MISSING | a refuted candidate can still be promoted |
| 7.5 | Sealed target immutable for the attempt | PARTIAL | convention, not enforced |
| 7.6 | Promotion is not prize progress | DONE | no aggregate is emitted |
| 7.7 | Certified frontier rendered separately from the promotion queue | MISSING | no renderer |
| 7.8 | History: seal hash, commit, timestamp, status, reason | PARTIAL | seal hash only, `CHG-09` |

### §9 LDB counterexample vocabulary

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 9 | `ListViolation` and LDB-specific vocabulary | DOWNSTREAM | `SPEC-03` — contradicts §2.1 |

### §10 (8.x) Quantitative partial progress

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 8.1 | Structural progress via certified splits | DONE | |
| 8.2 | Monotone parameterized families with an explicit monotonicity theorem | MISSING | no representation at all |
| 8.2 | Numerical reward only for a strictly stronger parameter under identical node semantics | MISSING | depends on the above |
| 8.3 | Certified root-bound evaluator | DEFERRED | spec says do not implement yet |

### §11 Agent task contract

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 11.1–11.6 | Task contract documented | DONE | `AGENTS.md` |
| 11 | Binary `OPEN → CLOSED` reward | PARTIAL | documented, not machine-emitted |
| 11 | Monotone-leaf reward variant | MISSING | depends on §8.2 |

### §12 (10.x) Graph-change protocol

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 10.1 | Refinement requires a compiled coverage theorem | DONE | `CHG-10` |
| 10.2 | Invalid refinements rejected | PARTIAL | list not exhausted |
| 10.3 | Retirement removes from the live frontier | DONE | `CHG-10` |

### §14 (12.x) Verification integration

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 12.2.1 | Build the live graph and every registered closed-task module | DONE | `crrg-check` |
| 12.2.2 | Reject banned constructs | MISSING | no banned-construct scan |
| 12.2.3 | Transitive `collectAxioms` over the live graph | DONE | `CHG-08` |
| 12.2.4 | Type-link the root exactly | DONE | `Frontier.rootIs` |
| 12.2.5 | Type-link each task theorem exactly | DONE | `Frontier.leafIs` |
| 12.2.6 | Print only `OPEN` / `CLOSED` / `INVALID` per task | MISSING | no task-status renderer |
| 12.2.7 | Print no aggregate count or percentage | MISSING | not asserted by any gate |
| 12.3 | Lean is authority over rendered state | DONE | |

### §15 Stage A — synthetic unit tests

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| A.1 | Direct `Edge` composition | DONE | |
| A.2 | Exhaustive `Split` | DONE | |
| A.3 | Witness-level `WitnessSplit` | DONE | `CHG-11` |
| A.4 | Guarded refinement, failed guard explicit | DONE | |
| A.5 | Escape refinement, exception explicit | DONE | |
| A.6 | Route retirement without deleting lineage | DONE | `CHG-11` |
| A.7 | DAG reuse: one theorem discharges multiple parents | DONE | `CHG-11` |
| A.8 | Negative tests for missing branches and weakened children | DONE | `CHG-07` |

Stages B–G are out of scope for the current work and remain `DEFERRED`.

### §18 Acceptance criteria (v0.3)

| # | Criterion | Status |
|---|-----------|--------|
| 0 | Builds standalone, imports nothing project-specific | DONE |
| 0a | Downstream consumes CRRG as a dependency, no second copy | DONE |
| 0b | Sibling-checkout and pinned-SHA integration both build | PARTIAL — sibling verified, SHA pending |
| 1–4 | Exact root, closeRoot link, two landed leaves, `k0` metadata | DOWNSTREAM |
| 5 | A leaf refines into two children only with a compiled coverage theorem | DONE |
| 6 | A guarded refinement visibly retains the guard-failure branch | DONE |
| 7 | An escape refinement visibly retains the exceptional branch | DONE |
| 8 | The gate rejects a weakened child / missing branch in a negative test | DONE |
| 9–11 | Prize gate unchanged, no percentage, Disprove side unchanged | DOWNSTREAM |
| 12 | Every candidate has an exact compilable proposition | DONE |
| 13 | A sealed target cannot be weakened in place | PARTIAL |
| 14 | Promotion requires the exact proposition plus the axiom/type-link gate | DONE |
| 15 | Yukon damaged-proof cost measured before directing live Soundness | DEFERRED — Stage C |
| 16 | An agent gets a correct binary reward from one exact leaf | PARTIAL |

---

## 2. Change log

### Unreleased

Entries are added as `CHG-nn` (implementation) and `SPEC-nn` (specification) as
work lands.

---

## 3. Deliberate deviations from spec

Recorded here so a reviewer can distinguish an intentional amendment from an
implementation error. Each has a corresponding `Spec.md` edit.

Nothing yet.
