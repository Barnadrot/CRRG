# CRRG — Certified Research Reduction Graph

**Proof-carrying research-state transitions for long-horizon automated mathematics.**

CRRG is a Lean 4 library and orchestration layer for maintaining a faithful certified research state while untrusted agents explore, refine, split, close, refute, retire, and revisit mathematical obligations.

The core rule is simple:

> **Propose → verify → commit or reject.**

Agents may maintain arbitrary speculative working state, but the certified research state changes only when a machine-checkable witness establishes the transition-specific admissibility condition.

CRRG is **not** a scalar reward function. A green integrity check is not mathematical progress. The project’s existing terminal gate remains authoritative for terminal-objective reward; CRRG governs which intermediate research-state mutations may be admitted.

## Status

Current specification: **v0.10.0**.

The persistence layer is implemented and has been exercised in a live Reed–Solomon autoresearch deployment in `Barnadrot/proximity-research`. That deployment has produced certified refinements and closures, caught live semantic drift, deduplicated identical obligations, separated `NO_TRANSITION` from admitted graph movement, and exercised first- and second-order stall handling.

These observations validate the mechanism’s operation. They do **not** yet establish improved theorem-discovery efficiency; that remains an empirical research question.

See [`Spec.md`](Spec.md) for the normative design and [`CHANGELOG.md`](CHANGELOG.md) for the audit trail and implementation history.

## Why CRRG

Long-horizon formal research has a sparse terminal reward: the final theorem either checks or it does not. Between terminal advances, an agent may still:

- prove a substantive structural theorem;
- eliminate a route;
- expose a missing premise;
- replace one hard obligation by a certified sufficient refinement;
- decompose an obligation into an exhaustive split;
- accumulate useful research evidence without moving the certified graph.

Without an explicit state discipline, those intermediate steps are easy to confuse with progress, weaken accidentally, duplicate, or lose as context grows.

CRRG keeps three things separate:

```text
PROJECT REWARD
  the project’s external/canonical terminal gate

CERTIFIED RESEARCH-STATE MOVEMENT
  proof-carrying mutations of the faithful research state

RESEARCH EVIDENCE
  helper theorems, experiments, constructions, counterexamples, failed routes
```

Only the second category is CRRG graph movement.

## Core semantics

The mathematical core depends on **Lean core only** — no Mathlib — so consuming CRRG does not constrain a downstream project’s Mathlib version resolution.

| Type | Purpose |
|---|---|
| `Goal` | Proposition-level research obligation |
| `Edge parent child` | Kernel theorem `child.claim → parent.claim` |
| `Split parent` | Exhaustive decomposition whose children jointly discharge the parent |
| `BadNode` | Witness/counterexample node |
| `WitnessMap` | Maps parent witnesses into a child witness space |
| `WitnessSplit` | Exhaustively classifies parent witnesses into child branches |
| `GuardedMap` | Guarded transform retaining both pass and fail branches |
| `EscapeMap` | Normal/exceptional split with neither branch silently dropped |
| `Frontier root` | Current live obligations together implying the unchanged root |
| `Frontier.Transition source target` | First-class proof that closing `target` closes `source` |
| `DraftCandidate` | Editable candidate proposition before sealing |
| `SealedCandidate P` | Immutable exact proposition `P` awaiting resolution |
| `Outcome P` / `ResolvedCandidate P` | Certified, refuted, invalid, etc., with proof-carrying terminal states |
| `MonotoneFamily` / `Progress` | Exact quantitative movement inside one formally monotone family |
| `TerminalOutcome` | Separates admitted movement, valid `NO_TRANSITION`, rejection, and tooling failure |
| `StallState` | First-order repeated-`NO_TRANSITION` orchestration state |
| `CycleState` | Second-order `NOVELTY_REQUIRED` state after repeated completed stall cycles |

A frontier has the invariant:

```lean
(∀ t, (frontier.leaf t).claim) → root.claim
```

Accepted frontier mutations additionally expose a composable `Frontier.Transition`, so a chain

```text
F0 --T1--> F1 --T2--> ... --Tn--> Fn
```

has a kernel-produced composite showing that closure of `Fn` entails closure of the original root.

## Certified research-state channels

CRRG recognizes only the following certified channels:

1. actual project reward movement produced by the project’s existing terminal gate;
2. exact `OPEN → CLOSED` closure of an assigned leaf;
3. a certified refinement or exhaustive split preserving root closure;
4. exact quantitative improvement inside one formally monotone family;
5. promotion of a sealed candidate into certified state — formalization movement, not terminal reward.

Research evidence does not become a certified channel by accumulation, theorem count, graph depth, or prose confidence.

## Candidate and seal discipline

A sealed proposition is immutable per candidate ID. Changing the proposition requires a new ID.

CRRG’s semantic seal covers the target’s meaning plus its transitive in-scope semantic dependencies. Proof bodies of theorems are excluded; theorem types carry their meaning. External dependencies are pinned by manifests.

A claimed refutation must carry a proof of `¬ P` for the exact sealed proposition `P`.

## Persistence and orchestration

The v0.10 layer adds persistent research-state tooling without turning orchestration metadata into mathematical truth:

- canonical live-obligation identity derived from semantic seals;
- deduplication of multiple frontier positions carrying one proposition;
- append-only research episodes and mechanism records;
- checkpoints and research-evidence records;
- `NO_TRANSITION` as a valid research no-op, mechanically distinct from admitted movement;
- `STALLED` after repeated no-transition attempts on one obligation;
- `NOVELTY_REQUIRED` after repeated completed stall cycles, changing research mode rather than authorizing the agent to stop;
- auditable launch refusal / policy enforcement downstream.

The stall and novelty states are orchestration facts only. They assert nothing about theorem truth, difficulty, literature novelty, or whether another obligation is easier.

## Repository layout

```text
CRRG/
  CRRG/            generic Lean semantics — Lean core only
  CRRGTest/        shipped test support such as #expect_failure
  Test/Synthetic/  synthetic positive/negative regression tests
  scripts/         audit, seal, promotion, persistence and orchestration tooling
  Spec.md          sole normative design / execution document
  AGENTS.md        generic agent interaction contract
  CHANGELOG.md     implementation history and audit findings
```

Application mathematics does not belong in CRRG. Downstream projects own their graph declarations, research programmes, model adapters, and terminal reward gates.

## Building

Primary toolchain: Lean 4 v4.30.0. The portability gate also tests supported downstream toolchains listed in `scripts/portability-toolchains.txt`.

```bash
lake build CRRG
lake build CRRGTest Test
scripts/crrg-check
```

`scripts/crrg-check` is the full eight-step CRRG gate: script hygiene, core build, test build, cross-toolchain portability, declaration checks, transitive axiom audit, gate self-tests, and banned-construct scan.

A bare `lake build` does not execute the full acceptance gate.

## Integration

Consume CRRG as an exact pinned Lake dependency:

```text
downstream-project → CRRG @ <exact commit SHA>
```

CRRG never imports downstream theorem vocabulary.

For downstream semantic seals, set `CRRG_SEAL_SCOPE` to every editable application namespace that can affect the target meaning. An accidentally narrow scope is not a trustworthy seal.

Typical downstream configuration:

```bash
CRRG_WORKDIR=/path/to/project \
CRRG_IMPORTS=MyProject.ResearchGraph \
CRRG_AUDIT_NAMESPACES=MyProject \
scripts/crrg-promote-check MyProject.deliveredTheorem MyProject.SealedTarget
```

## Selected tooling

### Verification

- `scripts/crrg-check` — full CRRG acceptance gate
- `scripts/crrg-audit` — transitive axiom audit
- `scripts/crrg-banned` — banned-construct scan
- `scripts/crrg-forbid` — proof/type dependency exclusion audit
- `scripts/crrg-portability` — supported-toolchain build gate
- `scripts/crrg-selftest` — positive/negative controls for the gate tools

### Certified state

- `scripts/crrg-seal` — create or verify semantic seals
- `scripts/crrg-register-candidate` — append a fresh immutable candidate seal
- `scripts/crrg-promote-check` — exact type-link + axiom validation for a delivered proof
- `scripts/crrg-depth-check` — reduction-depth record validation

### Research orchestration

- `scripts/crrg-obligations` — canonical unique-obligation view
- `scripts/crrg-episode` — append-only episode / checkpoint / terminal log
- `scripts/crrg-mechanism` — append-only mechanism registry
- `scripts/crrg-evidence` — research-evidence substrate; no novelty score
- `scripts/crrg-live-run` — generic downstream launch contract

## Trust model

- Every certified edge is a Lean theorem; there are no prose-only certified arrows.
- Every exhaustive split carries a coverage proof.
- Guards and exceptional cases retain the branches required for sound composition.
- No certified theorem or promotion may depend on banned proof holes.
- A sealed target cannot be silently weakened in place.
- A broken seal is not repaired by re-baselining the same candidate ID.
- A refutation must carry an exact disproof.
- Frontier transitions compose rootward in Lean.
- Numerical movement is local to one formally monotone family; unrelated quantities have no exchange rate.
- `NO_TRANSITION`, stall counts, mechanism counts, novelty metadata, graph depth, and theorem counts are never scalar research reward.
- Tooling failures are reported as tooling failures, not mathematical findings.

## Scope and research status

CRRG is currently a research prototype, not a claim of solved long-horizon autoresearch.

The implemented mechanism addresses **admissibility, persistence, and auditability** of intermediate research state. It does not yet solve true mathematical novelty recognition, semantic equivalence of research mechanisms, strategic theorem selection, or automatic invention of the missing theorem. Those remain explicit research problems built on top of the certified substrate.

## License

MIT
