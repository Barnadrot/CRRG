# CRRG — Certified Research Reduction Graph

A kernel-checked partial-progress architecture for autonomous mathematical research.

CRRG makes proof decompositions visible to the Lean 4 kernel, providing exact local reward signals for research agents working on grand challenge problems.

The core library depends on **Lean core only** — no Mathlib, so consuming it does
not constrain a downstream project's version resolution. See [`CHANGELOG.md`](CHANGELOG.md)
for the spec-conformance matrix and the full audit trail.

## Core primitives

| Type | Purpose |
|------|---------|
| `Goal` | A proposition-level research obligation |
| `Edge` | A kernel theorem showing one goal discharges another |
| `Split` | An exhaustive decomposition with a coverage proof |
| `BadNode` | A counterexample-type node (closed = empty) |
| `WitnessMap` | Maps parent witnesses to child witnesses |
| `WitnessSplit` | Exhaustive classifier from parent witnesses into branches |
| `GuardedMap` | Guard-based split retaining both pass and fail branches |
| `EscapeMap` | Two-way split for normal vs exceptional outcomes |
| `Frontier` | The live set of obligations closing the root |
| `Frontier.refineLeaf` | Replace one leaf via an `Edge`, preserving siblings |
| `Frontier.splitLeaf` | Replace one leaf by a `Split`'s branches, preserving siblings |
| `Frontier.retireLeaf` | Drop a leaf from the live frontier — requires a real proof |
| `DraftCandidate` | An editable candidate; target is still a field |
| `SealedCandidate P` | Sealed target — `P` is a type parameter, so it cannot be weakened |
| `Outcome P` | Terminal states; `certified` carries a proof, `refuted` a disproof |
| `ResolvedCandidate P` | Seal plus outcome, retained as history |
| `PromotionQueue` | Sealed-but-unresolved tasks; cannot close a root |
| `CompositionDebt` | Premise list plus conclusion; the target is computed from it |
| `MonotoneFamily` | A parameter order with its monotonicity theorem as a field |
| `Progress F old new` | The only numerical reward: a strict improvement, same family |
| `FrontierReport` | One line per task, `OPEN`/`CLOSED`/`INVALID`, no aggregate |

## Repository layout

```
CRRG/
  CRRG/            Core library modules — Lean core only
  CRRGTest/        Test support shipped to consumers (#expect_failure)
  Test/Synthetic/  Unit tests for each primitive, incl. asserted rejections
  scripts/         Build, audit, and promotion scripts
  Spec.md          Full specification
  AGENTS.md        Agent interaction contract
```

`CRRGTest` is a separate library: `import CRRG` does not pull it in. A downstream
adapter opts in to assert its *own* rejections — that a weakened leaf, an
incomplete split, or a dropped guard branch fails to compile:

```lean
import CRRGTest.ExpectFailure

#expect_failure
theorem weakenedLeaf : Edge myParent myEasierChild := ...
```

## Building

Requires Lean 4 v4.30.0 (via elan).

```bash
lake build CRRG        # build the library
lake build Test        # build and check all tests (incl. negative tests)
scripts/crrg-check     # the full seven-step gate
```

Note that `lake build` with no target builds only the `CRRG` library. CI must run
`scripts/crrg-check` (or `lake build Test` explicitly) to execute the tests.

The core is Lean-core-only, so it is consumed by projects pinning different
toolchains. `scripts/crrg-portability` builds the library and the full test
suite under every toolchain in `scripts/portability-toolchains.txt` and treats
any warning as a failure — a consumer inherits CRRG's warnings and cannot tell
them apart from its own. Both listed toolchains must be installed:

```bash
elan toolchain install leanprover/lean4:v4.30.0
elan toolchain install leanprover/lean4:v4.32.2
```

## Integration

CRRG is consumed as a pinned Lake dependency by downstream projects:

```
downstream-project -> CRRG @ <exact SHA>
```

CRRG never imports project-specific mathematics. The downstream project owns its graph declarations and adapter code.

## Scripts

- `scripts/crrg-check` — the full seven-step gate
- `scripts/crrg-portability` — clean build under every supported toolchain
- `scripts/crrg-audit` — transitive axiom audit (Spec §14.2 item 3)
- `scripts/crrg-banned` — banned-construct scan (Spec §14.2 item 2, §5.6, §14.2 item 7)
- `scripts/crrg-forbid` — transitive constant-dependency audit: "prove this
  without using that" (Spec §11 item 4)
- `scripts/crrg-selftest` — exercises each gate tool on a case it must accept
  and a case it must reject
- `scripts/crrg-status` — human-readable state summary
- `scripts/crrg-lineage` — print axiom dependencies of a declaration
- `scripts/crrg-seal` — print a candidate's exact type and seal hash before sealing
- `scripts/crrg-promote-check` — verify a theorem inhabits a sealed target *and*
  depends on no banned axiom

All scripts default to auditing CRRG itself. To point them at a downstream
ResearchGraph adapter:

```bash
CRRG_WORKDIR=/path/to/proximity-research CRRG_IMPORTS=ProximityPrize.Squeeze.Soundness.ResearchGraph.Current CRRG_AUDIT_NAMESPACES=ProximityPrize   scripts/crrg-promote-check MyProject.E17 MyProject.Candidates.E17Target
```

## Trust model

- Every edge is a Lean theorem (no prose-only arrows)
- No certified edge or promoted candidate may depend on `sorry`
- A sealed candidate target cannot be weakened in place — it is a type parameter
- A refutation must carry a disproof; a resolved candidate cannot be promoted
- Numerical reward only for a strictly stronger parameter in the *same* family
- The gate emits one line per task and no aggregate — `render_length` is a theorem
- Every split proves coverage
- Guards produce sibling branches (never silently dropped)
- Exceptions are never deleted
- No synthetic global percentage

## License

MIT
