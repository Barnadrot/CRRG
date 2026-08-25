# CRRG — Certified Research Reduction Graph

A kernel-checked partial-progress architecture for autonomous mathematical research.

CRRG makes proof decompositions visible to the Lean 4 kernel, providing exact local reward signals for research agents working on grand challenge problems.

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
| `CandidateEdge` | Typed promotion queue entry with exact Lean proposition |
| `SealedCandidate` | Immutable candidate target for promotion attempts |

## Repository layout

```
CRRG/
  CRRG/            Core library modules
  Test/Support/    Test harness (#expect_failure)
  Test/Synthetic/  Unit tests for each primitive, incl. asserted rejections
  scripts/         Build, audit, and promotion scripts
  Spec.md          Full specification
  AGENTS.md        Agent interaction contract
```

## Building

Requires Lean 4 v4.30.0 (via elan).

```bash
lake build CRRG        # build the library
lake build Test        # build and check all tests (incl. negative tests)
scripts/crrg-check     # full gate: library + tests + declarations + axiom audit
```

Note that `lake build` with no target builds only the `CRRG` library. CI must run
`scripts/crrg-check` (or `lake build Test` explicitly) to execute the tests.

## Integration

CRRG is consumed as a pinned Lake dependency by downstream projects:

```
downstream-project -> CRRG @ <exact SHA>
```

CRRG never imports project-specific mathematics. The downstream project owns its graph declarations and adapter code.

## Scripts

- `scripts/crrg-check` — build + tests + declaration audit + transitive axiom audit
- `scripts/crrg-audit` — transitive axiom audit alone (Spec 12.2 item 3)
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
- Every split proves coverage
- Guards produce sibling branches (never silently dropped)
- Exceptions are never deleted
- No synthetic global percentage

## License

MIT
