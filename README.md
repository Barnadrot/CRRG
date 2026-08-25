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
| `CandidateEdge` | Typed promotion queue entry with exact Lean proposition |
| `SealedCandidate` | Immutable candidate target for promotion attempts |

## Repository layout

```
CRRG/
  CRRG/           Core library modules
  Test/Synthetic/  Unit tests for each primitive
  scripts/         Build, audit, and promotion scripts
  Spec.md          Full specification
  AGENTS.md        Agent interaction contract
```

## Building

Requires Lean 4 v4.30.0 (via elan).

```bash
lake build CRRG    # build the library
lake build Test    # build and check all tests
```

## Integration

CRRG is consumed as a pinned Lake dependency by downstream projects:

```
downstream-project -> CRRG @ <exact SHA>
```

CRRG never imports project-specific mathematics. The downstream project owns its graph declarations and adapter code.

## Scripts

- `scripts/crrg-check` — build + test + axiom audit
- `scripts/crrg-status` — human-readable state summary
- `scripts/crrg-lineage` — print axiom dependencies of a declaration
- `scripts/crrg-seal` — validate a candidate declaration before sealing
- `scripts/crrg-promote-check` — verify a theorem inhabits a sealed target

## Trust model

- Every edge is a Lean theorem (no prose-only arrows)
- Every split proves coverage
- Guards produce sibling branches (never silently dropped)
- Exceptions are never deleted
- No synthetic global percentage

## License

MIT
