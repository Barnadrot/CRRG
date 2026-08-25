# CRRG Agent Contract

This document specifies how an autonomous research agent interacts with CRRG.

## What an agent receives

When assigned a task, an agent gets:

1. **Root lineage** — the declaration path from the Grand Challenge target to the assigned leaf.
2. **Exact target type** — a `theorem` signature or `example` that must compile unchanged.
3. **Allowed imports / writable files.**
4. **Sibling assumptions** — only previously proved theorem constants, never prose facts.
5. **Success condition** — kernel compilation + axiom audit + exact type-link.
   All three are checked by `scripts/crrg-promote-check`. A proof that compiles
   but depends on `sorry` is **not** a success; the gate rejects it.
6. **Failure output** — mathematical counterexample, impossibility theorem, or proposed split.

## Reward signal

The local reward is binary:

```
OPEN -> CLOSED
```

For a monotone parameterized leaf:

```
proved parameter p_old -> strictly stronger p_new
```

No aggregate percentage is ever computed. No synthetic global score exists.

## What an agent must NOT do

- Weaken the assigned leaf's proposition.
- Replace the target with an easier proxy.
- Add an uncertified assumption and claim the parent is solved.
- Propose a split without a compiled coverage theorem.
- Drop a guard-failure or escape branch.
- Modify CRRG core semantics while working on a task.

## Candidate promotion

An agent may be assigned a SEALED_UNVERIFIED candidate. The exact proposition is immutable for that attempt:

- Prove it exactly as stated → CERTIFIED
- Discover a missing premise → report as MALFORMED (new candidate ID needed)
- Show the statement is false → report as REFUTED
- Cannot prove it → leave unchanged (no reward, no penalty)

## Graph mutations

To refine a leaf into children, the agent must provide a `Split` or `WitnessSplit` with a compiled coverage theorem in the same commit, and apply it with `Frontier.splitLeaf` so that every sibling leaf is preserved. The orchestrator will not assign children as independent tasks until the refinement builds.

Retiring a route uses `Frontier.retireLeaf`, which requires an actual proof of
the leaf. Removing an obligation is never a bookkeeping edit.

## CRRG as dependency

CRRG is consumed as a pinned dependency by downstream projects. An agent working on a downstream leaf should not modify CRRG source code.
