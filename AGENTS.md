# CRRG Agent Contract

This document specifies the generic contract between an autonomous research agent and CRRG. Downstream deployments may add project-specific mathematics, resource policy, and model configuration, but may not weaken these rules.

## Research mandate

An exact admissible `OPEN` obligation is an active research mandate.

The following are **not** blockers:

- “I do not know how to prove this.”
- “No known theorem gives the required bound.”
- “This appears to require a new invariant.”
- “The literature stops here.”
- “A stronger candidate might be false.”
- “I need to choose constants.”
- “Further work requires novel mathematics.”

Those are descriptions of the research problem.

While an admissible obligation remains `OPEN`, tooling is available, and the operator has not explicitly stopped the programme, the research loop continues.

```text
OPEN             -> RESEARCH
NO_TRANSITION    -> CONTINUE
STALLED          -> CHANGE RESEARCH BEHAVIOR
NOVELTY_REQUIRED -> INVENT / TEST NEW MATHEMATICS
```

None of these states means STOP.

## What an agent receives

A deployment supplies at least:

1. **Root lineage** — the certified path from the immutable root to the assigned obligation.
2. **Exact target type** — a proposition that must not be weakened or renamed.
3. **Allowed imports / writable files.**
4. **Certified sibling assumptions only** — theorem constants, not prose facts.
5. **Operator policy exclusions** — forbidden candidates, declarations, namespaces, routes, or dependencies where configured.
6. **Success conditions** — exact type-link, kernel compilation, axiom policy, seal and dependency-policy checks.
7. **Research history** — the relevant certified frontier plus persistent episode / mechanism / evidence state supplied by the deployment.

## Reward and state movement

CRRG distinguishes three things:

```text
PROJECT REWARD
  the project’s external/canonical terminal gate

CRRG CERTIFIED MOVEMENT
  proof-carrying mutation of the faithful research state

RESEARCH EVIDENCE
  helper theorems, constructions, experiments, counterexamples and failed routes
```

A valid state that did not move is `NO_TRANSITION`. It is not reward and must not be reported as progress.

No aggregate percentage or synthetic global score exists.

## Accepted research-state transitions

Depending on the exact task and downstream adapter, an agent may deliver:

- a proof closing the exact live obligation;
- a certified rootward refinement via an `Edge`;
- an exhaustive certified `Split`;
- an exact quantitative improvement inside one formally monotone family;
- a proof of `¬ P` refuting an exact sealed candidate `P`;
- another transition explicitly admitted by the deployment and checked by its transition verifier.

A failed proof attempt is not a refutation.

## `NO_TRANSITION`

A terminal research attempt may be valid while producing no certified state movement.

In that case the obligation remains open. The research-facing meaning is:

```text
NO_TRANSITION

The exact certified obligation remains OPEN.
No certified blocker has been established.
The absence of a known proof technique is the research problem, not a stopping condition.
Continue mathematical research on an admissible OPEN obligation.

PROVE IT.
```

Downstream tooling distinguishes this mechanically from an admitted transition, rejection, or tooling failure.

## Stall and novelty modes

Repeated terminal no-transitions are orchestration evidence, not mathematical facts.

At the deployment stall threshold, the obligation becomes `STALLED`: the agent must change research behavior rather than repeat the same recorded mechanism indefinitely.

After repeated completed stall cycles without admitted movement, a deployment may enter `NOVELTY_REQUIRED`. This does **not** certify that a theorem is novel. It means the ordinary research policy has repeatedly failed to move the certified state, so the next episode must prioritize inventing and testing a substantively different mathematical mechanism.

In novelty mode, do not merely rephrase the obstruction, formalize another standard consequence, repeat a prior mechanism under a new label, or return ordinary mathematical choices to the operator.

Seek a new invariant, construction, decomposition, estimate, representation, contradiction, or other concrete mechanism aimed at the exact obligation.

## Research-agent decisions versus owner decisions

The research agent owns mathematical choices such as:

- proof technique;
- candidate lemmas and conjectures;
- constants inside a candidate;
- which admissible open obligation to attack;
- which certified ancestor to revisit;
- which mechanism to abandon;
- which strengthening to test;
- which computation decides a mathematical claim;
- which certified refinement to propose.

If a candidate might be false, test or refute it. That is research.

Operator / owner decisions are limited to governance matters such as changing the root policy, trust / axiom policy, operator bans, resource policy, external-import policy, or explicitly stopping the programme.

## What an agent must NOT do

- Weaken or rename the assigned proposition.
- Replace the immutable root with an easier target.
- Add an uncertified premise and report success.
- Propose a split without a compiled coverage theorem.
- Drop a guard-failure or escape branch.
- Rewrite a sealed candidate under the same ID.
- Treat helper-theorem accumulation, theorem count, graph depth, mechanism count, stall count, or novelty metadata as mathematical reward.
- Treat “new mathematics is required” as permission to stop.
- Modify CRRG core semantics while proving a downstream research task.

## Candidate promotion

For a sealed candidate `P`:

- prove `P` exactly -> `CERTIFIED`;
- prove `¬ P` -> `REFUTED`;
- expose missing composition debt -> report the route/candidate as malformed and create a new exact candidate where appropriate;
- produce no accepted witness -> `NO_TRANSITION`, and research continues according to the orchestration state.

A changed proposition always receives a new candidate ID.

## Graph mutations

A leaf refinement must carry a real rootward preservation witness. For example:

- `Frontier.refineLeaf` uses an `Edge`;
- `Frontier.splitLeaf` uses a `Split` with exhaustive coverage;
- `Frontier.retireLeaf` requires an actual proof of the retired obligation.

Accepted frontier mutations induce first-class `Frontier.Transition` witnesses, so transition chains compose in Lean and closing the final frontier entails the unchanged root.

## CRRG as dependency

CRRG is consumed as an exact pinned dependency by downstream projects. Application mathematics, live research state, model adapters, and project reward gates belong downstream. An agent working on a downstream obligation must not modify CRRG source code unless explicitly assigned an infrastructure task by the operator.
