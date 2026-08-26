# CRRG External Review 1

**Reviewer:** ChatGPT (GPT-5.6 Sol)  
**Review scope:** `Barnadrot/CRRG`, pushed `main` state visible through the connected GitHub repository  
**Primary checkpoint:** initial standalone implementation complete; Yukon lower-bound testing reportedly beginning locally  
**Important scope caveat:** this review covers the **pushed GitHub state only**. The implementation agent has reportedly updated `Spec.md` with implementation findings and begun Yukon-stage work locally, but those newer changes were not yet visible on `main` at review time.

---

## Executive verdict

The project has passed the first meaningful architecture checkpoint.

The initial implementation preserves the core CRRG thesis rather than collapsing into project-specific infrastructure:

- CRRG is genuinely standalone.
- The generic Lean core does not import `ProximityPrize`, ArkLib application code, Reed–Solomon machinery, or other downstream mathematics.
- The key semantic directions are correct:
  - child goals discharge parent goals rootward;
  - splits require total coverage;
  - guarded refinements retain both guard branches;
  - escape refinements retain exceptional branches;
  - frontiers close the root only from all current leaves;
  - candidate promotion requires inhabiting the exact typed proposition.

This is enough to justify proceeding to the Yukon integration/backtesting stage.

The main weaknesses are now in the **workflow enforcement and validation layer**, not in the conceptual kernel. In particular, “sealing,” negative tests, provenance/history, downstream-aware promotion tooling, and axiom auditing are currently prototypes rather than full implementations of the spec.

Overall assessment:

| Area | Assessment |
|---|---|
| Standalone architecture | **Green** |
| Generic Lean core semantics | **Green / Yellow** |
| Candidate lifecycle model | **Green / Yellow** |
| Sealing / provenance enforcement | **Yellow** |
| Audit / axiom verification | **Yellow** |
| Synthetic tests | **Yellow** |
| Agent-facing contract | **Green** |
| Yukon integration | **Not yet reviewable from pushed state** |

---

## 1. What is working well

### 1.1 The standalone boundary held

This was the highest-risk architectural failure mode, and the implementation avoided it.

The CRRG repository is a standalone Lean package with no external application mathematics in its Lake configuration. The core library is factored under `CRRG/`, with synthetic tests and scripts kept separately.

This is exactly the correct ownership boundary for a general agent-development tool.

### 1.2 `Edge` direction is correct

The core definition has the intended rootward semantics:

```lean
structure Edge (parent child : Goal) where
  discharge : child.claim → parent.claim
```

This matters because reversing this direction would silently destroy the intended interpretation of research decomposition.

Composition is also defined consistently with that direction.

### 1.3 Frontier semantics are real, not metadata

`Frontier` contains an actual proof-producing `closeRoot`:

```lean
structure Frontier (root : Goal) where
  Task : Type
  leaf : Task → Goal
  closeRoot : (∀ t, (leaf t).claim) → root.claim
```

A frontier is therefore not a state-file description of what should imply the root. It is a Lean object whose complete discharge really yields the root proposition.

### 1.4 Guarded refinement preserves both branches

`GuardedMap` requires both:

```lean
onPass
onFail
```

and converts to an exhaustive `WitnessSplit`.

This preserves the strongest design lesson inherited from ArkLib guarded CWSS:

> a condition used to justify a reduction cannot disappear merely because the next abstraction no longer stores the checked data.

### 1.5 Candidate promotion has the right type-level core

The candidate layer captures the central anti-proxy rule:

```lean
structure SealedCandidate where
  id : String
  targetProp : Prop

structure Promotion (c : SealedCandidate) where
  proof : c.targetProp
```

Promotion requires a proof of the exact proposition.

### 1.6 Agent contract is aligned with the spec

`AGENTS.md` is strong.

It tells agents they receive:

- root lineage;
- exact target type;
- allowed imports/writable files;
- only certified sibling assumptions;
- exact compilation/type-link success conditions.

It explicitly forbids:

- weakening the target;
- replacing it with a proxy;
- adding uncertified assumptions;
- proposing non-certified splits;
- dropping guard/escape branches;
- modifying CRRG core while working on downstream tasks.

---

## 2. Main gaps in the pushed implementation

These are not reasons to redesign the core. They are the areas Yukon should pressure-test next.

### 2.1 “Sealing” is not yet a durable seal

Current `crrg-seal` behavior is approximately:

1. `#check` a declaration;
2. print its type;
3. ask the operator to record it as a `SealedCandidate`.

That validates existence, but it does **not** yet implement the stronger repository-level semantics specified for sealing.

Missing pieces include:

- persistent target hash;
- source commit SHA;
- candidate ID registry;
- immutable seal record;
- creation timestamp;
- history entry;
- automatic detection if the target declaration later changes.

At the Lean value level, `SealedCandidate` is immutable.

At the repository/research-workflow level, however, the current mechanism does not yet prove that an agent cannot edit the declaration later and continue using the same candidate identity.

### 2.2 Candidate metadata is too thin for real multi-edge research

Current `CandidateEdge` carries:

```lean
id
targetProp
status
```

The fuller CRRG design anticipates more graph context:

- source goal IDs;
- destination goal ID;
- expected theorem name;
- seal/source provenance;
- history/status reason;
- possibly theorem SHA after certification.

This is not necessarily a core-library problem. It may be better implemented as downstream/generated registry metadata rather than by expanding the Lean structure itself.

Yukon is the right place to determine which fields are actually necessary.

### 2.3 The negative tests are not yet genuinely adversarial tests

`Test/Synthetic/NegativeTests.lean` demonstrates that valid constructions require all fields and branches.

That is useful, but it is mostly a **positive type-shape test**.

The intended stronger harness should contain examples such as:

```text
Negative/MissingSplitBranch.lean       expected FAIL
Negative/DroppedGuardFail.lean         expected FAIL
Negative/WrongEdgeDirection.lean       expected FAIL
Negative/WeakenedCandidateTarget.lean  expected FAIL
```

with a script that treats successful compilation as test failure.

This matters because CRRG is specifically an anti-reward-hacking system. Its negative tests should be first-class.

### 2.4 Audit semantics are weaker than the documentation currently implies

`CRRG.Audit` currently provides useful type-equality/type-link helpers and a theorem that all closed leaves yield the root.

However, it does not itself perform a transitive axiom audit.

Similarly, `crrg-check` currently:

- builds CRRG;
- builds tests;
- checks that important declarations exist.

The README describes it as including an “axiom audit,” but the pushed script does not yet implement a Proximity-style `collectAxioms` check.

For downstream deployment, certification should eventually mean:

```text
type-correct
+ exact type-link
+ allowed trusted axioms only
```

### 2.5 Promotion tooling is not yet naturally downstream-aware

Current `crrg-promote-check` executes from the CRRG checkout and generates a temporary file that imports only:

```lean
import CRRG
```

It then attempts to resolve a theorem name and a sealed-target declaration name.

That works for declarations available in the CRRG import environment.

It does not naturally work for a theorem and target living in `proximity-research` or a Yukon adapter unless the downstream environment wraps or replaces the command.

A better architecture may be:

```text
CRRG supplies generic Lean helpers
downstream repo supplies CRRG-check wrapper in its own Lake environment
```

rather than having CRRG CLI scripts assume they can import downstream declarations.

### 2.6 Candidate lifecycle state is representable but not yet governed

The Lean types represent:

```text
draft
sealedUnverified
certified
invalid
refuted
malformed
superseded
```

but the pushed repository does not yet appear to implement a persistent state/history mechanism enforcing legal transitions.

This may be acceptable if statuses are treated as descriptive metadata and **only proof terms determine certification**.

But the workflow should make clear which layer is trusted:

- Lean proposition/proof = semantic authority;
- lifecycle status = registry/orchestrator state.

Yukon should help determine whether stronger transition enforcement is worthwhile.

---

## 3. Spec consistency issue

The pushed `Spec.md` visible during this review is still essentially the v0.5 specification text from before implementation findings were incorporated.

It contains several stale editorial artifacts, including:

- inconsistent section numbering;
- old references to earlier spec versions;
- old file-layout text in places;
- no visible implementation-finding amendments yet.

The implementation agent reportedly has already updated the spec locally with findings and failed approaches.

Those newer changes were not visible on pushed `main` at review time.

Therefore this review **does not assess those amendments yet**.

This is the main scope limitation of External Review 1.

---

## 4. Yukon-stage assessment

Proceeding to Yukon is the correct next step.

The generic core is credible enough that further abstract design work would now be lower-value than integration pressure.

Yukon should be expected to break or reshape:

1. sealing/provenance workflow;
2. downstream import-context handling;
3. candidate metadata requirements;
4. lineage rendering;
5. negative-test architecture;
6. promotion ergonomics;
7. possibly frontier-refinement APIs.

That would be healthy.

The key test is not whether Yukon integrates without changes.

The key test is whether the changes remain **generic CRRG improvements** rather than forcing Yukon-specific mathematics into the CRRG core.

### Yukon success criterion

After retrospective reconstruction, CRRG should be able to answer:

> If every current certified leaf is proved, what exact Lean term yields the known Yukon endpoint?

For damaged-proof tests, it should also be able to answer:

> What exact sealed proposition is missing, and what proof would promote it?

### Important measurement

The most informative new metric is **candidate-promotion cost**.

Record:

- iterations per promoted candidate;
- compile/build attempts;
- malformed candidates discovered during promotion;
- target supersessions;
- attempts rejected because the sealed proposition was changed;
- proof lines if useful as an engineering diagnostic.

If known-correct Yukon edges are expensive to promote, that indicates an agent-DX/tooling bottleneck before CRRG is deployed deeply into Soundness.

---

## 5. Recommended next priorities

### Priority 1 — finish Yukon retrospective before adding major new abstractions

Do not over-engineer the generic core before seeing the real proof.

Use the current kernel as the experimental substrate.

### Priority 2 — make failed tests real

Add expected-failure Lean fixtures and a harness that verifies they fail.

### Priority 3 — move promotion checks into downstream build context

Keep generic helpers in CRRG, but let Yukon / `proximity-research` run exact type-link and axiom checks inside their own import environment.

### Priority 4 — implement durable sealing only after Yukon shows required metadata

Do not prematurely build a heavy registry.

But before live Soundness use, a sealed candidate should be anchored to:

- exact target declaration/type;
- candidate ID;
- source commit/hash;
- immutable historical record.

### Priority 5 — add genuine axiom audit before calling a candidate `CERTIFIED`

The eventual certification gate should mean:

```text
exact target inhabited
+ exact type-link
+ allowed axiom closure
```

not just successful elaboration.

### Priority 6 — keep CRRG core free of Yukon/Proximity concepts

If Yukon forces a new abstraction, ask:

> Is this a generic research-graph concept, or merely the shape of this particular proof?

Only the former belongs in `CRRG/`.

---

## 6. Go / no-go conclusion

**GO for Yukon integration and backtesting.**

The initial implementation has not revealed a fundamental design error.

The strongest parts of the original architecture survived implementation:

- exact typed goals;
- rootward certified edges;
- exhaustive splits;
- guard/escape preservation;
- certified frontier closure;
- exact candidate proposition promotion;
- standalone dependency boundary.

The remaining problems are primarily:

```text
enforcement
provenance
audit strength
negative testing
downstream ergonomics
```

These are precisely the classes of issues the Yukon stage was designed to expose.

The project should **not** yet be considered ready for CRRG-directed live Soundness research.

It is ready for the integration experiment that determines whether it can become so.

---

## 7. Review checkpoint for External Review 2

The next external review should occur after the implementation agent pushes the Yukon/spec-findings checkpoint.

External Review 2 should inspect:

1. updated `Spec.md` implementation findings;
2. Yukon retrospective graph;
3. exact sealed candidate examples;
4. failed approaches and why they failed;
5. candidate-promotion cost;
6. downstream import/build strategy;
7. real negative-test harness;
8. axiom-audit changes;
9. whether CRRG core remained application-independent;
10. whether the known Yukon endpoint reconstructs end-to-end through the certified graph.

At that point the review can assess the central research question:

> Is CRRG merely a clean formal audit layer, or is it becoming a practical agent credit-assignment system?
