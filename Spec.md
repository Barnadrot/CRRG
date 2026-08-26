# Certified Research Reduction Graph (CRRG)
## Kernel-checked research reduction and agent credit assignment

**Status:** v0.7 — implementation-constrained execution spec.  
**Authority:** this file is the sole normative CRRG design / execution document. `CHANGELOG.md` records history and implementation findings; it does not choose targets or override this spec. Downstream notes such as `STAGE_B.md` are evidence only.  
**Repository architecture:** CRRG is a standalone general-purpose Lean repository consumed as a pinned dependency by research projects.  
**First integration / research test:** `Barnadrot/proximity-research`, using controlled Yukon lower-bound history before any CRRG-directed live Soundness work.  
**Design lineage:** ArkLib `IOR relations → CWSS packages → exact relation seams → guarded CWSS → escape events → sequential composition → CRRG typed edges / splits / guards / escapes / frontiers → sealed candidate promotion`.  

---

## 1. Purpose

CRRG exists to solve a credit-assignment problem in autonomous formal mathematics.

The final research reward is exact but sparse. Between prize movements, an agent may prove a major structural theorem, eliminate a route, expose a missing premise, or replace one hard obligation by a certified exhaustive decomposition. Humans can recognize that as progress because they retain a proof graph in context. CRRG makes that graph kernel-visible.

The central rule is:

> **Partial success is not a percentage. Partial success is a theorem that either closes an exact live obligation or replaces it with a kernel-certified sufficient refinement.**

CRRG must never manufacture a synthetic global score such as “63% solved”, weighted theorem counts, graph depth, leaf count, or a hand-chosen exchange rate between unrelated local quantities.

Trusted progress channels are only:

1. actual project reward movement, produced by the project’s existing gate;
2. exact `OPEN → CLOSED` transition of an assigned leaf;
3. a certified refinement / split that preserves root closure;
4. an exact quantitative improvement inside one formally monotone family;
5. a sealed candidate becoming certified, which is formalization progress but **not** prize progress.

---

## 2. Standalone repository and trust boundary

CRRG is a standalone Lean library. The dependency direction is one-way:

```text
CRRG
  ▲
  │ pinned dependency
  │
downstream research project
```

CRRG core must never import application mathematics such as:

- `ProximityPrize`;
- ArkLib application modules;
- Reed–Solomon-specific objects;
- `Achievable`, `Broken`, `Lambda`, MCA, H2, Yukon, radii, security bits;
- any other downstream theorem vocabulary.

If a generic CRRG abstraction appears to require such a concept, the abstraction boundary is wrong. Put the concept in the downstream adapter.

### 2.1 Libraries

The intended split is:

```text
CRRG/          generic semantics, Lean-core-only
CRRGTest/      shipped test support such as #expect_failure
Test/          CRRG's own synthetic tests; may use extra test-only dependencies
scripts/       generic audit / seal / promotion tooling
```

Real Yukon or Soundness mathematics never belongs in CRRG’s test tree. Integration fixtures live downstream. CRRG may retain only anonymous synthetic regression patterns extracted from those integrations.

### 2.2 Development checkout versus trusted use

A sibling path checkout is allowed for fast development. It is **not** the trusted deployment mode.

Reproducible downstream use must pin CRRG to an exact Git commit SHA. This also prevents two projects on different Lean versions from sharing and corrupting one path dependency build directory.

### 2.3 Seal scope

A downstream gate that uses `crrg-seal` **must set `CRRG_SEAL_SCOPE` explicitly to the editable application root namespace** (for `proximity-research`, use `ProximityPrize`) unless the default target namespace is proven to contain every mutable application definition on which the target depends.

Do not rely on an accidentally narrow namespace prefix. A seal that omits a mutable semantic dependency is not a seal.

---

## 3. Branch policy

### 3.1 CRRG repository

The active branch policy is:

```text
main
  = last reviewed / stable CRRG

crrg-hardening
  = sole active implementation and validation branch

claude/crrg-spec-implementation-fr72i8
  = frozen bootstrap history; NO NEW WORK
```

`crrg-hardening` supersedes the old Claude implementation branch. Do **not** merge the old branch back into hardening: it contains the pre-hardening API and tooling. Preserve it only as provenance until External Review 2; then archive or delete it at owner discretion.

Do not merge `crrg-hardening` into `main` before External Review 2 passes. After review, merge/fast-forward the reviewed hardening state, repin downstream adapters to the resulting exact SHA, and rerun all gates.

### 3.2 `proximity-research`

For CRRG Yukon validation:

```text
yukon-lower-bound
  = historical research record; do not rewrite for CRRG

crrg-stage-b-yukon
  = known-proof 6399 reconstruction / calibration

crrg-stage-c-yukon
  = blind damaged-proof tests + frozen historical research backtest

soundness
  = live research lane; untouched by CRRG-directed scheduling before review
```

Do not merge CRRG experiment branches into `yukon-lower-bound`. They are experiments *against* the historical record.

---

## 4. Core semantics

### 4.1 Goals and edges

```lean
structure Goal where
  claim : Prop

abbrev Goal.Proved (G : Goal) : Prop := G.claim

structure Edge (parent child : Goal) : Prop where
  discharge : child.claim → parent.claim
```

Direction is rootward: solve the child, obtain the parent.

Every certified edge is a Lean theorem. There are no prose edges in CRRG.

### 4.2 Exact splits

```lean
structure Split (parent : Goal) where
  Branch : Type u
  child : Branch → Goal
  discharge : (∀ i, (child i).claim) → parent.claim
```

A split is not a task list. It is a proof that all children suffice for the parent.

### 4.3 Counterexample nodes

```lean
structure BadNode where
  Witness : Type u

abbrev BadNode.Closed (N : BadNode) : Prop := N.Witness → False

structure WitnessMap (parent : BadNode.{u}) (child : BadNode.{v}) where
  map : parent.Witness → child.Witness

structure WitnessSplit
    (parent : BadNode.{u})
    {Branch : Type v}
    (child : Branch → BadNode.{w}) where
  classify : parent.Witness → (i : Branch) × (child i).Witness
```

`WitnessSplit` is indexed by the branch family and children. This shape is normative: it preserves independent universes, avoids the `checkUnivs` failure of the earlier field-based shape, and puts the exact child family in the split’s type.

### 4.4 Guards and escapes

A guarded transform must represent both truth values. An escape transform must represent both normal and exceptional outcomes. A branch may never disappear because downstream data stopped carrying the checked condition.

These are the static analogue of ArkLib guarded / escape CWSS composition.

### 4.5 Frontier

```lean
structure Frontier (root : Goal) where
  Task : Type u
  leaf : Task → Goal
  closeRoot : (∀ t, (leaf t).claim) → root.claim
```

At every trusted state, CRRG must be able to produce a Lean term of the form:

> if every current certified leaf is proved, the unchanged root follows.

Leaf-preserving refinement is normative:

- `refineLeaf` replaces one leaf by one sufficient child;
- `splitLeaf` replaces one leaf by an exhaustive split;
- `retireLeaf` removes a leaf only after that leaf is actually proved;
- all sibling leaves survive.

`Frontier.compose` is whole-root rerooting, not leaf refinement, and must not be used when sibling preservation is intended.

---

## 5. Candidate graph and sealing

CRRG has two distinct layers:

```text
CERTIFIED GRAPH
  exact Lean implications that already exist

TYPED PROMOTION QUEUE
  exact Lean propositions whose proofs are absent
```

Only the certified graph can close the root.

### 5.1 Candidate lifecycle

```text
DRAFT
  ↓ seal exact proposition
SEALED_UNVERIFIED
  ├─ proof of exact proposition → CERTIFIED
  ├─ proof of negation           → REFUTED
  ├─ intended route wrong        → INVALID
  ├─ proposition missing debt    → MALFORMED
  └─ replaced exact target       → SUPERSEDED
```

A sealed proposition is a type parameter, not mutable status metadata. A resolved candidate cannot be promoted again.

A claimed refutation must carry `¬ P`. Mere suspicion or a failed proof attempt is not a refutation.

### 5.2 No hidden composition debt

If a candidate really needs assumptions `A`, `B`, and `C`, its exact proposition must expose all three. It is forbidden to describe the edge as `A → Parent` while silently relying on `B` or `C`.

### 5.3 Durable seal

The seal hash must cover:

- target declaration type;
- target definition body when the body carries meaning;
- the type and meaningful body of every transitive in-scope semantic dependency.

Do **not** hash only `#check Target`: a normal candidate has shape `def Target : Prop := ...`, so its type alone is just `Prop` and does not identify the proposition.

Theorem proof bodies are excluded from semantic sealing; a theorem’s type is its meaning. External dependencies such as Lean / Mathlib are pinned by the manifest rather than recursively sealed.

`crrg-seal --verify` and `--verify-registry` must detect retargeting under an unchanged declaration name. A broken seal is not repaired by recording a new hash. Create a new candidate ID and preserve the old one.

---

## 6. Verification / anti-cheating gate

The generic CRRG gate must check the checks themselves.

Current required classes of validation are:

1. script executable bits as recorded in the Git index, so a fresh clone works;
2. build CRRG core;
3. build test libraries;
4. cross-toolchain portability for every supported downstream Lean version, with warnings treated as failures;
5. declaration/type presence;
6. transitive axiom audit;
7. self-tests that exercise each audit on inputs it must accept **and** inputs it must reject;
8. banned-construct scan.

A rejection test counts only if it rejects for the intended reason. “Command exited nonzero” is insufficient: stale oleans, missing files, or unrelated parser errors must not masquerade as successful security tests.

`crrg-forbid` is the required tool for blind/damaged-proof experiments. It must traverse theorem proof bodies, including opaque theorem values, and must reject a submitted theorem if a forbidden declaration or namespace occurs anywhere in its transitive type/proof dependency closure.

---

## 7. Agent task contract

An agent receives:

1. exact root lineage;
2. one exact leaf or sealed candidate proposition;
3. allowed imports and writable files;
4. certified sibling assumptions only;
5. explicitly forbidden declarations / namespaces where needed;
6. success condition: build + exact type link + axiom audit + seal/forbid checks;
7. failure options: counterexample, impossibility theorem, certified split, or no graph change.

An agent must **not**:

- weaken or rename the target into an easier theorem;
- substitute a different benchmark/radius because it is easier;
- introduce a new open premise and report success;
- drop guard / escape branches;
- edit CRRG core while working on a downstream research task;
- choose a different research target than the one frozen by this spec / task contract.

---

## 8. Implementation status at v0.7

The status below is normative for the current hardening checkpoint. Historical detail belongs in `CHANGELOG.md`.

### DONE — generic CRRG core / hardening

- [x] Standalone repository boundary; no application mathematics in core.
- [x] `Goal`, rootward `Edge`, `Split`.
- [x] `BadNode`, `WitnessMap`, indexed universe-polymorphic `WitnessSplit`.
- [x] `GuardedMap` and `EscapeMap` with explicit sibling branches.
- [x] Leaf-preserving frontier refinement / split / retirement.
- [x] Typed candidate lifecycle with sealed proposition as type parameter.
- [x] Refutation requires an actual disproof.
- [x] Promotion queue separated from certified frontier.
- [x] Monotone-family local progress with no cross-family exchange rate.
- [x] One-line-per-task reporting with no aggregate percentage.
- [x] Real expected-failure Lean tests, including async-theorem regression coverage.
- [x] Transitive axiom audit.
- [x] Source-level banned-construct audit.
- [x] `crrg-forbid` transitive dependency audit over theorem proofs.
- [x] Gate self-tests that verify the expected rejection reason.
- [x] Cross-toolchain portability gate.
- [x] Fresh-clone executable-bit guard.
- [x] Seal hash over semantic body + in-scope dependency closure.
- [x] Seal verification / registry checks.
- [x] Synthetic replay patterns live in CRRG; real Yukon fixtures remain downstream.

### IN PROGRESS — downstream calibration

- [ ] Publish / use an exact pinned CRRG staging SHA in the downstream Yukon adapter instead of the sibling path.
- [ ] Keep `crrg-hardening` as the only active CRRG staging branch.
- [ ] Complete the downstream promotion wrapper in the consumer’s Lake/import context.
- [ ] Set downstream `CRRG_SEAL_SCOPE=ProximityPrize` explicitly.
- [ ] Add downstream seal registry and verify it in the downstream gate.
- [ ] Add downstream expected-failure tests for graph drift / weakened targets.
- [ ] Finish Stage B root reconstruction so the **actual certified root frontier**, not merely a side agreement theorem, contains the MCA/list/budget decomposition and the deeper alignment refinement.

### NOT STARTED / FORBIDDEN BEFORE REVIEW

- [ ] No CRRG-directed live Soundness scheduling.
- [ ] No target selection by the implementation agent.
- [ ] No ArkLib upstreaming.

---

## 9. Yukon validation programme

There are three different experiments. They must not be conflated.

### Stage B — known-proof calibration at 6399

**Purpose:** test whether CRRG can faithfully reconstruct an already-completed real proof.

Frozen endpoint:

```lean
ProtocolClaim 6399 307083 1048576
```

This stage is **calibration only**. `6399` is not the Yukon research objective.

The intended certified graph contains, in the actual root lineage:

```text
ProtocolClaim 6399
  ├─ admissible
  ├─ score
  └─ reduction
       ├─ MCA term
       │    └─ alignment premise
       ├─ Johnson/list term
       └─ field-capacity budget
```

Acceptance requires the existing Yukon gate to pass unchanged and the reconstructed graph to preserve the exact endpoint, exact radii/constants, exact theorem directions, exact side conditions, and allowed axiom closure.

**Stage B is not complete merely because a side module proves that MCA/list/budget compose. The live certified root graph itself must contain that decomposition.**

### Stage C — blind damaged-proof calibration

**Purpose:** measure enforcement and agent DX on statements known to be provable.

For each selected candidate:

```text
one sealed exact target
one fresh agent context
reference proof mechanically forbidden
exact allowed imports/files
attempt log preserved
```

The orchestrating implementation agent may know the reference proof. The promotion agent may not.

Measure raw per-candidate results and aggregate only experimental engineering statistics, never mathematical progress percentages:

- iterations from `SEALED_UNVERIFIED` to `CERTIFIED`;
- build attempts;
- malformed candidate discoveries;
- superseded exact target types;
- seal violations / target weakening attempts rejected;
- tooling failures separately from theorem-search iterations.

### Stage D — primary historical Yukon research backtest

**Purpose:** test the actual CRRG research thesis under genuine mathematical uncertainty.

This experiment is frozen at the historical research state **before the later target regression**.

#### 9.3.1 Frozen authority

```text
repository: Barnadrot/proximity-research
branch:     yukon-lower-bound
cutoff:     iteration 165
commit:     f758c1b18a301fe76675cb628027360268bb15cb
```

Later Yukon commits, later `FRONTIER.md` heads, later 6400 analysis, and later discovered theorems are **evaluation / ground-truth data only**. They may not alter the experiment’s root or task selection.

#### 9.3.2 Primary research root

The primary backtest target is:

```lean
ProtocolClaim 7487 349526 1048576
```

The downstream tree already contains an exact conditional route of the form:

```text
T1 base list bound at radius 7487
+
T2 / MCA-side extension-list or equivalent count obligation
+
closed numeric budget / positivity side conditions
        ↓
ProtocolClaim 7487 349526 1048576
```

At iteration 165 the collapse cap `532676608 = (p-1)/4` had been diagnosed as forced but **not the binding obstruction**; the radius / beyond-Johnson mathematics remained the research problem. The 7487 rung is therefore the correct primary research backtest.

The first CRRG job is to encode the exact certified 7487 root seam and expose the remaining honest T1/T2 obligations without importing later answers.

#### 9.3.3 Optional second diligence target

After the primary 7487 backtest is running correctly, a second frozen historical rung such as 9433 may be added to test how CRRG handles a harder member of the same parameterized family. This is optional and must not delay the primary 7487 experiment.

#### 9.3.4 6400 is a negative control, not a research objective

For the iteration-165 / 7487 experiment, switching to a later 6400 mini-target is **FORBIDDEN TARGET SUBSTITUTION**.

An agent assigned to 7487 may not decide that 6400 is easier and replace the root with it. If it proposes such a move, the correct CRRG outcome is:

```text
TARGET SUBSTITUTION REJECTED
no certified edge from the proposed 6400 target to the frozen 7487 root
GRAPH UNCHANGED
```

A separate 6400 reconstruction may be retained only as a **negative/control fixture** demonstrating that CRRG refuses an attractive easier target substitution. It is not evidence of progress on the frozen 7487 experiment.

This control is important because later Yukon work explicitly pivoted toward 6400 despite the earlier rung programme; CRRG is intended to prevent exactly this class of target drift.

#### 9.3.5 What Stage D measures

Do not evaluate only final score movement. Record:

- target substitutions proposed / rejected;
- invalid or non-exhaustive refinements;
- certified reductions discovered;
- candidate promotions;
- route refutations / retirements;
- repeated rediscovery of already-known context;
- lemmas with no certified consumer;
- times the scheduler safely stepped back to an ancestor because a child route stalled;
- times a sealed parent was safely refined further rather than mutated;
- benchmark movement if it occurs.

The central Stage D question is:

> Does CRRG keep an autonomous researcher attached to the correct frozen theorem while still allowing safe decomposition, backtracking, route retirement, and genuinely novel mathematics?

---

## 10. Reduction depth and backtracking

A certified reduction can be logically correct and strategically bad. CRRG guarantees sufficiency; it does not prove that a child theorem is easier than its parent.

Therefore:

- certified ancestors remain historical graph nodes;
- a stalled child may be removed from the active research frontier without deleting its valid edge;
- the scheduler may return to an ancestor or choose a different certified descendant;
- a current hard target may be refined further only by supplying a certified edge/split back into that unchanged target.

A reduction-depth audit should classify the active state as:

```text
OVERREDUCED   — step upward; identify concrete information lost by the child
RIGHT-DEPTH   — keep current parent; recent failures are mechanism failures
UNDERREDUCED  — give an explicit certified candidate refinement below it
```

An operation wish-list (“there should exist a map with properties ...”) is not a reduction until an exact candidate proposition and a real first arrow exist.

---

## 11. Implementation-agent reporting contract

Implementation agents are **builders, not research-target selectors**.

At each checkpoint report only:

```text
1. commits landed
2. files changed
3. exact commands run + exit status
4. stage checklist entries changed
5. defects found, each with reproducer / regression test
6. remaining blockers
7. questions requiring owner decision
```

Do not rewrite downstream research history into a new objective. Do not choose a different radius because it is easier. Do not promote later historical prose over a target frozen by this spec.

A tooling defect is “fixed” only when a regression/self-test demonstrates the bad behavior before/without the fix and the correct behavior with the fix, or an equivalent positive/negative test pins the property.

`CHANGELOG.md` may continue recording detailed implementation discoveries. It must not become a second planning document.

---

## 12. External Review 2 gate

External Review 2 occurs **after** the following are complete:

```text
A. generic core / hardening                         DONE
B. faithful 6399 reconstruction                    complete
C. blind damaged-proof calibration                 complete
D. frozen iter165 / 7487 historical backtest       complete enough to evaluate behavior
pinned-SHA downstream dependency                    verified
seal / forbid / axiom / negative-test gates         verified downstream
Spec.md updated with implementation findings         current
```

External Review 2 must inspect:

1. exact CRRG SHA and downstream SHA;
2. the final Stage B certified graph, including MCA/list/budget in root lineage;
3. blind Stage C candidate results and promotion cost;
4. frozen Stage D 7487 root and cutoff enforcement;
5. any attempted 6400 target substitution and CRRG’s handling of it;
6. seal scope and registry behavior;
7. downstream promotion wrapper;
8. negative tests and axiom closure;
9. whether application mathematics stayed out of CRRG core;
10. whether the tooling remained usable enough for research agents.

**Do not start CRRG-directed live Soundness research before this review.**

---

## 13. Soundness deployment after review

After External Review 2, CRRG may enter Soundness first in **shadow mode**.

The initial certified Soundness seam remains the already-landed exact theorem:

```text
Achievable (971426 / 2097152)
        ↑
MomentRecovery.achievable_971426_of_fpMomentBudget_genericTail
       / \
      /   \
FpMomentBudgetAt momentKappa 971426
GenericTailThresholdAt momentKappa 971426
```

Deeper prose research structure does not become trusted graph structure until exact Lean edges connect it to those leaves.

Shadow mode observes the existing executor. It does not schedule it. Only after shadow-mode review may CRRG become the scheduler.

The existing project prize gates, frozen invariants, bridges, and Disprove side remain unchanged.

---

## 14. Acceptance criteria for v0.7

CRRG v0.7 is ready for External Review 2 when all of the following hold:

- [ ] `crrg-hardening` is the only active CRRG staging line.
- [ ] CRRG builds independently and remains application-agnostic.
- [ ] Every supported downstream Lean toolchain builds CRRG cleanly with warnings treated as failure.
- [ ] Axiom, banned-construct, forbid, seal, and self-test gates all have positive and negative controls.
- [ ] Downstream Yukon consumes an exact pinned CRRG SHA.
- [ ] Downstream seal scope is explicitly `ProximityPrize` and registry verification is part of the gate.
- [ ] Stage B’s actual certified root graph contains the MCA/list/budget decomposition and alignment refinement; no side-only reconstruction is called “full”.
- [ ] Stage C uses fresh blind agents with reference proofs mechanically forbidden.
- [ ] Candidate-promotion cost is recorded without pretending it is mathematical progress.
- [ ] Stage D is frozen to Yukon iteration 165 / commit `f758c1b18a301fe76675cb628027360268bb15cb`.
- [ ] Stage D primary target is exactly `ProtocolClaim 7487 349526 1048576`.
- [ ] Later 6400 work cannot replace that root; 6400 is only a target-substitution negative control.
- [ ] Historical later Yukon material is excluded from Stage D agent context and used only for evaluation.
- [ ] No CRRG-directed live Soundness scheduling has begun.

---

## 15. Design summary

CRRG separates three things that ordinary research logs often blur:

```text
MATHEMATICAL TRUTH
  certified proof DAG

FORMALIZATION DEBT
  exact sealed candidate propositions

RESEARCH POLICY
  which certified leaf / candidate / ancestor to work on next
```

The kernel controls the first two. The scheduler may change the third, but it may not mutate the mathematical target to manufacture progress.

The intended agent loop is:

```text
read frozen root + certified frontier + promotion queue
choose an exact permitted task
research

proof                → close / promote
certified reduction  → refine
counterexample        → refute / retire route
stalled child         → step back to certified ancestor
nothing               → graph unchanged

recompute active frontier
```

The invariant is simple:

> **Research freedom lives below an immutable theorem target. The graph may grow, compress, backtrack, and retire routes; the target does not drift.**
