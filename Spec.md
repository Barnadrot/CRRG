# Certified Research Reduction Graph (CRRG)
## Kernel-checked research reduction and agent credit assignment

**Status:** v0.7.1 — Stage B/C calibrated; Stage D is next.  
**Authority:** this file is the sole normative CRRG design / execution document. `CHANGELOG.md` records history and implementation findings; it does not choose targets or override this spec. Downstream notes are evidence only.  
**Repository architecture:** CRRG is a standalone general-purpose Lean repository consumed as a pinned dependency by research projects.  
**First integration / research test:** `Barnadrot/proximity-research`, using controlled Yukon lower-bound history before any CRRG-directed live Soundness work.  
**Design lineage:** ArkLib `IOR relations → CWSS packages → exact relation seams → guarded CWSS → escape events → sequential composition → CRRG typed edges / splits / guards / escapes / frontiers → sealed candidate promotion`.

---

## 1. Purpose

CRRG exists to solve a credit-assignment problem in autonomous formal mathematics.

The final research reward is exact but sparse. Between prize movements, an agent may prove a major structural theorem, eliminate a route, expose a missing premise, or replace one hard obligation by a certified exhaustive decomposition. CRRG makes that proof graph kernel-visible.

The central rule is:

> **Partial success is not a percentage. Partial success is a theorem that either closes an exact live obligation or replaces it with a kernel-certified sufficient refinement.**

CRRG must never manufacture a synthetic global score such as weighted theorem counts, graph depth, leaf count, or a hand-chosen exchange rate between unrelated local quantities.

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

CRRG core must never import application mathematics such as `ProximityPrize`, ArkLib application modules, Reed–Solomon-specific objects, `Achievable`, `Broken`, `Lambda`, MCA, H2, Yukon, radii, security bits, or any other downstream theorem vocabulary.

If a generic CRRG abstraction appears to require such a concept, the abstraction boundary is wrong. Put the concept in the downstream adapter.

### 2.1 Libraries

```text
CRRG/          generic semantics, Lean-core-only
CRRGTest/      shipped test support such as #expect_failure
Test/          CRRG's own synthetic tests
scripts/       generic audit / seal / promotion tooling
```

Real Yukon or Soundness mathematics never belongs in CRRG’s test tree. Integration fixtures live downstream. CRRG may retain only anonymous synthetic regression patterns extracted from those integrations.

### 2.2 Development checkout versus trusted use

A sibling path checkout is allowed for fast development. It is **not** the trusted deployment mode.

Reproducible downstream use must pin CRRG to an exact Git commit SHA. This also prevents two projects on different Lean versions from sharing one path-dependency build directory.

### 2.3 Seal scope

A downstream gate that uses `crrg-seal` must set `CRRG_SEAL_SCOPE` explicitly to every editable application namespace that may affect the target semantics.

For the Yukon adapter the correct scope discovered during integration is:

```text
ProximityPrize,YukonGraph
```

or the analogous graph namespace for the stage being checked.

Do not rely on an accidentally narrow namespace prefix. A seal that omits a mutable semantic dependency is not a seal.

---

## 3. Branch policy

### 3.1 CRRG repository

```text
main
  = last reviewed / stable CRRG

crrg-hardening
  = sole active implementation and validation branch

claude/crrg-spec-implementation-fr72i8
  = frozen bootstrap history; NO NEW WORK
```

Do **not** merge the old Claude branch back into hardening. Preserve it only as provenance until External Review 2; then archive or delete it at owner discretion.

Do not merge `crrg-hardening` into `main` before External Review 2 passes.

### 3.2 `proximity-research`

```text
yukon-lower-bound
  = historical research record; do not rewrite for CRRG

crrg-stage-b-yukon
  = completed known-proof 6399 reconstruction / calibration

crrg-stage-c-yukon
  = completed damaged-proof / source-visible reconstruction calibration

crrg-stage-d-yukon
  = NEW branch for historical research backtest; MUST start from iter165 commit

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

Direction is rootward: solve the child, obtain the parent. Every certified edge is a Lean theorem. There are no prose edges in CRRG.

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

### 4.5 Frontier

```lean
structure Frontier (root : Goal) where
  Task : Type u
  leaf : Task → Goal
  closeRoot : (∀ t, (leaf t).claim) → root.claim
```

At every trusted state, CRRG must be able to produce a Lean term of the form:

> if every current certified leaf is proved, the unchanged root follows.

Leaf-preserving refinement is normative. `refineLeaf`, `splitLeaf`, and `retireLeaf` preserve siblings and derive the new `closeRoot`. `Frontier.compose` is whole-root rerooting, not leaf refinement.

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

A sealed proposition is a type parameter, not mutable status metadata. A claimed refutation must carry `¬ P`.

### 5.2 No hidden composition debt

If a candidate really needs assumptions `A`, `B`, and `C`, its exact proposition must expose all three. It is forbidden to describe the edge as `A → Parent` while silently relying on `B` or `C`.

### 5.3 Durable seal

The seal hash must cover the target’s semantic body plus every transitive in-scope semantic dependency. Do **not** hash only `#check Target`: a normal candidate has shape `def Target : Prop := ...`, so its type alone is merely `Prop`.

Theorem proof bodies are excluded from semantic sealing; a theorem’s type is its meaning. External dependencies are pinned by manifests rather than recursively sealed.

A broken seal is not repaired by recording a new hash. Create a new candidate ID and preserve the old one.

---

## 6. Verification / anti-cheating gate

The generic CRRG gate must check the checks themselves.

Required validation classes include:

1. fresh-clone executable-bit check from the Git index;
2. core and test builds;
3. cross-toolchain portability with warnings treated as failures;
4. transitive axiom audit;
5. banned-construct scan;
6. seal verification;
7. `crrg-forbid` over theorem proof/type dependencies;
8. self-tests that exercise both acceptance and rejection paths.

A rejection counts only if it happens for the intended reason. Stale oleans, missing imports, or unrelated errors must be reported as **TOOLING FAILURE**, not as a security/research finding.

Outcome vocabulary must remain semantic:

```text
CERTIFIED
REFUTED
MALFORMED
INVALID
SUPERSEDED
UNCHANGED
TOOLING_FAILURE
```

A refutation is never counted or rendered as a promotion.

---

## 7. Agent task contract

An agent receives:

1. exact root lineage;
2. one exact leaf or sealed candidate proposition;
3. allowed imports and writable files;
4. certified sibling assumptions only;
5. explicit forbidden declarations / namespaces where needed;
6. success condition: build + exact type link + axiom audit + seal/forbid checks;
7. failure options: counterexample, impossibility theorem, certified split, or no graph change.

An agent must **not** weaken or rename the target, substitute a different benchmark/radius, introduce an uncertified premise and report success, drop guard/escape branches, edit CRRG core while proving a downstream task, or choose a different root than the one frozen by this spec/task contract.

---

## 8. Implementation status at v0.7.1

### DONE — generic CRRG core / hardening

- [x] Standalone application-agnostic core.
- [x] `Goal`, rootward `Edge`, `Split`.
- [x] `BadNode`, `WitnessMap`, indexed universe-polymorphic `WitnessSplit`.
- [x] `GuardedMap` and `EscapeMap`.
- [x] Leaf-preserving frontier refinement / split / retirement.
- [x] Typed candidate lifecycle and proof-carrying refutation.
- [x] Promotion queue separated from certified frontier.
- [x] Monotone-family local progress; no cross-family exchange rate.
- [x] No aggregate progress percentage.
- [x] Real expected-failure tests, including asynchronous theorem regression coverage.
- [x] Axiom / banned-construct / forbid audits.
- [x] Gate self-tests that verify rejection reasons.
- [x] Cross-toolchain portability gate.
- [x] Fresh-clone executable-bit guard.
- [x] Semantic seal hash + verification / registry.
- [x] Multi-namespace seal scope discovered and implemented during Yukon integration.
- [x] Synthetic replay patterns only; real Yukon fixture downstream.

### DONE — Stage B known-proof calibration

- [x] Downstream Yukon adapter pins exact CRRG SHA `003b7fa7263a88246192532c30f17f859de84991`.
- [x] Root graph itself contains MCA/list/budget decomposition and alignment refinement.
- [x] Downstream promotion wrapper runs in consumer Lake/import context.
- [x] Downstream seal registry is gate-verified.
- [x] Downstream scope uses both application namespaces required by the actual graph.
- [x] Downstream expected-failure tests cover drift / missing branches / wrong constants.
- [x] Existing Yukon gate remains unchanged and passes at `ProtocolClaim 6399 307083 1048576`.

### DONE — Stage C source-visible reconstruction calibration

- [x] Seven sealed candidates, fresh agent context per candidate.
- [x] Six `CERTIFIED`, one genuine `REFUTED` with a Lean proof of `¬ P`.
- [x] Reference declarations mechanically forbidden in proof dependency closure.
- [x] Harness validated on one case it must reject and one it must accept before dispatch.
- [x] Two harness faults were correctly classified as tooling faults before agent measurement.
- [x] C7 outcome leakage was detected and recorded; its cost is excluded from blind evidence.
- [x] C1/C5/C6 difficulty leakage recorded; C2/C3/C4 are the clean mathematics-bearing subset.
- [x] Stage C establishes promotion/tooling usability, **not theorem-discovery cost**.
- [x] Zero MALFORMED outcomes and zero agent weakening attempts are explicitly null results, not evidence of defence quality.

### NEXT — Stage D historical research backtest

- [ ] Create `crrg-stage-d-yukon` from exact commit `f758c1b18a301fe76675cb628027360268bb15cb`.
- [ ] Transplant only neutral CRRG plumbing needed for the historical experiment.
- [ ] Do not expose post-iter165 Yukon mathematics, state prose, theorem names, or later target decisions to research agents.
- [ ] Freeze exact root `ProtocolClaim 7487 349526 1048576`.
- [ ] Use later history only in an evaluator-side checkout after agent output.
- [ ] Mechanically reject any root substitution rather than teaching the agent the known later failure mode.

### FORBIDDEN BEFORE EXTERNAL REVIEW 2

- [ ] No CRRG-directed live Soundness scheduling.
- [ ] No target selection by the implementation agent.
- [ ] No ArkLib upstreaming.

---

## 9. Yukon validation programme

### 9.1 Stage B — known-proof calibration at 6399 — COMPLETE

Purpose: prove CRRG can faithfully reconstruct an already-completed real proof.

Frozen endpoint:

```lean
ProtocolClaim 6399 307083 1048576
```

This is calibration only. It is not the Yukon research objective.

The certified root lineage now contains:

```text
ProtocolClaim 6399
  ├─ admissible
  ├─ score
  └─ reduction
       ↓
     analytic conclusion
       ├─ MCA term
       │    └─ alignment premise
       ├─ Johnson/list term
       └─ field-capacity budget
```

### 9.2 Stage C — damaged-proof calibration — COMPLETE WITH LIMITATIONS

Purpose: measure promotion enforcement and engineering overhead on statements with known ground truth.

Observed result:

```text
CERTIFIED  6
REFUTED    1
```

The experiment is **source-visible reconstruction**, not genuine theorem discovery. `crrg-forbid` prevented agents from *using* reference declarations in submitted proof closures, but agents could read the completed source tree and all independently re-derived the proofs from what they read.

Therefore Stage C supports only these conclusions:

- promotion tooling is not an obvious bottleneck at this scale;
- exact type-link, seal, forbid, and axiom checks compose successfully downstream;
- proof-carrying refutation works;
- harness failures can be separated from agent failures.

It does **not** measure theorem-discovery cost, target-drift resistance under uncertainty, MALFORMED detection in live research, or adversarial weakening behavior.

### 9.3 Stage D — primary historical Yukon research backtest

**Purpose:** test the actual CRRG research thesis under genuine mathematical uncertainty.

#### 9.3.1 Historical isolation is mandatory

The Stage D research working tree itself must be based on:

```text
repository: Barnadrot/proximity-research
cutoff:     iteration 165
commit:     f758c1b18a301fe76675cb628027360268bb15cb
```

Do **not** create Stage D on top of `crrg-stage-c-yukon` or the modern `yukon-lower-bound` head. `crrg-forbid` prevents proof-term dependency on a declaration; it does not prevent an agent from reading later source and copying the mathematical idea. Stage C demonstrated that agents do exactly this.

Stage D therefore uses two logically separate environments:

```text
RESEARCH CHECKOUT
  repo at f758c1b...
  + pinned CRRG
  + neutral Stage D graph/harness
  + only information available through iter165

EVALUATOR CHECKOUT
  full later Yukon history
  + post-165 findings
  + known later target regression
  used only after research-agent output
```

No post-iter165 theorem, state memo, commit message, target rationale, or candidate rationale may be made available to the research agent through the Stage D working tree or task contract.

#### 9.3.2 Primary root

Freeze exactly:

```lean
ProtocolClaim 7487 349526 1048576
```

At iteration 165 the collapse cap `532676608 = (p-1)/4` had been diagnosed as forced but not the binding obstruction; the radius / beyond-Johnson mathematics remained the research problem. The primary CRRG job is to encode the exact certified 7487 root seam available at the cutoff and expose the honest remaining obligations without importing later answers.

#### 9.3.3 Target substitution control

The research agent is told only that the root is immutable. It is **not** told that a later executor regressed to a specific 6400 mini-target.

If the agent independently proposes any different root/radius/score, the gate must reject it mechanically because it is not the frozen root and has no certified refinement edge into it.

The known later 6400 pivot is evaluator-side ground truth and may be used after the experiment as a concrete negative-control comparison. Do not leak it into the research prompt.

#### 9.3.4 Stage D outcome reporting

Unlike Stage C, Stage D cannot read an `expectedOutcome` column to decide what success means. The evaluator/gate must preserve distinct observed states:

```text
CERTIFIED
REFUTED
MALFORMED
INVALID
SUPERSEDED
UNCHANGED
TOOLING_FAILURE
```

A refutation is not a promotion. A failed proof is not a refutation. A tooling error is not a research/security finding.

#### 9.3.5 What Stage D measures

Record:

- target substitutions proposed / rejected;
- invalid or non-exhaustive refinements;
- certified reductions discovered;
- candidate promotions;
- route refutations / retirements;
- MALFORMED candidates exposing missing composition debt;
- repeated rediscovery of already-known pre-cutoff context;
- lemmas with no certified consumer;
- safe returns to an ancestor when a child route stalls;
- safe further refinement of an immutable parent;
- benchmark movement, if any.

The central Stage D question is:

> Does CRRG keep an autonomous researcher attached to the correct frozen theorem while still allowing safe decomposition, backtracking, route retirement, and genuinely novel mathematics?

---

## 10. Reduction depth and backtracking

A certified reduction can be logically correct and strategically bad. CRRG guarantees sufficiency; it does not prove that a child theorem is easier than its parent.

Therefore certified ancestors remain historical graph nodes, a stalled child may be removed from the active research frontier without deleting its valid edge, the scheduler may return to an ancestor, and a current hard target may be refined further only by supplying a certified edge/split back into that unchanged target.

A reduction-depth audit should classify the active state as:

```text
OVERREDUCED   — step upward; identify concrete information lost by the child
RIGHT-DEPTH   — keep current parent; recent failures are mechanism failures
UNDERREDUCED  — give an explicit certified candidate refinement below it
```

An operation wish-list is not a reduction until an exact candidate proposition and a real first arrow exist.

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

A tooling defect is “fixed” only when a regression/self-test demonstrates the bad behavior and the corrected behavior, or an equivalent positive/negative test pins the property.

`CHANGELOG.md` may continue recording detailed implementation discoveries. It must not become a second planning document.

---

## 12. External Review 2 gate

External Review 2 occurs after:

```text
A. generic core / hardening                         DONE
B. faithful 6399 reconstruction                    DONE
C. source-visible damaged-proof calibration        DONE
D. frozen iter165 / 7487 historical backtest       complete enough to evaluate behavior
pinned-SHA downstream dependency                    verified
seal / forbid / axiom / negative-test gates         verified downstream
Spec.md                                               current
```

External Review 2 must inspect the exact CRRG/downstream SHAs, final Stage B graph, Stage C limitations/results, Stage D isolation and 7487 root, any attempted target substitutions, seal scope and registry behavior, downstream promotion tooling, negative tests/axiom closure, generic-core boundary, and agent DX.

**Do not start CRRG-directed live Soundness research before this review.**

---

## 13. Soundness deployment after review

After External Review 2, CRRG may enter Soundness first in shadow mode.

The initial certified Soundness seam remains:

```text
Achievable (971426 / 2097152)
        ↑
MomentRecovery.achievable_971426_of_fpMomentBudget_genericTail
       / \
      /   \
FpMomentBudgetAt momentKappa 971426
GenericTailThresholdAt momentKappa 971426
```

Deeper prose research structure does not become trusted graph structure until exact Lean edges connect it to those leaves. Shadow mode observes the existing executor; it does not schedule it.

---

## 14. Acceptance criteria for v0.7.1

- [x] `crrg-hardening` is the only active CRRG staging line.
- [x] CRRG builds independently and remains application-agnostic.
- [x] Supported downstream Lean toolchains build CRRG cleanly with warnings treated as failure.
- [x] Axiom, banned-construct, forbid, seal, and self-test gates have positive and negative controls.
- [x] Downstream Yukon consumes an exact pinned CRRG SHA.
- [x] Downstream seal registry uses the actual required application/graph namespaces and is gate-verified.
- [x] Stage B certified root graph contains MCA/list/budget decomposition and alignment refinement.
- [x] Stage C has separate raw results and documented blindness limitations.
- [x] Candidate-promotion engineering cost is recorded without pretending it is mathematical progress.
- [ ] Stage D branch is created from exact iter165 commit `f758c1b18a301fe76675cb628027360268bb15cb`.
- [ ] Stage D research checkout contains no post-iter165 mathematical answers.
- [ ] Stage D primary target is exactly `ProtocolClaim 7487 349526 1048576`.
- [ ] Any substituted root is mechanically rejected without leaking the known later 6400 regression into the task prompt.
- [ ] Stage D reporting distinguishes `CERTIFIED`, `REFUTED`, `MALFORMED`, `UNCHANGED`, and `TOOLING_FAILURE` rather than collapsing them into promotion.
- [x] No CRRG-directed live Soundness scheduling has begun.

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

The intended loop is:

```text
read frozen root + certified frontier + promotion queue
choose an exact permitted task
research

proof                → close / certify
certified reduction  → refine
counterexample        → refute / retire route
stalled child         → step back to certified ancestor
nothing               → graph unchanged

recompute active frontier
```

> **Research freedom lives below an immutable theorem target. The graph may grow, compress, backtrack, and retire routes; the target does not drift.**
