# Certified Research Reduction Graph (CRRG)
## Kernel-checked research reduction and agent credit assignment

**Status:** v0.10.0-draft — the persistence layer is specified (§28–§36), implementation pending; v0.9.0 is live on the Yukon lane (`crrg-yukon` @ `8fc55432`); External Review 2 complete.  
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

Certified research-state channels are only:

1. actual project reward movement, produced by the project’s existing gate;
2. exact `OPEN → CLOSED` transition of an assigned leaf;
3. a certified refinement / split that preserves root closure;
4. an exact quantitative improvement inside one formally monotone family;
5. a sealed candidate becoming certified, which is formalization progress but **not** prize progress.

Channel 1 is project reward (the terminal objective); channels 2–5 are CRRG certified state movement. Research evidence is not a channel and never becomes one by accumulation — the explicit three-way distinction is §19.3's.

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

or the analogous graph namespace for the stage being checked — `ProximityPrize,CrrgLive` for the live deployment.

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
  = completed historical research backtest; started from the iter165 commit

crrg-yukon
  = THE LIVE DEPLOYMENT (§16). Descends from the current yukon-lower-bound
    head. The research agent runs here and nowhere else.

crrg-shadow-soundness
  = incomplete Stage E shadow work; see §13

soundness
  = live research lane; untouched by CRRG-directed scheduling
```

Do not merge CRRG experiment branches into `yukon-lower-bound`. They are experiments *against* the historical record.

`crrg-yukon` is not an experiment branch — it is a live lane — but it is still not merged into `yukon-lower-bound` by the research agent. Promoting live CRRG results back into the canonical record is an owner decision, and the canonical lane is protected from direct research-agent writes (§16.1).

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

#### What is immutable, and what is not

This distinction is normative, and getting it wrong disables a live deployment:

```text
a seal                    immutable, per candidate ID
the registry of seals     NOT required to be immutable
```

A live deployment **must permit creation of fresh seal records for new exact candidate propositions**, because that is what a certified refinement produces: a child proposition that did not exist when the deployment was built. An existing candidate ID and its row may never be rewritten to mean a different proposition — a changed proposition gets a **new ID**, and the old row stays forever.

A deployment that hashes its whole seal registry as a frozen governance file has made its own sanctioned next step indistinguishable from tampering. The researcher then holds a certified `REFINED` it is not permitted to act on, and the only ways forward are to violate governance or to discard a real result. Both are worse than the problem. Append is live state; rewrite is not; enforce the difference in the registration tool and in the audit trail, not by freezing the file.

`scripts/crrg-register-candidate` is the generic implementation: fresh ID required, the declaration must elaborate, the hash comes from `crrg-seal` rather than a second implementation, the append is atomic, the resulting registry is re-verified before it is installed, and every rejection leaves the registry byte-identical.

#### The live refinement lifecycle

```text
DRAFT exact child
        ↓
certified Edge / Split
        ↓
fresh durable seal registration for every new child
        ↓
SEALED_UNVERIFIED child
        ↓
activate certified refinement on the Frontier
        ↓
child is an OPEN live task
```

A candidate **may** be sealed before its `Edge` or `Split` is discovered — predeclaring a target is legitimate and often better. It **must** be sealed before it becomes a live frontier leaf. Every branch of a `Split` is a separate child and needs its own seal; activating a split with one branch sealed and one not is rejected.

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
REFINED
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
5. explicit operator policy exclusions, including forbidden candidate IDs, declarations and namespaces;
6. success condition: build + exact type link + axiom audit + seal/forbid checks;
7. failure options: counterexample, impossibility theorem, certified split, or no graph change.

Operator exclusions are research-policy constraints, not mathematical facts.

A deployment may ban a candidate/result/declaration/namespace from future research selection or proof dependency in order to prevent repeated grinding on a settled route.

A ban:

- never changes the root;
- never deletes certified graph history;
- never certifies or refutes a proposition;
- only restricts what future research may select or use.

Where mechanically enforceable, the gate **must** enforce the exclusions using the proof/type dependency closure (`crrg-forbid`), not only prompt prose.

An agent must **not** weaken or rename the target, substitute a different benchmark/radius, introduce an uncertified premise and report success, drop guard/escape branches, edit CRRG core while proving a downstream task, or choose a different root than the one frozen by this spec/task contract.

---

## 8. Implementation status at v0.8.0

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
- [x] Leaf preservation is a shipped generic theorem for all three frontier operators, not an obligation each adapter re-proves (found by live deployment; see §16).

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

### DONE — Stage D historical research backtest

- [x] `crrg-stage-d-yukon` created from exact commit `f758c1b18a301fe76675cb628027360268bb15cb`.
- [x] Only neutral CRRG plumbing transplanted; no Stage B/C material.
- [x] No post-iter165 Yukon mathematics, state prose, theorem names or target decisions exposed to research agents.
- [x] Root frozen at `ProtocolClaim 7487 349526 1048576`.
- [x] Later history used only evaluator-side, after agent output.
- [x] Root substitution mechanically rejected; the later 6400 regression was never named in a task prompt, and neither agent proposed a substitution.

### DONE — External Review 2

- [x] Review packet assembled and delivered (`audits/EXTERNAL_REVIEW_2_PACKET.md`).
- [x] Review closed by owner decision. Live deployment is authorised; see §13.

### STANDING PROHIBITIONS

- [ ] No target selection by the implementation agent. Target selection inside a live deployment belongs to the research agent and is bounded by §16.4.
- [ ] No ArkLib upstreaming.
- [ ] No CRRG-directed live Soundness scheduling — **delayed by owner decision**, not by an open review item (§13).

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

### 9.3 Stage D — primary historical Yukon research backtest — COMPLETE

**Purpose:** test the actual CRRG research thesis under genuine mathematical uncertainty.

**Observed result** (`crrg-stage-d-yukon` @ `2dc5912f`):

```text
T1   UNCHANGED    claim matched observation
T2   REFUTED      Lean term of ¬ P, seal intact, axiom closure kernel-3
```

Both agents were blind to post-cutoff history and neither proposed a target
substitution. The frozen root is unchanged: one *decomposition* of it was
refuted, not the target.

The four findings — the T2 historical rediscovery and its propagation to a seam
the historical lane left standing, root preservation under route death, T1's
honest null, and the gap between logical and strategic refinement — are set out
in `audits/EXTERNAL_REVIEW_2_PACKET.md`, which is the review deliverable. The
artifact-recovery caveat recorded there is normative: the T2 result is
mathematically reverified, but byte identity with the first delivered file cannot
be established.

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
REFINED
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

### 11.1 Validation cadence and runtime budget

Soundness and iteration speed are both requirements. A deployment whose ordinary validation cycle takes hours is not usable as a live research system, even if every individual check is sensible.

Validation has three distinct tiers:

```text
PRODUCTION GATE
  verifies the invariants required to accept the current live research transition

FOCUSED REGRESSION
  exercises the property changed by an implementation edit, including the relevant
  positive / negative path, using the same underlying check implementation

FULL ACCEPTANCE SUITE
  exercises the complete deployment contract in §17
```

These tiers must not be collapsed into “rerun the complete deployment for every assertion.” A self-test must not invoke the entire production gate merely to test one local condition when the same production check can be exercised directly or through a focused gate entry point. Focused test paths may factor or parameterize production checks; they must not duplicate them into a weaker second implementation.

During implementation, the required loop is the affected focused regression(s) plus the production gate. The full acceptance suite is required once on the final candidate before push/review, not after every intermediate edit.

On the designated deployment machine, with the toolchain and dependencies already materialized:

```text
ordinary implementation validation   MUST complete within 15 minutes
full downstream acceptance suite      MUST complete within 15 minutes
production live gate                  SHOULD remain within about 5 minutes
```

First-time toolchain/package download or equivalent cold bootstrap is outside this iterative budget; bootstrap correctness remains testable separately when that boundary changes.

Exceeding the 15-minute budget is an implementation defect and blocks further growth of the acceptance suite until the redundant work is removed. The remedy is to isolate tests, batch checks, reuse already-built artifacts when sound, and remove repeated whole-gate execution — **not** to delete proof/seal/axiom/forbid requirements or convert a required verification into an unauthenticated stale cache.

`CHANGELOG.md` may continue recording detailed implementation discoveries. It must not become a second planning document.

---

## 12. External Review 2 gate

External Review 2 occurs after:

```text
A. generic core / hardening                         DONE
B. faithful 6399 reconstruction                    DONE
C. source-visible damaged-proof calibration        DONE
D. frozen iter165 / 7487 historical backtest       DONE
pinned-SHA downstream dependency                    verified
seal / forbid / axiom / negative-test gates         verified downstream
Spec.md                                               current (this revision)
```

External Review 2 must inspect the exact CRRG/downstream SHAs, final Stage B graph, Stage C limitations/results, Stage D isolation and 7487 root, any attempted target substitutions, seal scope and registry behavior, downstream promotion tooling, negative tests/axiom closure, generic-core boundary, and agent DX.

**COMPLETE.** The packet is `audits/EXTERNAL_REVIEW_2_PACKET.md`; the review is closed and live deployment is authorised under §13 and §16.

---

## 13. Soundness deployment — DELAYED BY OWNER DECISION

After External Review 2, CRRG may enter Soundness first in shadow mode. **The owner has delayed that deployment.** The first live deployment is Yukon instead (§16). This section stays normative for whenever Soundness is scheduled; nothing in it is withdrawn.

Shadow-mode work exists in `crrg-shadow-soundness` and is explicitly incomplete: the graph module builds and transcribes the seam below, and the cross-iteration observer does not. Nothing there may be cited as a Stage E finding.

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

## 14. Acceptance criteria for v0.7.2 — COMPLETE

Retained as the record of what External Review 2 was reviewed against. §17 carries the criteria for a live deployment.

- [x] `crrg-hardening` is the only active CRRG staging line.
- [x] CRRG builds independently and remains application-agnostic.
- [x] Supported downstream Lean toolchains build CRRG cleanly with warnings treated as failure.
- [x] Axiom, banned-construct, forbid, seal, and self-test gates have positive and negative controls.
- [x] Downstream Yukon consumes an exact pinned CRRG SHA.
- [x] Downstream seal registry uses the actual required application/graph namespaces and is gate-verified.
- [x] Stage B certified root graph contains MCA/list/budget decomposition and alignment refinement.
- [x] Stage C has separate raw results and documented blindness limitations.
- [x] Candidate-promotion engineering cost is recorded without pretending it is mathematical progress.
- [x] Stage D branch is created from exact iter165 commit `f758c1b18a301fe76675cb628027360268bb15cb`.
- [x] Stage D research checkout contains no post-iter165 mathematical answers.
- [x] Stage D primary target is exactly `ProtocolClaim 7487 349526 1048576`.
- [x] Any substituted root is mechanically rejected without leaking the known later 6400 regression into the task prompt.
- [x] Stage D reporting distinguishes `CERTIFIED`, `REFUTED`, `REFINED`, `MALFORMED`, `INVALID`, `SUPERSEDED`, `UNCHANGED` and `TOOLING_FAILURE` rather than collapsing them into promotion.
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

---

## 16. Live deployment — mode, and the rules a live research agent runs under

§13's shadow mode observes an executor. A **live deployment** is the other thing: CRRG governs a research programme that is actually running, and the agent inside it changes the graph. This section is the generic contract for that mode. It is application-agnostic on purpose — the first live deployment is Yukon, and every Yukon-specific numeral, seam and ladder stays downstream in `proximity-research`.

### 16.1 Mode

```text
mode                  bounded active autoresearch
concurrency           ONE research agent, one persistent process
root                  immutable within an epoch
root completion       permits an upward epoch transition, autonomously
canonical lane        protected from direct research-agent writes
```

**One agent.** A live deployment is not a calibration. Comparative lanes, A/B researchers and diligence sampling belong to Stages B–D, which are finished; running them again inside a live programme buys another synthetic comparison at the price of the thing actually worth measuring, which is whether the agent moves the target.

### 16.2 Epochs

A live programme is a sequence of **epochs**. An epoch fixes:

```text
bank    the strongest claim currently admitted by this deployment
root    the exact sealed target under research
```

Within an epoch the root is immutable. The agent may close, refute, refine or split leaves, and may step back to a certified ancestor. It may not replace the root, and this is enforced by types and seals, not by prose: every frontier operator returns a `Frontier root` for the epoch's own `root`, so a moved target is a different type and no operator produces one.

### 16.3 Root completion is a transition, not a stop

When every leaf closes and the exact root becomes certified, the programme does **not** halt:

```text
1. bank the completed claim
2. freeze the completed epoch; its graph is retained as immutable history
3. open a new epoch
4. select and seal a strictly stronger target
5. continue
```

That is a new-root transition *after success*. It is categorically different from mutating an open root, and an implementation that cannot tell the two apart has not implemented this section.

### 16.4 Monotone upward target selection

After completing an epoch the research agent selects the next target without asking the owner, **subject to a mechanical rule and nothing else**. A new target must:

```text
be an exact target triple, not prose
be strictly stronger than the bank in the project's own metric
be strictly stronger in the underlying certified quantity, not only in the score
lie strictly inside the currently certified-safe region
typecheck
be sealed before research begins
record its relation to the bank
```

Rejected: an equal target, a weaker one, a retreat to an easier underlying parameter, a re-parameterisation that does not strictly improve, an unsealed prose target, and anything at or beyond the certified ceiling.

The certified-safe region is **live state**, not a constant. It must be re-read from the project's own upper-bound record at every epoch transition, because a stronger external upper bound lowers it and a target that was legal last epoch may not be legal this one.

Where a project has a canonical parameter order and an actual monotonicity theorem, §10.2's `MonotoneFamily` applies and local numerical reward is available. Where it does **not** — where the implication between claims at different parameters is unproved — a live deployment must not declare the family anyway. The admissibility rule above is a decidable predicate over the target's own numerals and asserts no implication; that is the honest encoding, and it is the one to use.

### 16.5 External supersession

A live programme is not the only thing proving theorems. A downstream integration should automatically admit a newer authoritative external result when that import is mechanically certifiable.

If an external verifier or challenge version changes, automatic import is permitted only when the downstream integration mechanically establishes that the certified statement against which its local graph is interpreted is unchanged.

For an externally certified claim `E` that has been mechanically admitted:

```text
E weaker than or equal to the bank       no graph change
bank < E < root                           bank E; update provenance; root unchanged
E at or above the active root             mark the epoch SUPERSEDED; bank E; open a
                                           stronger admissible epoch; continue
```

Supersession is **not** an agent proof and is never counted as one. The admitted external state must name an exact external commit; a floating branch reference is not a pin.

If an external result cannot be mechanically imported, it is not admitted into CRRG state. The currently admitted exact pin remains authoritative. External synchronization and application-specific compatibility checks live in the downstream integrator.

### 16.6 Governance is not research

The research agent writes attempts, candidate propositions, proofs, research notes, and approved state-transition outputs. It does **not** write its own programme, the gate, the seal implementation, the outcome classifier, the epoch-transition rules, the dependency pin, or the protected root definitions.

The live gate must detect drift in those files by hash and fail on it. A genuinely required change to any of them is an implementation change made by an implementation agent under review, not a research iteration.

Sanctioned state transitions are not governance edits. Examples include appending a fresh candidate seal, activating a certified refinement, advancing a completed epoch, and admitting an externally certified result through the deployment's governed transition machinery. The code that implements such transitions may itself be governed; the state it is authorized to update must remain mutable through that bounded path.

**Detection, not prevention — and say which you have.** This section requires the gate to *detect* a governed-file edit; it does not claim the edit is impossible. A deployment must state its posture explicitly rather than let a reader infer enforcement from the word "governance":

```text
tamper-evident    the edit is possible, and it is caught and attributable
tamper-proof      the edit cannot happen
```

A proof-of-concept deployment may be **tamper-evident** provided it says so, and provided the audit trail is real: one research iteration is one pushed commit, history is append-only (no rebase, reset, force-push, amend-after-push, or tag rewriting), and a governed-file edit is recorded as a violation rather than silently absorbed. Under that posture the launch mechanism is not a trust boundary and must not be presented as one. Hard sandboxing — a separate principal, or kernel-enforced read-only governance — is what upgrades such a deployment to tamper-proof, and until it exists the deployment must not describe itself as protected.

### 16.6.1 Live launch

CRRG provides a generic live-launch command.

The command is invoked from the downstream repository and receives a downstream-owned live configuration containing:

- programme file;
- working repository / branch;
- model adapter configuration;
- operator exclusions;
- downstream preflight and gate commands.

CRRG owns the generic dispatch semantics. The downstream integrator owns all application-specific configuration.

A live deployment must support at least these adapter classes:

- Codex;
- Kimi;
- Claude.

Each adapter must run in its vendor-equivalent unattended / full-permission mode so permission prompts do not stall autonomous research.

CRRG must not infer vendor flags. The downstream configuration supplies the exact executable and argument vector for each adapter.

Canonical invocation:

```text
crrg-live-run --config <downstream-config> --model codex
crrg-live-run --config <downstream-config> --model kimi
crrg-live-run --config <downstream-config> --model claude
```

The launcher passes one instruction to the selected agent to read the downstream programme fully and start.

The launcher is orchestration, not a mathematical trust boundary.

### 16.7 Refinement is not a reward currency

§4.5's meaning of a certified refinement is unchanged and must not be relaxed in a live setting: a `REFINED` outcome means **the child suffices for the parent**, proved. It does not mean the research became easier, and refinement count is not a metric. A live deployment may let the agent activate a certified refinement, and should require it to record a short strategic reason for doing so, but must not reward the act. Restatements that change nothing remain graph history and do not replace the active leaf.

No live deployment is required to decide general semantic "easier than". It is not solved here and must not be faked.

#### Adjudication is not activation

`REFINED` is a statement about what was **proved**, not about what has **happened to the graph**:

```text
REFINED = the gate certified an Edge, or an exhaustive Split, sufficient for
          the current live leaf.

It does NOT by itself assert that the Frontier has already moved.
```

Activation is a separate, ordered transition:

```text
REFINED adjudicated
    → register a fresh durable seal for every new child (§5.1)
    → apply the frontier refinement
    → gate the new frontier
```

Each step can fail for its own reasons, and they are different reasons. A deployment must therefore report the two axes separately:

```text
research_outcome  = REFINED
transition_status = IMPLEMENTATION_BLOCKED
```

**No new progress or prize outcome is introduced for this**, and none is needed. What is forbidden is downgrading a certified `REFINED` to `UNCHANGED` because the activation machinery failed: that corrupts the outcome vocabulary, misattributes a harness defect to the researcher, and destroys the evidence that the mathematics was sound. If activation is blocked, the research outcome stands and the blockage is recorded as an implementation matter (§16.6).

### 16.8 Reporting

The live loop reports exactly the §9.3.4 vocabulary — `CERTIFIED`, `REFUTED`, `REFINED`, `MALFORMED`, `INVALID`, `SUPERSEDED`, `UNCHANGED`, `TOOLING_FAILURE` — one line per live task, and no aggregate progress magnitude (§5.6, §14.2 item 7). Epoch history is retained; a completed epoch is never deleted to make the current one look cleaner.

---

## 17. Acceptance criteria for a live deployment

Generic acceptance properties for a live deployment. Every item below must be exercised mechanically, with a positive / negative control where applicable. These are acceptance-suite obligations; they are **not** a requirement that every item execute inside the production live gate or be rerun after every implementation edit.

The production gate verifies the invariants required for the current live transition. Focused regressions verify the mechanism changed by an implementation edit. The full acceptance suite verifies the complete deployment before final push/review. All three obey the validation architecture and runtime budget in §11.1; testing the whole deployment repeatedly in order to assert one local condition is non-conforming.

- [ ] The admitted external-result pin is exact (commit, version, metric, and the exact claim) and internally consistent; floating or internally invalid pins fail. Remote freshness is handled only by the downstream import transition in §16.5.
- [ ] The exact epoch root passes its type-link; adjacent and wrong roots fail.
- [ ] Any lineage the project has formally refuted is not the live lineage, and that is a theorem rather than a grep.
- [ ] A valid proof yields `CERTIFIED`; a valid `¬ P` yields `REFUTED`.
- [ ] A valid `Edge` refinement and a valid `Split` refinement both yield `REFINED`.
- [ ] A hole-backed refinement is rejected by the axiom audit.
- [ ] An unrelated or easier proposed child is rejected.

Adjudicating `REFINED` is not enough, and a suite that stops there will certify a deployment whose researcher cannot act on its own results. The activation path must be exercised end to end, on a child that did **not** exist when the deployment was built:

- [ ] A genuinely fresh `Edge` child can be registered under a new durable seal and activated as a live `OPEN` leaf.
- [ ] Every fresh branch of a `Split` can be independently sealed and the full split activated.
- [ ] Existing candidate seal IDs cannot be mutated in place.
- [ ] A failed registration cannot partially mutate the registry or the frontier.
- [ ] The post-activation full gate verifies the new frontier, the root, sibling preservation, the task manifest, and all seals.
- [ ] A new live leaf that is not sealed is rejected; a manifest naming a nonexistent seal is rejected; a split with one branch sealed and one unsealed is rejected.
- [ ] An open root cannot be changed; a completed root can be banked.
- [ ] An equal or weaker next target is rejected; a strictly stronger one inside the certified ceiling is accepted.
- [ ] A prior epoch remains available as immutable history.
- [ ] A stronger external floor updates the bank; one below the root does not mutate the root; one reaching the root supersedes the epoch and is not counted as agent proof.
- [ ] The research agent cannot edit its own programme, the gate, or the transition policy; ordinary attempt files remain writable.
- [ ] The project's own pre-existing verification gate runs **unchanged** and passes.
- [ ] Operator-banned candidate IDs cannot be selected as new live work.
- [ ] Operator-banned declarations or namespaces are rejected from submitted proof dependency closure where mechanically enforceable.
- [ ] Adding a ban does not mutate the root, certified graph, or prior graph history.
- [ ] `crrg-live-run` launches a downstream programme through the configured Codex adapter.
- [ ] `crrg-live-run` launches a downstream programme through the configured Kimi adapter.
- [ ] `crrg-live-run` launches a downstream programme through the configured Claude adapter.
- [ ] All three adapters use downstream-declared unattended / full-permission execution arguments; CRRG does not infer vendor flags.
- [ ] Model selection changes no mathematical CRRG state.
- [ ] A compatible newer external result can be imported automatically by a downstream integration.
- [ ] A compatible external improvement below the root moves the bank only.
- [ ] A compatible external result reaching the root triggers `SUPERSEDED` and an upward epoch transition.
- [ ] External state whose statement compatibility cannot be mechanically certified is not admitted into CRRG state.

---

## 18. v0.9 — orchestration layer: purpose, scope, order

The first live Yukon deployment validated target preservation, sealing, certified refinement/split, refutation, external bank updates, and tamper evidence. It also exposed three orchestration failures the architecture did not prevent:

1. **Infinite preparation** — the researcher can repeatedly prove helper machinery while avoiding the hard mathematical crux.
2. **Machinery-as-progress** — kernel-clean helper theorems and repeated no-op gate passes can be mistaken for progress.
3. **Circling** — the researcher can repeatedly revisit the same exact obligation and the same family of mechanisms as research history grows.

The motivating observation is operational, not mathematical: after iteration 24 the certified frontier stopped moving, while consecutive `RIGHT-DEPTH / UNCHANGED` iterations kept accumulating Lean machinery on one unchanged obligation. v0.9 specifies the response inside what is already technically specifiable. It does not claim to solve mathematical novelty or strategic theorem discovery; §26 records what is deferred and why.

The design-lineage lesson stands: formal composition boundaries deserve to be first-class mathematical objects carrying the data and certificate needed for sound composition. v0.9 strengthens that property for research-state transitions — source state, target state, and preservation witness become first-class, and composition is kernel-proved (§20). Nothing from ArkLib or any application enters CRRG core (§2).

### 18.1 Scope rule

Implement only the parts that do not require a new automated-mathematics research programme to discover the right technique. The seven parts are §19–§25. Everything in §18–§27 is application-agnostic; the Yukon integration is Phase F (§18.3) and changes no historical state (§23).

### 18.2 Runtime requirements for v0.9 work

§11.1 remains normative. For the v0.9 implementation specifically:

```text
ordinary owner/implementor development loop
  focused affected regression(s) + production gate
  target <= 5 minutes, hard stop <= 10 minutes

full acceptance suite
  <= 15 minutes

new stall / episode / obligation / mechanism unit tests
  seconds, not whole-gate invocations
```

Before adding a test that invokes the full gate, estimate its runtime multiplier. No new feature is accepted without a runtime estimate. Do not weaken mathematical checks to meet runtime. If ordinary validation projects above 10 minutes, stop and profile before adding more tests.

### 18.3 Implementation order

The spec owner directs the implementation agent one phase at a time, in this order:

```text
A  spec only (this revision; no implementation)
B  mathematical transition core (§20); synthetic Lean tests only; no downstream changes
C  outcome semantics + stall state (§19, §22)
D  episodes / unique obligations / mechanisms (§21, §23, §24)
E  novelty evidence substrate (§25)
F  Yukon integration — only after the generic phases pass
```

Phase F must preserve the current root/bank/frontier mathematics byte-for-byte unless a sanctioned external bank sync occurs independently; must not rewrite historical iterations; must begin episode/stall semantics from a declared forward boundary; must deduplicate same-proposition live obligations; must not render `NO_TRANSITION` as CRRG progress; and must trigger the stall audit after five future terminal no-transition attempts on one obligation. The research executor is not launched until the Phase F integration diff is audited.

---

## 19. Outcome semantics: integrity versus certified transition

The pre-v0.9 outcome vocabulary conflated two questions: "is this state/outcome valid?" and "did the certified research state move?". They are separate axes.

### 19.1 Two axes

Integrity / adjudication status:

```text
VALID
REJECTED
TOOLING_FAILURE
```

Certified transition status:

```text
ADMITTED
NO_TRANSITION
```

An `ADMITTED` transition also records its semantic kind:

```text
CLOSED / CERTIFIED
REFINED
SPLIT
REFUTED
RETIRED
SUPERSEDED
exact monotone quantitative movement, where a proved family supports it
```

The legacy §9.3.4 spellings may be preserved for compatibility; the semantic separation is mandatory. §16.7's two-axis reporting (`research_outcome` versus `transition_status`) is an instance of this rule, not an exception to it.

### 19.2 `UNCHANGED` is not a successful transition

`UNCHANGED` means `VALID` + `NO_TRANSITION`. It must never be rendered to the research executor as a green "PASS" that can be interpreted as progress. The research-facing command must distinguish `NO_TRANSITION` from an admitted transition by machine-readable output and a distinct exit code:

```text
0   admitted certified transition
10  valid but NO_TRANSITION
20  rejected research/state mutation
30  tooling failure
```

The exact numbers may change where an existing CLI contract forces it; the four states must remain mechanically distinguishable. An integrity-only command may still return ordinary success for a valid unchanged state — a valid no-op is a research no-op, not a security failure.

### 19.3 Reward semantics

```text
PROJECT REWARD
  the external/canonical project gate; authoritative terminal-objective reward

CRRG CERTIFIED MOVEMENT
  a proof-carrying mutation of the faithful research state; not automatically
  terminal reward

RESEARCH EVIDENCE
  helper theorems, constructions, experiments, counterexamples; useful evidence;
  not certified graph movement unless an admitted transition consumes it
```

A green integrity check is never rendered as progress. §1's five certified research-state channels are unchanged; this section only forbids dressing the absence of movement as one of them.

---

## 20. First-class frontier transitions

Accepted research-state mutations are themselves first-class proof objects. Add the minimal generic notion:

```lean
abbrev Frontier.AllClosed (F : Frontier root) : Prop :=
  ∀ t, (F.leaf t).claim

structure Frontier.Transition (source target : Frontier root) : Prop where
  preserve : target.AllClosed → source.AllClosed
```

Names may be improved; the semantics must remain this simple. The definition must be universe-polymorphic in the two frontiers, because the existing operators change universe level (`splitLeaf` lands in `max u v`).

Required generic theorems:

```text
identity transition
transition composition
root-closure transport: source.closeRoot composed with a
  Transition source target yields target.AllClosed → root.claim
```

Every existing frontier operator must expose or induce a transition witness: `refineLeaf`, `splitLeaf`, and `retireLeaf` each induce a `Transition` from the pre-operation to the post-operation frontier. `Frontier.compose` and `Frontier.ofSplit` owe no same-root witness: `compose` changes the root (its certificate is the `Edge` itself, composed with the inner frontier's `closeRoot`), and `ofSplit` constructs an initial frontier with no source. The operator-witness requirement covers exactly the three leaf-preserving operators. The point is an explicit certified state chain

```text
F0 --T1--> F1 --T2--> ... --Tn--> Fn
```

whose kernel-produced composite `Transition F0 Fn` makes closing `Fn` entail the original root through one composed certificate.

Do not replace the existing `Goal`, `Edge`, `Split`, or `Frontier` semantics. Do not introduce category-theory machinery. Refutation is not a root-preserving transition and must not be encoded as one; candidate/route refutation remains its own proof-carrying fact (§5.1).

---

## 21. Unique live obligations

Scheduling operates on exact mathematical obligations, not frontier task positions. If several task positions carry the same exact sealed proposition, they are one research obligation; a proof of that proposition may discharge every matching position.

A canonical obligation identity is derived deterministically from the existing semantic seal information (§5.3). It must not be derived from a task display name, a generation number, or a free-text description.

The scheduler-facing state must expose:

```text
frontier positions
canonical obligation ID of each position
all positions sharing an obligation
```

This prevents duplicate research effort of the kind a live deployment produces when two positions carry the same proposition.

---

## 22. Stall detector

A generic, mechanically derived operational stall detector.

Default rule:

> Every 5 terminal `NO_TRANSITION` outcomes on the same canonical live obligation trigger `STALLED`.

This is an orchestration fact, not a mathematical theorem about difficulty or truth. The count:

- is per canonical obligation (§21);
- increments only on a terminal `NO_TRANSITION`;
- does not increment on checkpoints (§23);
- does not reset because the agent rewrites prose;
- resets when certified state movement materially changes, closes, or retires that obligation.

At every multiple of 5 (`5, 10, 15, ...`), a stall response is mandatory before another research episode may launch on that obligation. A stall response is one of:

```text
RESELECT            choose another unique live obligation
BACKTRACK           return to a certified ancestor / earlier admissible frontier position
NEW_MECHANISM       continue the same exact obligation under a different recorded mechanism
PROPOSE_REFINEMENT  provide an exact candidate + certified reduction
OWNER_OVERRIDE      explicit operator decision
```

The detector must not infer that the theorem is false, that it is too difficult, that another leaf is easier, or that the reduction is over or under depth. Those remain separate judgements (§10). A `RIGHT-DEPTH` obligation can still become operationally `STALLED`; at that point the agent changes research behaviour rather than producing more helper machinery.

Immediate relaunch of the same stalled obligation under the same recorded mechanism is rejected by the scheduler unless owner override is present. A block clears only through a recorded stall response or through certified state movement that materially changes, closes, or retires the obligation; producing further `NO_TRANSITION` outcomes never clears it.

A stall count is orchestration state. It never feeds a score, a reward, or a rendered aggregate (§1).

---

## 23. Research episodes and checkpoints

Not every helper-theorem commit is a complete research iteration. The orchestration semantics are:

```text
research episode
  exact canonical obligation
  exact certified start state
  mechanism identity (§24)
  zero or more checkpoints
  one terminal outcome
```

A checkpoint may contain Lean lemmas, experiments, notes, and computations. It is append-only research evidence. It does not mutate the certified graph, does not increment the stall detector, does not produce `UNCHANGED`, and does not restart task selection.

A terminal outcome is exactly one of: an admitted certified transition; `NO_TRANSITION`; a rejection or tooling failure (§19).

Existing Git history remains valid evidence. Historical iterations are not rewritten; this is forward-only orchestration semantics, beginning from a declared forward boundary in each deployment.

---

## 24. Mechanism identity

Semantic mechanism equivalence is not solved in v0.9 (§26, R2). What exists is a stable mechanism-record substrate.

A mechanism record is append-only and ties together:

```text
canonical obligation ID (§21)
certified route / ancestor anchor
stable mechanism ID
optional exact candidate IDs
declared basis theorem / declaration names that mechanically resolve
```

The system may fingerprint the record deterministically. The fingerprint means only "the researcher declared this as the same recorded mechanism". It does not certify mathematical novelty, and new prose alone must not silently mutate an existing record.

Enforcement is asymmetric, and the asymmetry is normative. The basis declarations are mechanically resolved (`resolve-check` against the configured environment). The anchor is declarative: it is fingerprinted with the record, so it cannot be silently changed under a fixed mechanism id, but nothing resolves it against certified lineage, because v0.9 prescribes no anchor shape. Prescribing one (a generation lineage theorem, a sealed candidate id, a commit) is a §24 decision deferred until a deployment has a real usage pattern to prescribe from; until then a checker would be inventing a convention, not verifying one.

Mechanism identity is used for stall-response enforcement (§22), visit history, detection of immediate repetition, and later novelty/circling research (§25, §26). No heuristic embedding or similarity score enters the trust boundary.

---

## 25. Novelty evidence substrate — no novelty score

Novel mathematics and graph movement are not the same thing; the live deployment demonstrated both directions. v0.9 records evidence without pretending to measure novelty.

For each episode or checkpoint, a machine-readable evidence record may be attached to exact Lean declarations:

```text
declaration
type fingerprint                   caller-supplied deterministic digest (sha256
                                   over the declaration's type, as in the §5.3
                                   seal definition); `-` when not computed —
                                   the evidence tool never invents one
source commit
dependency closure fingerprint     same rule, over the transitive in-scope
                                   dependency closure; `-` when not computed
intended exact consumer / obligation
whether the consumer is certified / live
the episode the record belongs to
```

Permitted mechanical classifications:

```text
NEW_DECLARATION
EXISTING_DECLARATION
IN_ADMITTED_EPISODE
NOT_IN_ADMITTED_EPISODE
```

The names assert exactly what is computed. The first pair is log-local bookkeeping: first or later appearance of the (declaration, type fingerprint) pair in the evidence log. The second pair is co-occurrence: whether the record's episode terminated `admitted-*`. Co-occurrence is not dependency-closure consumption — whether an admitted transition's witness actually depends on a declaration is a question about that witness's closure, checkable downstream with the existing §6 forbid-class machinery, and deliberately not asserted by the evidence log.

An optional human or research-loop label may exist:

```text
NOVELTY_UNASSESSED
KNOWN_OR_FORMALIZATION
CANDIDATE_NOVEL
```

It is metadata only and must never affect certified state or project reward.

Not implemented, and forbidden as trusted state:

```text
novelty percentages
theorem-count rewards
LLM novelty judging as trusted state
literature novelty claims from syntax
any scalar "research progress" score
```

The substrate exists so a later dedicated novelty-research programme has evidence to work on (§26, R1). Evidence records cannot mutate the root, the frontier, candidate truth state, project reward, or the stall count except through normal terminal episode semantics.

---

## 26. Deferred — each requires its own research programme

The following are not v0.9 implementation tasks. Each needs separate automated research or experimental work to find a defensible mathematical or algorithmic technique.

**R1. True mathematical novelty measurement.** Distinguishing a novel theorem from a reformulation, specialization, rediscovery, or straightforward formalization. Needs research on theorem equivalence / implication search, bounded corpus comparison, literature provenance, semantic novelty evidence, and adversarial gaming. v0.9 only captures evidence (§25).

**R2. Semantic mechanism equivalence.** When two research routes are genuinely distinct mathematical mechanisms rather than renamed variants. v0.9 records mechanism identities (§24) and certifies nothing about equivalence or difference.

**R3. Strategic reduction quality.** Certifying or predicting that a logically sufficient child is a strategically better research target. CRRG does not invent an "easier than" oracle; the §10 depth audit remains explicit judgement.

**R4. Automatic mechanism synthesis after stall.** Given a precise obstruction, synthesizing a genuinely new mathematical attack rather than another helper lemma. A natural dedicated autoresearch benchmark.

**R5. Semantic obstruction objects.** First-class exact "obstruction" objects connecting failed mechanisms, counterexamples, and missing premises to candidate new reductions. Not standardized before empirical and mathematical research demonstrates the right abstraction.

---

## 27. Acceptance criteria for v0.9

v0.9 is ready for downstream live testing only when every item is true. These join §17's live-deployment criteria; both sets are exercised under the §11.1 / §18.2 validation architecture.

- [x] Accepted frontier mutations have first-class composable preservation witnesses (§20). — `CHG-34`
- [x] A composite certified state chain mechanically yields root closure from final frontier closure. — `CHG-34`
- [x] `NO_TRANSITION` is mechanically distinct from an admitted transition (§19). — `CHG-35`
- [x] The research-facing CLI neither prints nor returns ordinary success for `NO_TRANSITION`. — `CHG-38`; auditor-run gate: exit 10
- [x] Canonical unique obligations deduplicate duplicate frontier positions (§21). — `CHG-36`, wired downstream `CHG-38`
- [x] Five terminal no-transitions on one obligation mechanically trigger `STALLED` (§22). — `CHG-35`, `CHG-36`
- [x] Checkpoints do not increment the stall count (§23). — `CHG-35`, `CHG-36`
- [x] The stall detector asserts no mathematical falsehood or difficulty (§22). — `CHG-35`
- [x] The same stalled obligation under the same recorded mechanism cannot immediately relaunch without explicit owner override (§22, §24). — `CHG-36`, enforced at `open` `CHG-38`
- [x] Mechanism history is append-only and deterministic (§24). — `CHG-36`
- [x] Novelty evidence is recorded without becoming reward or trusted state movement (§25). — `CHG-37`
- [x] Old CRRG core semantics and seals remain valid. — every phase strictly additive; gates green throughout
- [x] The generic CRRG full acceptance suite remains within its runtime budget (§11.1, §18.2). — `crrg-check` ≈ 50 s. Note: the downstream *acceptance tier* exceeds 15 min; recorded in `CHG-38` for the owner
- [x] The downstream Yukon integration preserves the current certified mathematics (§18.3). — `CHG-38`; frozen set byte-identical, auditor-verified
- [x] Historical Yukon iterations are not rewritten (§23). — `CHG-38`

Stop for owner review after Phase F before launching live autoresearch under v0.9 semantics.

---

## 28. v0.10 — persistence and novelty pressure: purpose, evidence, scope

v0.9 made certified research-state movement honest and made circling visible. It did not make research *persistent*: three days of live operation showed the failure mode directly. The researcher concluded — in a system whose programme already says "do not stop because the mathematics is novel, absent from the literature, hard, or because the last attack failed" — that further commits "would be the treadmill", and stopped. Mathematical ignorance was converted into a self-authored exit. Separately, the first-order stall machinery cycled as designed but without a second order: one obligation accumulated 23 strikes and 4 recorded responses with no structural consequence.

v0.10's invariant:

> **An exact OPEN obligation is an active research mandate. Lack of a known technique is not a blocker. Stalling changes how the system researches; it does not authorize the researcher to stop.**

What does not change: the mathematical core (`Goal`, `Edge`, `Split`, `Frontier`, `Frontier.Transition`), the candidate lifecycle, seals, axiom policy, root immutability, external bank/supersession semantics, the two-axis outcome model (§19), the first-order stall detector (§22), and the novelty-evidence substrate with no scores (§25). v0.10 is an orchestration/persistence layer on top of them. Any Lean-core addition needs a stated mathematical reason.

---

## 29. The research-persistence invariant

While all of the following hold, a live autonomous research programme **must remain active**:

```text
at least one exact admissible obligation is OPEN
no certified result has eliminated that obligation
the operator has not explicitly stopped the project
required tooling is operational
```

The following are **not blockers**. They are descriptions of the research problem:

```text
"I do not know how to prove this."
"No known theorem gives the required bound."
"This appears to require a new invariant."
"The literature stops here."
"A stronger candidate might be false."
"I need to choose constants."
"I have exhausted known methods."
"Further work would require novel mathematics."
"Continuing would be machinery production."
```

### 29.1 Objective blocker taxonomy

A research run may stop or pause only for a small explicit class of objective conditions:

```text
OPERATOR_STOP        authenticated operator instruction
TOOLING_BLOCKED      required compiler / repository / execution facility unavailable
                     after the deployment's defined retry/recovery policy
NO_ADMISSIBLE_WORK   no OPEN schedulable obligation remains under the certified
                     graph and operator policy
PROGRAM_COMPLETE     the project's terminal condition reached and no automatic
                     next target admissible
```

A certified closure, refutation, retirement, split, or supersession is a state transition, not a reason for the programme to stop. **There is no generic `RESEARCH_BLOCKED` escape hatch.** A deployment that finds itself wanting one has an underspecified programme, not a blocker.

---

## 30. The research-facing response to NO_TRANSITION

The two-axis semantics (§19) and exit code 10 are unchanged. What changes is the rendering to the researcher. A valid no-transition must say, in machine-readable form plus concise text:

```text
NO_TRANSITION
The exact certified obligation remains OPEN.
No certified blocker has been established.
CRRG has accepted no state movement.
The absence of a known proof technique is the research problem,
not a stopping condition.
Continue mathematical research on an admissible OPEN obligation.
```

A research loop must not interpret exit 10 as termination, and an integrity-only green result must never be presented as grounds to stop either. The downstream programme wording lands at integration (§35's phases); the contract is normative now.

---

## 31. NOVELTY_REQUIRED — the second-order state

The v0.9 stall detector is first-order: five terminal no-transitions on one canonical obligation force a recorded response. Live evidence shows the first-order cycle can itself circle: stall → new mechanism → no transition → stall. v0.10 adds the second order.

### 31.1 Definition

Per canonical obligation, count **completed stall cycles**: a cycle is a block event followed by its recorded response (§22). When the count of completed cycles since the last admitted transition on that obligation reaches the deployment default of **3** (downstream-configurable), the obligation enters `NOVELTY_REQUIRED`.

### 31.2 What it means, and what it does not

`NOVELTY_REQUIRED` is an orchestration fact: repeated attempts under recorded mechanisms have failed to produce certified movement, so the next research on this obligation must prioritize inventing a new mathematical mechanism over further routine formalization around the same obstruction.

It is **not** a mathematical novelty certificate. It asserts nothing about whether the needed theorem is objectively novel, whether the literature contains a solution, or whether previous mechanism records are semantically exhaustive.

It is **not an escalation**. `NOVELTY_REQUIRED` never asks the owner to choose mathematics and never pauses research. It changes the *mode* of research, not its continuation.

### 31.3 The novelty-mode research contract

An episode opened on a `NOVELTY_REQUIRED` obligation is a novelty-mode episode. Its contract to the researcher:

```text
INPUT   the exact OPEN proposition; immutable root lineage; certified ancestors
        and current frontier; the previous mechanism records with their exact
        basis declarations; relevant research-evidence records; certified
        refutations / counterexamples / failed candidates; the current
        obstruction summary

TASK    invent and test mathematics capable of attacking the exact obligation.
        Not: rephrase the obstruction; formalize another standard consequence;
        repeat a prior mechanism under a new name; stop because a new theorem
        is required; return mathematical choices to the operator.
        Seek: a new invariant, construction, decomposition, estimate,
        representation, contradiction, or other substantive mechanism.

OUTPUT  preferably one of: a proof of the exact obligation; a certified
        refinement / split; a certified refutation; an exact new candidate
        proposition with a concrete rootward route; a falsifier eliminating a
        significant mechanism; a concrete first theorem of a new attack.
```

CRRG does not judge whether the output is truly novel (§25's substrate records; §26's R1 remains deferred).

### 31.4 Enforcement and reset

Enforcement sits at the same point as §22's: `crrg-episode open`. While an obligation is in `NOVELTY_REQUIRED`, a normal-mode open is refused; the open must declare novelty mode. The obligation leaves `NOVELTY_REQUIRED` when an admitted transition materially changes, closes, or retires it — the same reset rule as §22, proved on the same state.

### 31.5 Launch modes are downstream policy

The scheduler signal is generic: `NORMAL_RESEARCH` / `STALLED_RESEARCH` / `NOVELTY_REQUIRED`. A deployment may map modes to different executor configurations (a higher-effort reasoner, a different model family, parallel independent researchers, a synthesis/review swarm). CRRG core knows no vendors, model names, or flags; the mapping lives in the downstream launch configuration (§16.6.1's adapter mechanism).

---

## 32. Adjudication and application: episodes and APPLY events

v0.9's live deployment produced, organically, a two-episode pattern for `REFINED`-then-activate (a research episode, then an activation episode under a second mechanism id). v0.10 standardizes the underlying reality and retires the pattern:

```text
RESEARCH EPISODE
  → one terminal adjudication (§19's two axes, unchanged)
  → if ADMITTED: APPLY event(s) recording every certified effect committed
```

`APPLY` is bookkeeping and state mutation, not research, and never opens an episode. An apply event records the *full* effect list — frontier refinement (naming edge or split), child closure, candidate resolution, retirement, epoch advance, external admission — rather than forcing simultaneous certified effects through one winner-takes-all token. This supersedes the §16.7-era practice of a separate activation episode and the F.1-era most-specific-first token ladder: the episode's terminal token expresses the adjudication; the apply event expresses the state movement; neither masquerades as the other.

The stall detector and the second-order counter read the adjudication axis only. Apply events never increment either.

---

## 33. Automatic checkpoints; refusal logging

Voluntary checkpoint bookkeeping failed in live operation (zero voluntary rows in three days; research evidence landed as ordinary git commits instead). v0.10 removes the discipline burden:

1. While an episode is open, a research commit on the deployment branch that is not the episode's terminal commit **is** a checkpoint of that episode and is recorded as one automatically — the gate (and the episode-close path) derives checkpoint rows from the branch's own history since the episode opened, so the record cannot be skipped. Checkpoint rows change nothing: no stall increment, no certified-state mutation, no task-selection restart (§23 unchanged in substance). If this derivation proves mechanically unreliable in a deployment, the deployment declares git the authoritative checkpoint history and the row type is retired there — an unused ceremonial mechanism is not kept.
2. A refused launch leaves a trace: a `REFUSED_LAUNCH` event appended at refusal time, carrying the obligation, the mechanism, the reason class, and the state reference. It opens no episode, produces no outcome, changes no mathematical state, and increments no counter. Its purpose is audit: enforcement that fires must be distinguishable from enforcement that never fires.

---

## 34. The owner-decision boundary

v0.10 makes the boundary explicit because live operation showed the agent delegating mathematical decisions upward (which is also the escalation-as-exit failure in embryo).

The research agent decides: proof technique; candidate theorem; constants inside a candidate; which admissible open obligation to attack; which certified ancestor to revisit; which mechanism to abandon; which conjecture to test; which strengthening to try; which computation decides a mathematical claim; which certified refinement to propose. If a candidate might be false, test it — that is research.

The owner decides: project/root policy; trust and axiom policy; operator bans; resource policy; external-import policy; stopping the programme; resolving an actual governance ambiguity.

The agent must not present a choice between two mathematically admissible options to the owner unless choosing one would mutate owner-governed policy.

---

## 35. v0.10 deployment: forward-only, runtime, phases

Historical iterations (1–116 at this writing) are not rewritten. New semantics begin at a declared boundary (`CRRG_PERSISTENCE_FROM=<commit/episode>`) in each deployment.

Runtime: the second-order state, refusal logging, checkpoint derivation, and apply-event logging are orchestration bookkeeping and must cost seconds, with **no new full-gate invocation** introduced to test them; the production gate stays at its current cost; the §11.1/§18.2 budgets remain normative.

Implementation order, spec-owner directed:

```text
A  spec only (this revision)
B  persistence invariant + objective blocker semantics, outcome rendering contract
C  second-order NOVELTY_REQUIRED state (generic)
D  episode/APPLY/refusal/checkpoint model (generic)
E  generic launch-mode signal
F  Yukon integration
G  live programme wording (OPEN / STALLED / NOVELTY_REQUIRED / PROVE IT)
```

Stop for owner review before live relaunch under v0.10 semantics.

---

## 36. Acceptance criteria for v0.10

- [ ] An OPEN obligation with a valid no-transition leaves the loop authorized to continue, and the research-facing response carries the §30 persistence semantics.
- [ ] Five terminal no-transitions on one canonical obligation trigger `STALLED` (§22, unchanged).
- [ ] After a stall response, research may continue under a permitted changed action.
- [ ] Three completed stall-response cycles without an admitted transition trigger `NOVELTY_REQUIRED`.
- [ ] `NOVELTY_REQUIRED` never produces STOP and never escalates a mathematical choice to the owner; it opens only novelty-mode episodes.
- [ ] An admitted transition clears stall-cycle and novelty-required state for the materially changed obligation.
- [ ] A tooling failure increments no stall count and no cycle count.
- [ ] The agent cannot create an operator override by itself.
- [ ] Mathematical-ignorance text ("a new theorem is required", "the literature stops here", "further work is machinery production") creates no blocker state.
- [ ] A refused launch leaves a `REFUSED_LAUNCH` audit event; no episode exists; no counter moved.
- [ ] A research commit during an open episode is recorded as a checkpoint automatically, or the deployment has declared git authoritative and retired the row type.
- [ ] An adjudication with multiple certified effects produces one research episode and an apply event recording every effect.
- [ ] Old CRRG core semantics, seals, and the v0.9 records remain valid; nothing historical is rewritten.
- [ ] The new machinery adds no full-gate invocation and stays within the §11.1/§18.2 budgets.

The key sentence this revision exists to enforce:

> **CRRG must never allow "this requires new mathematics" to become a stopping condition while an exact admissible obligation remains OPEN.**
