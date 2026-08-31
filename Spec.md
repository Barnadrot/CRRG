# Certified Research Reduction Graph (CRRG)
## Kernel-checked research reduction and agent credit assignment

**Status:** v0.8.0 — External Review 2 complete; first live deployment is Yukon, in bounded active autoresearch.  
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
bank    the strongest claim certified so far, from any source
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

A live programme is not the only thing proving theorems. Before each research **session or resume** — not each iteration — the programme checks the project's authoritative external result against its pin:

```text
external unchanged, or weaker than the bank   continue the epoch
stronger than the bank, below the root        bank it; keep the root; update provenance
at or above the active root                   mark the epoch SUPERSEDED; bank; open a
                                              stronger epoch; continue
```

Supersession is **not** an agent proof and is never counted as one. The sync must be explicit and logged, and its pin must name an exact external commit; a floating branch reference is not a pin.

### 16.6 Governance is not research

The research agent writes attempts, candidate propositions, proofs, research notes, and approved state-transition outputs. It does **not** write its own programme, the gate, the seal implementation, the outcome classifier, the epoch-transition rules, the dependency pin, or the protected root definitions.

The live gate must detect drift in those files by hash and fail on it. A genuinely required change to any of them is an implementation change made by an implementation agent under review, not a research iteration.

**Detection, not prevention — and say which you have.** This section requires the gate to *detect* a governed-file edit; it does not claim the edit is impossible. A deployment must state its posture explicitly rather than let a reader infer enforcement from the word "governance":

```text
tamper-evident    the edit is possible, and it is caught and attributable
tamper-proof      the edit cannot happen
```

A proof-of-concept deployment may be **tamper-evident** provided it says so, and provided the audit trail is real: one research iteration is one pushed commit, history is append-only (no rebase, reset, force-push, amend-after-push, or tag rewriting), and a governed-file edit is recorded as a violation rather than silently absorbed. Under that posture the launch mechanism is not a trust boundary and must not be presented as one. Hard sandboxing — a separate principal, or kernel-enforced read-only governance — is what upgrades such a deployment to tamper-proof, and until it exists the deployment must not describe itself as protected.

### 16.6.1 The launch mechanism is not part of the trust model

CRRG is model-agnostic. A deployment must not hardcode a vendor CLI into its harness, and must not depend on a launcher to configure the researcher: the programme is a self-sufficient operating contract, and launching is a human running whichever agent CLI they chose with one instruction to read it. Any launcher that survives is an optional convenience — it may check the branch, the governance hashes and the programme's integrity, and it must not be the only path by which a correct session can start.

### 16.7 Refinement is not a reward currency

§4.5's meaning of a certified refinement is unchanged and must not be relaxed in a live setting: a `REFINED` outcome means **the child suffices for the parent**, proved. It does not mean the research became easier, and refinement count is not a metric. A live deployment may let the agent activate a certified refinement, and should require it to record a short strategic reason for doing so, but must not reward the act. Restatements that change nothing remain graph history and do not replace the active leaf.

No live deployment is required to decide general semantic "easier than". It is not solved here and must not be faked.

### 16.8 Reporting

The live loop reports exactly the §9.3.4 vocabulary — `CERTIFIED`, `REFUTED`, `REFINED`, `MALFORMED`, `INVALID`, `SUPERSEDED`, `UNCHANGED`, `TOOLING_FAILURE` — one line per live task, and no aggregate progress magnitude (§5.6, §14.2 item 7). Epoch history is retained; a completed epoch is never deleted to make the current one look cleaner.

---

## 17. Acceptance criteria for a live deployment

Generic; each is a mechanical check the deployment's own gate must run before an agent is launched.

- [ ] The external result pin is exact (commit, version, metric, and the exact claim), internally consistent, and a stale pin fails.
- [ ] The exact epoch root passes its type-link; adjacent and wrong roots fail.
- [ ] Any lineage the project has formally refuted is not the live lineage, and that is a theorem rather than a grep.
- [ ] A valid proof yields `CERTIFIED`; a valid `¬ P` yields `REFUTED`.
- [ ] A valid `Edge` refinement and a valid `Split` refinement both yield `REFINED`.
- [ ] A hole-backed refinement is rejected by the axiom audit.
- [ ] An unrelated or easier proposed child is rejected.
- [ ] An open root cannot be changed; a completed root can be banked.
- [ ] An equal or weaker next target is rejected; a strictly stronger one inside the certified ceiling is accepted.
- [ ] A prior epoch remains available as immutable history.
- [ ] A stronger external floor updates the bank; one below the root does not mutate the root; one reaching the root supersedes the epoch and is not counted as agent proof.
- [ ] The research agent cannot edit its own programme, the gate, or the transition policy; ordinary attempt files remain writable.
- [ ] The project's own pre-existing verification gate runs **unchanged** and passes.
