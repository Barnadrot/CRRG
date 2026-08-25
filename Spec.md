# Certified Research Reduction Graph (CRRG)
## A kernel-checked partial-progress architecture for the Proximity Grand Challenges

**Status:** v0.6 — first revision reconciled against a building, self-testing implementation. Supersedes v0.5 (spec-only).  
**Repository architecture:** CRRG is a standalone general-purpose Lean repository consumed as a pinned dependency by research projects.  
**First downstream integration:** private `proximity-research` LDB soundness program (`soundness` branch).  
**Historical integration target:** existing frozen Disprove side, unchanged by this revision.  
**Secondary downstream integration:** MCA program (`mca-merger`) after the LDB pilot.  
**Design source:** ArkLib IOR / security-composition architecture, adapted to a static extremal-combinatorics problem rather than implemented as an actual interactive oracle reduction.  
**CWSS lineage / keywords:** `IOR relations → CWSSPackage → exact relation seams → guarded CWSS → escape events → sequential composition → CRRG typed edges / guards / escapes / frontier lineage → sealed candidate promotion`.  
**Key inheritance:** ArkLib CWSS showed that a local proof module is composable only when its input/output relation seam is exact; guarded and escape variants keep runtime checks and exceptional failure modes explicit instead of silently dropping them. CRRG abstracts that discipline from interactive-protocol security to general autonomous mathematical research.

---

## 1. Problem statement

The current research loop has an exact final reward but a weak intermediate reward.

For LDB, the frozen endpoint is:

```lean
def Achievable (δ : ℚ) : Prop :=
  ∃ B : ℕ, ListDecodingChallenge KBField targetCode δ B
```

with `achievable_antitone`, the dual `Broken`, and `no_overlap` forming the trusted two-sided squeeze. The ArkLib bridge then transports the executable-side theorem to the actual ArkLib Grand Challenge witness type.

This endpoint is correct, but it is too coarse for a long automated research program. A research iteration can establish a major structural theorem, eliminate a complete case, or replace a large counterexample family by a much smaller rigid family while leaving `δ_lo` unchanged. Humans understand that as progress because they retain the proof graph in context. The Lean kernel currently does not expose that proof graph as a first-class object, and the main verification gate deliberately prints only the prize metric because any synthetic magnitude becomes gameable.

The result is a credit-assignment problem:

- the global reward is exact but extremely sparse;
- state files contain the real research decomposition, but state prose is not a theorem;
- agents can spend many iterations on useful lemmas without a precise local success condition;
- worse, an informal split can omit a case, assume a guard that was never justified, or retain a historical hypothesis that later turns out false.

The CRRG is intended to make the *decomposition itself* kernel-visible.

---

## 2. Repository Architecture — Standalone CRRG, Thin Downstream Adapters

CRRG is a **standalone general-purpose Lean library and agent-development tool**. It must not be implemented as a permanent subtree of `proximity-research`.

`proximity-research` is the first serious downstream application and integration test, not the ownership boundary of the CRRG abstraction.

### 2.1 Dependency direction

The required dependency direction is:

```text
CRRG
  ▲
  │ pinned Lean/Lake dependency
  │
proximity-research
```

and later:

```text
CRRG
  ▲             ▲
  │             │
proximity-research   other formal-research projects
  │
  ├── LDB Soundness adapter
  └── MCA adapter
```

CRRG must never import:

- `ProximityPrize`;
- `proximity-research`;
- ArkLib application modules;
- Reed–Solomon-specific mathematics;
- `Achievable`, `Broken`, `Lambda`, MCA, H2, Yukon, radii, security bits, or any project-specific theorem vocabulary.

If the generic CRRG package appears to require one of these concepts, the abstraction boundary is wrong and the concept belongs in a downstream adapter.

### 2.2 Standalone repository contents

Recommended repository shape:

```text
crrg/
  lakefile.lean
  lean-toolchain

  CRRG/                        -- core library: Lean core only, no Mathlib
    Basic.lean                 -- Goal, Edge
    Split.lean
    Witness.lean               -- BadNode, WitnessMap, WitnessSplit
    Guarded.lean
    Escape.lean
    Frontier.lean              -- Frontier + refineLeaf / splitLeaf / retireLeaf
    Candidate.lean
    Audit.lean                 -- type-link helpers

  Test/                        -- test library: may depend on Mathlib
    Support/
      ExpectFailure.lean       -- #expect_failure negative-test harness
    Synthetic/
      Edge.lean
      Witness.lean
      Split.lean
      Refinement.lean
      Guarded.lean
      Escape.lean
      CandidateSeal.lean
      NegativeTests.lean

    YukonReplay/               -- Stage B; not present until Stage A is complete
      ... integration fixture / adapter ...

  scripts/
    crrg-check                 -- build + tests + declarations + axiom audit
    crrg-audit                 -- transitive collectAxioms gate (§14.2 item 3)
    axiom_audit_body.lean.in   -- elaborator body used by crrg-audit
    crrg-status
    crrg-lineage
    crrg-seal
    crrg-promote-check

  CHANGELOG.md                 -- conformance matrix and audit trail
  AGENTS.md
  README.md
```

`Edge` lives in `Basic.lean` beside `Goal` rather than in its own file: an edge
is meaningless without a goal, and §13's pilot layout likewise groups them.

The **core library** must remain Lean-core-only. The **test library** may take
additional dependencies, including Mathlib, because nothing downstream links
against it; a test-only dependency does not constrain a consumer's version
resolution. This split is what lets the synthetic fixtures use `ℚ` and other
Mathlib structure while the shipped semantics stay dependency-free.

The generic core should be as dependency-light as practical. Prefer Lean core types and logic where sufficient. Avoid creating an unnecessary independent Mathlib-version constraint merely for basic CRRG semantics.

### 2.3 Downstream `proximity-research` adapter

`proximity-research` consumes CRRG and owns only application-specific graph declarations:

```text
proximity-research/
  ProximityPrize/
    Squeeze/
      Soundness/
        ResearchGraph/
          Root971426.lean
          Current.lean
          Pins.lean
          Candidates/
          Tasks/
```

Typical downstream code:

```lean
import CRRG
import ProximityPrize.Squeeze.Soundness.MomentRecovery

def target971426 : CRRG.Goal :=
  ⟨Achievable ((971426 : ℚ) / 2097152)⟩
```

The actual mathematics remains in `proximity-research`. CRRG only represents and checks dependency semantics.

### 2.4 Development checkout versus trusted integration

For local development, use sibling checkouts:

```text
workspace/
  crrg/
  proximity-research/
  proximity-prize/
```

The CRRG implementation agent may point the downstream projects at the sibling CRRG checkout for fast edit/build cycles.

For reproducible or live research runs, downstream projects must consume an **exact pinned CRRG commit SHA**.

Conceptually:

```text
development:
  proximity-research -> ../crrg

trusted/live:
  proximity-research -> CRRG @ <exact SHA>
```

A CRRG API update is therefore a deliberate dependency upgrade:

```text
push CRRG commit
    ↓
pin downstream repo to exact SHA
    ↓
update Lake manifest
    ↓
run downstream graph tests + existing project gate
    ↓
resume research agents
```

### 2.5 Trust separation

The standalone dependency creates three distinct authority layers:

```text
CRRG
  defines what counts as a valid edge, refinement, candidate,
  promotion, guard, escape, and lineage
        ↓ pinned / rarely changed

proximity-research ResearchGraph adapter
  declares what the current project-specific proof graph is
        ↓ changes as research understanding changes

research agents
  prove, refute, or refine exact leaves/candidates
        ↓ changes continuously
```

CRRG semantics are analogous to the **rules of the research game**.

The downstream graph is the **current formal model of the research problem**.

The research theorems are **moves in that game**.

An ordinary Soundness research agent should not be able to modify the CRRG dependency while attempting to promote or close a task.

### 2.6 Dependency, not vendoring

The default production integration is a pinned dependency, **not vendored CRRG source**.

Reasons:

- cleaner trust boundary;
- no accidental CRRG semantic edits by project research agents;
- forces genuinely generic APIs;
- avoids adding more permanent code to an already very large research repository;
- permits CRRG to serve unrelated future research projects;
- makes rollback trivial;
- avoids the high extraction cost of separating generalized infrastructure after months of project-specific growth.

A sibling local checkout is permitted for CRRG development ergonomics. This does not change the production ownership boundary.

### 2.7 Rollout consequence

Final integration into `proximity-research` should be intentionally boring:

```text
1. pause live research briefly
2. update/pin CRRG dependency
3. add or update thin Soundness ResearchGraph adapter
4. run CRRG checks
5. run existing proximity-research gate unchanged
6. give agents a short CRRG usage update
7. resume
```

The underlying Soundness mathematics must not require migration into CRRG.

Removing CRRG should likewise require only reverting the dependency/adapter integration, not rewriting the mathematical proof tree.

---

## 3. Source-derived design constraints

### 3.1 What to reuse from ArkLib

ArkLib treats `OracleReduction/` as its conceptual center. Its key architectural idea is not “protocols are interactive”; it is that a large security theorem is represented by typed intermediate statements, explicit relations, named security properties, and composition theorems.

Relevant patterns:

1. **Type signature separated from semantics/security.** `ArkLib/OracleReduction/Basic.lean` defines the IOR/reduction interfaces; execution and security live separately.
2. **Relations and quantitative properties are explicit.** `Security/Basic.lean` defines completeness/soundness against explicit input/output relations and explicit error values, with monotonicity lemmas.
3. **Composition is a theorem, not a convention.** `ProtocolSpec/SeqCompose.lean` and `Composition/Sequential/*` build sequential composition and transport properties through it.
4. **Guards cannot be silently dropped.** `CoordinateWiseSpecialSoundness/Guarded.lean` exists because a runtime check may consume data that a later statement drops. The check must remain explicit in the semantics.
5. **Exceptional outcomes are explicit.** ArkLib’s CWSS “escape” packages compose a normal reduction together with a named escape event instead of pretending the exceptional branch disappeared.
6. **Grand Challenge endpoints are boundary objects.** `GrandChallenges.lean` represents LDB/MCA as monotone boundary problems, with lower/upper witness structures and exact integer-grid semantics.
7. **`Code.Lambda` is a good canonical quantity.** ArkLib makes `Lambda` primitive and provides finite-subset characterizations (`Lambda_le_of_forall_finset_card_le`), finiteness consequences, and radius monotonicity.

CRRG should copy these *composition disciplines*, not the IOR execution monad.

### 3.2 What to preserve from `proximity-research`

The private repository already has strong trust engineering:

- `Invariant.lean` freezes the actual LDB contract (`Achievable`, `Broken`, monotonicity, `no_overlap`).
- `ArkLibBridge.lean` proves the private code/domain/metric are the ArkLib code/domain/metric and constructs the actual Grand Challenge witness.
- `verify.sh` treats the kernel plus frozen invariant as the only soundness authority, bans untrusted constructs, audits axioms, type-links outputs, and keeps the prize metric separate from hygiene.
- `soundness_program.md` already requires every idea to name a downstream consumer and explicitly warns that an isolated true slice is not progress.
- `SQUEEZE_SHARED.md` demonstrates why the graph must be versioned: the historical `ClassCapAt 971426 176342654` implication remains kernel-correct while its hypothesis is now known false. The live branch now holds `d = 971426`, with the maximal tight-inversion order `k0 = 370796931` used inside the research route, while the exact landed root seam is the two-premise `MomentRecovery` consumer described below.
- `state/soundness/FRONTIER.md` is the live research north star. As of iteration 1132 it fixes one unconditional discharge blueprint and explicitly forbids target renaming/subdivision as a way to manufacture progress.
- `state/soundness/STATUS.md` is historical and must not override the `FRONTIER.md` head or the current rung re-derivation in `SQUEEZE_SHARED.md`.
- `mca-merger` has a parallel `MCA_Achievable` / `MCA_Broken` frozen contract, so the same framework should generalize later.

CRRG must therefore be additive. It must **not** replace `Invariant.lean`, `ArkLibBridge.lean`, `verify.sh`, or the existing prize ledger.

---

## 4. Core decision

**Do not encode LDB as an ArkLib `OracleReduction`.**

The Grand LDB problem is a static extremal problem, so protocol transcripts, challenges, oracle interfaces, and execution semantics would be irrelevant overhead.

Instead implement a static analogue:

> A CRRG node is an exact mathematical obligation. A CRRG edge is a kernel theorem showing how discharge of one obligation discharges another. A split is valid only when the kernel proves that all branches cover the parent obligation. Exceptional/guard-failure branches remain explicit. The live frontier is a typed package whose complete discharge implies the unchanged Grand Challenge target.

The architecture should feel like ArkLib CWSS packages, but the semantic currency is proof obligations / counterexample witnesses rather than protocol executions.

---

## 5. Trust model and non-negotiable invariants

### 5.1 Frozen root

The root remains the existing target, for example:

```lean
Achievable (971426 / 2097152 : ℚ)
```

and eventually an exported ArkLib `ListLowerWitness` via the existing bridge.

No CRRG change is allowed to redefine `Achievable`, the code, the field, the domain, the security threshold, or the radius normalization.

### 5.2 Every edge is Lean

No prose-only arrow counts.

A state memo may propose

```text
MomentTarget -> quadratic locator configuration
```

but that node does not enter the trusted frontier until Lean contains a theorem of the exact implication/classification type.

### 5.3 Every split proves coverage

An agent may not earn credit for proving cases `A`, `B`, and `C` unless the parent-to-branches theorem proves that every parent counterexample lies in `A ∨ B ∨ C` (or a dependent equivalent).

### 5.4 Guards produce sibling branches

If a transformation is valid only when `p w`, the non-`p` case becomes an explicit branch. Never encode “assume `p`” unless `p` is already a theorem from the parent node.

### 5.5 Exceptions are never deleted

If a reduction either produces the desired structured object or an exceptional object, use an explicit two-way split / escape package. The exception remains on the frontier until separately killed or consumed.

### 5.6 No synthetic global percentage

CRRG must not print “63% solved”, closed-leaf percentages, theorem counts, pin counts, or a weighted sum chosen by an agent.

Trusted reward channels are only:

1. root prize movement (`δ_lo`, `δ_hi`), already produced by `verify.sh`;
2. binary completion of an exact assigned leaf theorem;
3. an exact quantitative improvement *inside a fixed monotone family* (for example a smaller proved class cap, a larger safe radius, or a stronger moment inequality), where the ordering is itself formalized;
4. a new certified decomposition edge, which changes the task graph but is not numerically scored.

This preserves the existing gate’s anti-reward-hacking principle.

---

## 6. Lean API: minimal core

Implement the pilot under the writable soundness subtree first:

```text
ProximityPrize/Squeeze/Soundness/ResearchGraph/
```

Do not modify ArkLib or the frozen Squeeze core while the pilot is in progress.

### 6.1 Proposition-level goals

```lean
namespace ProximityPrize.Squeeze.Soundness.ResearchGraph

structure Goal where
  claim : Prop

abbrev Goal.Proved (G : Goal) : Prop := G.claim

/-- `child` is sufficient to discharge `parent`. -/
structure Edge (parent child : Goal) : Prop where
  discharge : child.claim → parent.claim

namespace Edge

def id (G : Goal) : Edge G G := ⟨id⟩

def trans {A B C : Goal} (ab : Edge A B) (bc : Edge B C) : Edge A C :=
  ⟨fun hC => ab.discharge (bc.discharge hC)⟩

end Edge
```

Direction convention is deliberately **rootward**: `Edge parent child` means “solve child, then parent is solved.”

The `: Prop` on `Edge` is **normative**, not incidental. Lean would infer it from
the single proof-valued field, but that inference is fragile: adding any data
field later would silently move `Edge` into `Type` and change the universe of
every downstream signature mentioning it. A certified edge carries no data by
design — metadata belongs on the candidate record (§8.3).

**Universe discipline (normative).** `Goal` is universe-free: its `claim` is a
`Prop`. Every *index* or *witness* type in the calculus — `BadNode.Witness`,
`Split.Branch`, `WitnessSplit.Branch`, `Frontier.Task` — is `Type u`, not
`Type 0`. A research counterexample is not guaranteed to live in the lowest
universe: any witness that itself carries a type (a family, a code, a
category-like structure) is at least `Type 1`, and a monomorphic calculus could
not host it at all. Sibling nodes of one refinement share a universe; a
`WitnessMap` may cross universes.

The two `trivial` convenience constructors (`Split.trivial`, `Frontier.trivial`)
are the deliberate exception: they are pinned to `Type 0`. A convenience
constructor whose universe nothing pins forces every downstream definition built
from it to become polymorphic, and the level is then unsolvable at the use site.
Anything needing a trivial node at a higher universe writes the structure
instance directly.

Ordinary `Type 0` usage must require no universe annotations anywhere. This is a
testable property, not an aspiration.

### 6.2 Exact finite/dependent splits

```lean
universe u

structure Split (parent : Goal) where
  Branch : Type u
  child : Branch → Goal
  discharge : (∀ i, (child i).claim) → parent.claim
```

A split is not a collection of tasks; it is a proof that the collection of tasks is sufficient.

### 6.3 Counterexample nodes (preferred for structural research)

Proposition-level goals are necessary for retrofitting existing theorems, but new structural decompositions should preferentially use explicit counterexample types.

```lean
universe u v w

structure BadNode where
  Witness : Type u

abbrev BadNode.Closed (N : BadNode) : Prop := N.Witness → False

structure WitnessMap (parent : BadNode.{u}) (child : BadNode.{v}) where
  map : parent.Witness → child.Witness

structure WitnessSplit (parent : BadNode.{u}) where
  Branch : Type v
  child : Branch → BadNode.{w}
  classify : parent.Witness → Σ i, (child i).Witness
```

Generic theorems:

```lean
theorem WitnessMap.closed_parent
    (r : WitnessMap parent child) :
    child.Closed → parent.Closed

theorem WitnessSplit.closed_parent
    (s : WitnessSplit parent) :
    (∀ i, (s.child i).Closed) → parent.Closed
```

This is the strongest correctness shape for research case splits: exhaustiveness is represented by an actual classifier from every parent witness into a branch.

**`Closed` is deliberately not Mathlib's `IsEmpty`.** §2.2 requires the CRRG core
to be dependency-light and to avoid an independent Mathlib-version constraint,
which would otherwise propagate to every downstream consumer. `IsEmpty α` is a
one-field structure wrapping exactly `α → False`, so the two are the same
proposition and every theorem above holds verbatim; only the introduction and
elimination syntax differs. CRRG never needs `Closed` to be found by instance
search — it is always supplied explicitly as a hypothesis — so nothing is lost
by dropping the class. Downstream projects that do depend on Mathlib may bridge
the two with `⟨·⟩` and `IsEmpty.false` in a single line.

### 6.4 Explicit escape package

Semantically this is a two-way `WitnessSplit`, but the name matters operationally:

```lean
structure EscapeMap (parent main escape : BadNode) where
  classify : parent.Witness → main.Witness ⊕ escape.Witness
```

Use it whenever a proof says “either the desired normalization succeeds, or an exceptional algebraic configuration occurs.”

The orchestrator must create one task for `main` and one task for `escape`; the latter cannot disappear into prose.

### 6.5 Guarded transformation helper

A guarded transform must consume both truth values:

```lean
structure GuardedMap (parent pass fail : BadNode) where
  guard : parent.Witness → Bool
  onPass : ∀ w, guard w = true → pass.Witness
  onFail : ∀ w, guard w = false → fail.Witness
```

A generic conversion produces a `WitnessSplit` with two branches.

This is the static analogue of ArkLib’s guarded-verifier discipline.

---

## 7. Root package and live frontier

### 7.1 Root goal

For each active rung, define the exact goal once:

```lean
def target971426 : Goal :=
  ⟨Achievable (971426 / 2097152 : ℚ)⟩
```

Use integer Hamming radius as the identifier. The denominator `2097152` is fixed by the code length and must not be repeated inconsistently across task files.

Recommended helper:

```lean
def radius (d : ℕ) : ℚ := d / 2097152
```

with a frozen/type-linked theorem `radius d = ...` where needed.

### 7.2 Current exact root seam on `soundness`

The live branch already contains the correct two-premise composition theorem in
`ProximityPrize/Squeeze/Soundness/MomentRecovery.lean`:

```lean
def GenericTailThresholdAt (κ d : ℕ) : Prop := ...
def FpMomentBudgetAt (κ d : ℕ) : Prop := ...

theorem achievable_971426_of_fpMomentBudget_genericTail
    (hfp : FpMomentBudgetAt momentKappa 971426)
    (hgen : GenericTailThresholdAt momentKappa 971426) :
    Achievable ((971426 : ℚ) / 2097152)
```

This is the **initial CRRG root interface**.

The live research program also uses the maximal tight-inversion order

```text
k0 = 370796931
```

inside the deeper moment/recovery machinery. This is distinct from the existing
`momentKappa = 1546673`. The former is the largest order satisfying the tight
side-condition `2*k^2 <= directBudget`; the latter is the order appearing in
the landed `MomentRecovery` endpoint. CRRG must not conflate them.

Therefore the initial certified frontier is exactly two leaves:

```text
Root: Achievable (971426 / 2097152)

  ├── FpMomentBudgetAt momentKappa 971426
  └── GenericTailThresholdAt momentKappa 971426
```

with `MomentRecovery.achievable_971426_of_fpMomentBudget_genericTail` as
`closeRoot`.

The current iteration-1132 hard theorem
`H2CompletionQuarticResidualKernelOrStructuralTerminal` is **not** automatically
a CRRG frontier leaf merely because `FRONTIER.md` names it. It becomes a child
only after Lean contains the full source-faithful edge from that theorem,
through the H2 count and rank-free H1/H0 specializations, into one or both of
the two certified leaves above.

### 7.3 Frontier package

```lean
structure Frontier (root : Goal) where
  Task : Type u
  leaf : Task → Goal
  closeRoot : (∀ t, (leaf t).claim) → root.claim
```

A `Frontier root` is the kernel-authoritative statement of “these are all the obligations currently required to close the target.”

For the refreshed pilot:

```lean
inductive Root971426Task
  | fpMomentBudget
  | genericTail

def current971426 : Frontier target971426 where
  Task := Root971426Task
  leaf
    | .fpMomentBudget =>
        ⟨MomentRecovery.FpMomentBudgetAt momentKappa 971426⟩
    | .genericTail =>
        ⟨MomentRecovery.GenericTailThresholdAt momentKappa 971426⟩
  closeRoot := by
    intro h
    exact MomentRecovery.achievable_971426_of_fpMomentBudget_genericTail
      (h .fpMomentBudget) (h .genericTail)
```

**Important:** task count has no reward meaning.

### 7.4 Refinement

Generic, leaf-preserving frontier refinement is **normative**, not deferred. A
refinement must:

- replace one leaf by a single child using an `Edge`;
- replace one leaf by multiple children using a `Split`;
- **preserve all other leaves**;
- derive the new `closeRoot` automatically.

```lean
def Frontier.refineLeaf {root : Goal} (F : Frontier root) (dec : DecidableEq F.Task)
    (t₀ : F.Task) {child : Goal} (e : Edge (F.leaf t₀) child) : Frontier root

def Frontier.splitLeaf {root : Goal} (F : Frontier root) (dec : DecidableEq F.Task)
    (t₀ : F.Task) (s : Split (F.leaf t₀)) : Frontier root

def Frontier.retireLeaf {root : Goal} (F : Frontier root) (dec : DecidableEq F.Task)
    (t₀ : F.Task) (proof : (F.leaf t₀).claim) : Frontier root
```

`splitLeaf`'s new task set is `{t : F.Task // t ≠ t₀} ⊕ s.Branch`: the siblings
survive as the left summand and the coverage proof carried by `s` is
structurally required, which is what makes §12.1 enforceable rather than
advisory.

`retireLeaf` implements §12.3. It demands an actual proof of the retired leaf, so
removing an obligation from the live frontier can never be a bookkeeping edit.

**Do not use `Frontier.compose` for leaf refinement.** It re-roots an entire
frontier through an `Edge` and its result carries only the inner frontier's
leaves; every sibling of the outer frontier is discarded. It is sound but it is
not a refinement operator.

**Decidability is an explicit argument, not an instance.** Instance resolution
runs at `instances` transparency and will not unfold a frontier declared with a
plain `def` — which is exactly how downstream adapters declare theirs — so
`[DecidableEq F.Task]` fails to synthesize on the intended usage. Callers pass
`inferInstanceAs (DecidableEq MyTask)`.

---

## 8. Typed Candidate Graph and Promotion Queue

The certified CRRG must remain brutally literal: every certified edge is a Lean theorem. However, the live research program often depends on a plausible chain of implications before all of those implications have been formalized. CRRG therefore has a second, explicitly non-certified layer: the **Typed Candidate Graph**.

The candidate layer exists to expose formalization debt without pretending that debt has already been paid.

### 8.1 Hard invariant: there are no prose edges inside CRRG

A candidate edge is **not** a sentence such as:

```text
"H2 should feed MomentRecovery"
```

or:

```text
"H2 count -> rank-free H1/H0"
```

Those are research notes and remain outside CRRG.

A CRRG candidate edge must have an **exact Lean proposition** whose proof is currently absent.

For example:

```lean
namespace ResearchGraph.Candidates

def E3Target : Prop :=
  H2CompletionResult →
  DimKerPsi4ResidualBound →
  LandedH2Count →
  MomentRecovery.FpMomentBudgetAt momentKappa 971426

end ResearchGraph.Candidates
```

The declaration above is allowed because it merely defines a proposition. It does not assert that the proposition is true.

Promotion means producing a theorem inhabiting that exact target:

```lean
theorem E3 : ResearchGraph.Candidates.E3Target := by
  ...
```

Only after that theorem passes the ordinary build, axiom audit, and type-link checks may E3 become a certified graph edge.

**Rule:** if an arrow does not have an exact Lean target type, it is not part of CRRG at all.

### 8.2 Candidate edges must expose all composition debt

A syntactically exact proposition can still hide the actual research gap by introducing extra hypotheses casually.

For example, this is informative:

```lean
H2CompletionResult →
DimKerPsi4ResidualBound →
LandedH2Count →
FpMomentBudget
```

but it must be interpreted correctly: `H2CompletionResult` alone does **not** close `FpMomentBudget`. The other hypotheses are separate obligations unless they are already certified ancestors.

CRRG therefore permits two honest encodings.

#### Shape A — explicit multi-parent candidate

```text
Certified A ─┐
Certified B ─┼─> [E3 UNVERIFIED] ─> Parent
Candidate C ─┘
```

The exact proposition consumes every parent explicitly.

#### Shape B — package the entire unresolved source obligation

```lean
structure E3Obligation : Prop where
  hH2    : H2CompletionResult
  hPsi4  : DimKerPsi4ResidualBound
  hCount : LandedH2Count

def E3Target : Prop :=
  E3Obligation →
  MomentRecovery.FpMomentBudgetAt momentKappa 971426
```

Both are acceptable. What is forbidden is describing the edge as "H2 -> FpMomentBudget" while silently relying on untracked side conditions.

### 8.3 Candidate record

A candidate edge should carry machine-readable metadata in addition to its exact proposition.

The record is **not** a single mutable structure with a `status` field. Storing
the target proposition and the status side by side as ordinary fields makes every
illegal transition expressible, and CRRG's whole claim is that illegal
transitions are not expressible. The normative encoding indexes the type by the
sealed proposition and gives each lifecycle state its own type:

```lean
/-- Provenance fixed at seal time, never mutated. -/
structure SealRecord where
  id : String
  sourceIds : List String
  targetId : String
  expectedTheoremName : String
  sealHash : String        -- sha256 of the exact printed target type
  sourceCommit : String
  createdAt : String

/-- DRAFT. Target is a field, because a draft may still change. -/
structure DraftCandidate where
  id : String
  sourceIds : List String
  targetId : String
  expectedTheoremName : String
  targetProp : Prop

/-- SEALED_UNVERIFIED. Target is a *type parameter*: it can no longer change. -/
structure SealedCandidate (targetProp : Prop) where
  record : SealRecord

/-- The terminal states. `certified` and `refuted` are kernel-checked. -/
inductive Outcome (P : Prop)
  | certified (proof : P) (theoremSha : String)
  | refuted (disproof : ¬ P) (reason : String)
  | invalid (reason : String)
  | malformed (reason : String)
  | superseded (bySealId : String) (reason : String)

/-- History: the exact proposition, its provenance, and its final status. -/
structure ResolvedCandidate (P : Prop) where
  sealed : SealedCandidate P
  outcome : Outcome P
```

`CandidateStatus` still exists, but only for **rendering**. It is derived from
the value's type via `Outcome.status`, never stored as mutable state, and
nothing in CRRG accepts a `CandidateStatus` as evidence of anything.

Three properties follow structurally rather than by convention:

- **a sealed target cannot be weakened in place** — `SealedCandidate P` and
  `SealedCandidate Q` are different types (§8.5);
- **promotion requires the exact proposition** — `certified` carries a proof of
  the very `P` the seal is indexed by;
- **a resolved candidate cannot be promoted** — `Outcome` has no transition out
  of it, and `Outcome.status_not_promotable` is a theorem.

**A claimed refutation must carry a disproof.** `refuted` requires `¬ P`.
"The intended route is contradicted, but I have no disproof" is `invalid`, which
makes no claim about `P` at all. Conflating the two would let an agent close a
task by asserting falsity.

The semantic requirements the encoding must satisfy are:

```text
candidate ID
source goal IDs
destination goal ID
exact Lean proposition
expected theorem name
sealed target hash / source commit
status
```

The prose rationale, research motivation, and expected proof mechanism may live beside the record but are not graph semantics.

### 8.4 Candidate lifecycle

Candidate edges have a strict lifecycle:

```text
DRAFT
  ↓ seal exact proposition
SEALED_UNVERIFIED
  ↓ theorem inhabits exact sealed target
CERTIFIED
```

Alternative terminal states:

```text
SEALED_UNVERIFIED
  ├─> INVALID / REFUTED
  ├─> MALFORMED
  └─> SUPERSEDED
```

Definitions:

- **DRAFT** — free research design. May be edited. Carries no graph status or reward.
- **SEALED_UNVERIFIED** — exact proposition fixed and hash-anchored for the attempt. This is a real promotion task.
- **CERTIFIED** — theorem inhabits the exact sealed proposition and passes the graph gate. May enter the trusted CRRG.
- **INVALID / REFUTED** — the candidate proposition or its intended mathematical route is false or contradicted.
- **MALFORMED** — the proposition is type-correct but does not represent the intended composition, for example because a needed premise was omitted or a quantifier is wrong.
- **SUPERSEDED** — a different sealed candidate replaces it. The old exact target remains in history.

A sealed target may never be weakened in place. If the target changes, create a new candidate ID and retain the old one.

This is enforced by the type, not by review: the proposition is a parameter of
`SealedCandidate`, so "changing it" produces a value of a different type rather
than a mutation. The `sealHash` in the seal record covers the complementary
attack of redefining the underlying Lean declaration while keeping its name — the
kernel cannot see that, but the hash printed by `scripts/crrg-seal` does.

### 8.5 Anti-proxy rule for candidate promotion

Once an agent is assigned a sealed candidate, the proposition is immutable for that attempt.

Forbidden:

```text
iteration 1:
  E17Target := hard statement

iteration 4:
  "refactor" E17Target into easier statement

iteration 5:
  prove easier E17Target and report promotion
```

Permitted:

```text
E17Target remains fixed
research discovers missing premise X
E17 is marked MALFORMED
new sealed candidate E23Target includes X explicitly
```

This is the candidate-layer analogue of the frozen Grand Challenge root.

### 8.6 Candidate promotion is objective formalization progress, not prize progress

A transition

```text
E17: SEALED_UNVERIFIED -> CERTIFIED
```

is an objective event:

> a dependency the research program had been relying on informally is now a Lean theorem.

It does **not** mean that the Grand Challenge is a fixed percentage closer to solution. Candidate promotion must not be converted into an aggregate "percent solved" score.

Likewise:

```text
E17: SEALED_UNVERIFIED -> MALFORMED
```

may be highly valuable. It proves that the research blueprint was missing a real obligation.

### 8.7 Certified graph vs typed promotion queue

`CRRG.Report` renders the two separately and provides no operation that merges
them: `QueueReport` and `FrontierReport` are unrelated types, and a
`PromotionQueue` is not a `Frontier`, so a queue entry cannot close a root.

The user-facing or agent-facing state should distinguish them visually and semantically:

```text
CERTIFIED FRONTIER
==================

FpMomentBudget ─────┐
                    ├── Achievable 971426
GenericTail ────────┘


TYPED PROMOTION QUEUE
=====================

[E17 SEALED_UNVERIFIED]
exact Lean proposition: ...
expected theorem: ...
source(s): ...
destination: ...

[E18 SEALED_UNVERIFIED]
exact Lean proposition: ...
...
```

Only the certified frontier can close the root.

The typed promotion queue guides research and formalization, but its edges contribute zero trusted root closure until promoted.

### 8.8 Candidate graph history

Every sealed candidate should be preserved with:

- exact Lean proposition;
- source commit / branch;
- seal hash;
- creation timestamp;
- final status;
- theorem SHA if certified;
- reason if malformed/refuted/superseded.

This history is useful both for research provenance and for measuring whether CRRG is actually reducing repeated decomposition mistakes.

---

## 9. LDB-specific counterexample vocabulary — **downstream adapter only**

> **Boundary warning.** Everything in this section is `proximity-research`
> vocabulary: `Word`, `KBField`, `targetCode`, `listAt`, `radius`, `Achievable`,
> `securityBits`. §2.1 states that CRRG "must never import" any of these, and
> §2.2 requires the core to stay dependency-light. **None of this section may be
> implemented inside the standalone CRRG package.** It specifies declarations
> that belong to the downstream `ResearchGraph` adapter, alongside `Root971426`
> and `Current`, and it is recorded here only because the counterexample
> vocabulary is the long-term semantic model for the LDB program.
>
> The generic machinery this section builds on — `BadNode`, `WitnessMap`,
> `WitnessSplit`, `EscapeMap`, `GuardedMap` — is in CRRG (§6.3–§6.5). The
> LDB-specific instantiation below is not.
>
> If a future reader finds `ListViolation` inside the CRRG package, that is a
> boundary violation and should be moved out, not blessed.

After the proposition-level pilot works, the downstream adapter should introduce an explicit violation object aligned with the existing executable `listAt` API.

```lean
structure ListViolation (d B : ℕ) where
  center : Word KBField targetCode
  family : Finset (Word KBField targetCode)
  inside : ↑family ⊆ listAt KBField targetCode (radius d) center
  tooLarge : B < family.card
```

Then prove an adapter theorem of the form (again, downstream):

```lean
theorem achievable_of_no_listViolation
    (d B : ℕ)
    (hClosed : IsEmpty (ListViolation d B))
    (hSecurity : B * 2 ^ securityBits ≤ Fintype.card KBField) :
    Achievable (radius d)
```

The proof should reuse the current finite-subfamily interpretation of `ListDecodingChallenge`; if it is cleaner to work through ArkLib, use the already-proved bridge plus ArkLib’s `Lambda_le_of_forall_finset_card_le` theorem.

Once this exists, the entire soundness program can be read as normalization of a hypothetical `ListViolation d B` into increasingly rigid counterexample types.

That is the recommended long-term semantic model — for the downstream adapter. CRRG itself only supplies the generic `BadNode`/`WitnessSplit` calculus that this instantiates.

---

## 10. Quantitative partial progress

CRRG deliberately distinguishes **structural progress** from **quantitative progress**.

### 10.1 Structural progress

Examples:

- every violating list has a rank-one or generic witness;
- every full-span residual has `c = 1`, `c = 2`, or `c ≥ 3`;
- every high-density shell either has a bounded cofactor fibre or yields a split-section source.

These are valuable if and only if the split/classifier is Lean-certified.

Reward: the exact split theorem lands. No scalar magnitude.

### 10.2 Quantitative progress

For fixed node families with a mathematically canonical order, expose that order.

Examples:

```lean
ClassCapAt d L
MomentBound d k B
ListBound d B
McaBadGammaBound d B
```

Each family should have an explicit monotonicity theorem stating which parameter direction is stronger.

An agent assigned to such a family may receive local numerical reward only when it proves a strictly stronger parameter under the *same node semantics*.

Never compare unrelated local currencies (e.g. “3 bits of moment slack” versus “one case eliminated”) by a hand-chosen exchange rate.

Both conditions are **structural**, not editorial:

```lean
structure MonotoneFamily (Param : Type u) where
  Stronger : Param → Param → Prop
  claim : Param → Prop
  stronger_refl : ∀ p, Stronger p p
  stronger_trans : ∀ {a b c}, Stronger a b → Stronger b c → Stronger a c
  /-- The monotonicity theorem, as a field: a family cannot exist without it. -/
  monotone : ∀ {a b}, Stronger a b → claim a → claim b

def MonotoneFamily.StrictlyStronger (F : MonotoneFamily Param) (a b : Param) : Prop :=
  F.Stronger a b ∧ ¬ F.Stronger b a

/-- The only numerical reward CRRG recognises. -/
structure Progress (F : MonotoneFamily Param) (old new : Param) where
  improvement : F.StrictlyStronger new old
  proof : F.claim new
```

- **The monotonicity theorem is a field**, so declaring a family without proving
  it is impossible.
- **`Progress` is indexed by the family**, so progress in one family is not
  progress in another — even when both are parameterised by `ℕ` and both improve
  the same numerals. There is deliberately **no** operation that adds, averages,
  or exchanges progress across families. The absence of that operation *is* the
  prohibition on exchange rates.
- **`Progress.implies_old` is a theorem**: a proof at a strictly stronger
  parameter still proves the old parameter's claim. An agent can never be
  rewarded for an "improvement" that abandons what was already established.
- `StrictlyStronger` is irreflexive, so re-proving the same parameter earns
  nothing.

`Stronger` requires reflexivity and transitivity. Without them "strictly
stronger" does not compose and a chain of improvements cannot be certified as a
single one.

**Declaration idiom.** Declare a family with `abbrev`, not `def`. `Stronger` and
`claim` are structure fields, so `myFamily.Stronger a b` reduces to the intended
relation only when `myFamily` is reducible; behind a plain `def`, `omega` and
`decide` see an opaque atom and fail. This is the same projection-reducibility
hazard noted for frontiers in §7.4, and it applies wherever a `Type`- or
`Prop`-valued field is projected in user code.

### 10.3 Optional certified root-bound evaluator

A later phase may attach fallback bounds to every branch and compose them by exact `sum`, `max`, or product lemmas, producing a valid root upper bound even before the threshold is reached.

This would yield a dense scalar signal such as an actual proved `Lambda ≤ B_current`.

Do **not** implement this until the decomposition naturally provides valid fallback bounds. A fake scalar is worse than binary tasks.

---

## 11. Agent task contract

Every research agent receives one exact task file containing:

1. **Root lineage:** the declaration path from the live Grand Challenge target to this leaf.
2. **Exact target type:** a `theorem` signature or `example` that must compile unchanged.
3. **Allowed imports / writable files.**
4. **Sibling assumptions:** only previously proved theorem constants, never prose facts.
5. **Success condition:** kernel compilation + axiom audit + exact type-link.
6. **Failure output:** mathematical counterexample, impossibility theorem, or proposed split — but a proposed split is not promoted until its coverage theorem compiles.

The local reward is binary:

```text
OPEN -> CLOSED
```

or, for a monotone parameterized leaf:

```text
proved parameter p_old -> strictly stronger p_new
```

This is enough to give an agent a correct reward signal without inventing a global percentage.

---

## 12. Graph-change protocol

A graph change is a mathematical event, not project-management metadata.

### 12.1 Valid refinement

To replace leaf `L` by children `C_i`, the same commit must contain:

```lean
split_L : (∀ i, C_i) → L
```

or preferably a witness classifier proving exhaustive coverage.

Only after that theorem builds may the orchestrator assign `C_i` as independent tasks.

### 12.2 Invalid refinement

Reject any change that does only one of:

- adds children in a state file;
- proves children for a convenient subclass without a coverage theorem;
- introduces a hypothesis that is not derived from the parent;
- drops a guard because the downstream object no longer carries the checked data;
- replaces a false historical premise by a nearby plausible premise without rebuilding the parent edge;
- measures “fraction of cases” without a certified measure/partition theorem.

### 12.3 Retirement

A historical route can remain in source, but it must be removed from the **live frontier** when:

- an assumption is refuted;
- a stronger route supersedes it;
- its root edge no longer belongs to the selected target plan.

This exactly addresses the current `ClassCapAt 971426 176342654` situation: the implication may remain a true theorem, but the false premise means it is not a live frontier leaf.

---

## 13. File layout for the pilot

```text
ProximityPrize/Squeeze/Soundness/ResearchGraph/
  Basic.lean                 -- Goal, Edge, Split, BadNode, WitnessMap/Split, EscapeMap
  ListViolation.lean         -- optional in phase 2
  Root971426.lean            -- exact root
  Current.lean               -- two-leaf live Frontier target971426
  Pins.lean                  -- exact #check/example type-links for graph declarations
  Tasks/
    T000_FpMomentBudget.lean
    T001_GenericTail.lean
    ...                      -- only after certified refinements

scripts/squeeze/
  verify_research_graph.sh
  extract_research_graph_axioms.lean

state/research_graph/
  CURRENT.md                 -- human-readable rendering; NOT authority
  history/                   -- old frontier descriptions
```

No frozen-file changes are required for the pilot.

---

## 14. Verification integration

### 14.1 Keep `verify.sh` prize output unchanged

Do not add intermediate scores to its `TARGET` section.

### 14.2 Add a separate graph gate

`verify_research_graph.sh` should:

1. build `ResearchGraph.Current` and every registered closed-task module;
2. reject banned constructs under the same policy as the main gate;
3. run transitive `collectAxioms` on:
   - the live `Frontier.closeRoot` theorem/package;
   - every certified edge/split used by the live frontier;
   - every closed leaf theorem;
4. type-link the root exactly to `Achievable (971426 / 2097152)`;
5. type-link each task theorem to the exact leaf declaration;
6. print task identifiers with only `OPEN` / `CLOSED` / `INVALID` states;
7. print no aggregate count or percentage.

Items 2, 6 and 7 have concrete implementations rather than being left to
reviewer discipline.

**Item 2 — banned constructs.** `scripts/crrg-banned` scans Lean sources for
escape hatches that keep a declaration axiom-clean while defeating the trust
model: `sorry`, `native_decide` (trusts the compiler, not the kernel), `axiom`,
`unsafe`, `partial`, and `@[implemented_by]` / `@[extern]` (which replace a
verified definition at runtime). Lean comments are stripped before matching, so a
doc-comment may quote this list without tripping the scan. This is complementary
to the axiom audit, which catches only what reaches the kernel.

**Items 6 and 7 — reporting.** `CRRG.Report` provides `TaskStatus` with exactly
three constructors and `FrontierReport`, whose `render` emits **one line per
task and nothing else**:

```lean
theorem FrontierReport.render_length (r : FrontierReport root) :
    r.render.length = r.tasks.length
```

A summary line, a count, or a percentage would make the output longer than the
task list, so surfacing one requires breaking this theorem. `FrontierReport` has
no aggregate field to hold such a value, and `crrg-banned` additionally rejects
identifiers such as `percentage`, `progressScore` and `completionRatio`.

Task count remains available to the orchestrator as `FrontierReport.taskCount`,
because iterating over tasks is legitimate. It is deliberately not part of
`render`: §7.3 states that task count has no reward meaning.

The orchestrator may use the individual status of the task it assigned as the reward signal.

### 14.3 Graph integrity

`Current.lean` is the authority for the live graph. `state/research_graph/CURRENT.md` is generated commentary.

If the state rendering and Lean graph disagree, Lean wins.

---

## 15. Implementation Plan — validation before Soundness control

CRRG should be validated in stages. The objective is to separate two hypotheses:

1. **CRRG correctness:** the graph calculus faithfully records exact mathematical dependencies, refinements, guards, exceptional branches, and root lineage.
2. **CRRG research utility:** giving agents certified local obligations and graph mutations improves autonomous research rather than merely reorganizing proofs.

The first hypothesis should be tested on a controlled real problem before CRRG is allowed to direct the live LDB Soundness program.

### Stage A — synthetic unit tests

Use tiny Lean examples to validate each CRRG primitive in isolation:

- direct `Edge` composition;
- exhaustive `Split`;
- witness-level `WitnessSplit`;
- guarded refinement where the failed guard remains an explicit child;
- escape refinement where the exceptional event remains explicit;
- route retirement without deleting historical lineage;
- DAG reuse where one theorem discharges multiple parents;
- negative tests for missing branches and weakened child statements.

These tests establish implementation correctness only. They are not evidence that CRRG improves research.

### Stage B — Yukon / better.codes retrospective reconstruction

Use the already solved Yukon lower-bound proof as the first integration test.

The current public endpoint is:

```lean
ProtocolClaim 6399 307083 1048576
```

The known proof already exposes a nontrivial modular chain of the right shape:

```text
BCHKSPolynomialAlignment6399
        ↓
AffineLineAlignmentBound
        ↓
MCA error bound
        +
Johnson/list bound
        +
field-capacity arithmetic
        ↓
certifiedGammaError ≤ 2^-128
        ↓
ProtocolClaim 6399 307083 1048576
```

Build a CRRG for this completed proof **retrospectively**.

The acceptance condition is not merely that the final theorem compiles. CRRG must reconstruct the known endpoint while preserving:

- every exact premise;
- every quantitative side condition;
- the MCA/list decomposition;
- the field-capacity arithmetic;
- the existing theorem directions;
- the exact final `ProtocolClaim`.

Because the proof is already known, any disagreement between the reconstructed graph and the existing proof is diagnosable. This makes Yukon a substantially safer integration target than live Soundness for validating CRRG itself.

### Stage C — deliberately damaged Yukon proof

After retrospective reconstruction succeeds, create a private test branch or isolated test harness in which selected intermediate proof edges are removed from the live CRRG frontier while the known completed proof remains available as ground truth outside the agent context.

Before dispatch, convert every removed edge into a **SEALED_UNVERIFIED typed candidate**. Each promotion task therefore has an exact Lean proposition known to be achievable from the completed reference proof, but the agent does not receive the proof.

Run several controlled experiments.

#### C1. Missing direct edge

Expose an exact intermediate goal such as an alignment bound while withholding the existing theorem that proves it.

The agent may:

- prove the leaf directly;
- refine it through a certified exhaustive decomposition;
- fail and leave the graph unchanged.

It may **not** weaken the leaf, replace it by a proxy, or add an uncertified assumption.

#### C2. Known exhaustive split

Choose an existing proof segment whose correct case split is already known. Present only the parent obligation and require the agent to recover or improve the split.

CRRG must reject:

- incomplete case lists;
- dropped exceptional branches;
- one-directional implications presented as equivalences;
- guards that disappear downstream.

#### C3. Route refutation

Expose a sufficient route whose antecedent can be shown false or whose proposed refinement can be falsified.

The expected CRRG behavior is:

- retain the historical valid implication;
- mark the route retired for the live frontier;
- preserve the root;
- require a replacement live path before changing the frontier.

This stage is the main adversarial test of CRRG's anti-reward-hacking semantics.

In addition, measure the **candidate-promotion cost**:

- median iterations from `SEALED_UNVERIFIED` to `CERTIFIED`;
- Lean lines / build attempts per promoted edge;
- number of candidates discovered to be malformed despite plausible prose descriptions;
- number of promotions requiring the candidate to be superseded by a more accurate exact type;
- number of candidate targets weakened or rewritten attempts rejected by the seal mechanism.

This measurement directly answers the structural concern that the Soundness certified graph may remain at two root leaves for many iterations. If even a known-correct Yukon edge takes dozens of iterations to promote, edge certification itself is an engineering bottleneck and CRRG tooling should be improved before deep Soundness deployment.

### Stage D — real forward Yukon research

Once the retrospective and damaged-proof tests pass, use CRRG on an actual attempt to improve the Yukon lower-bound result beyond the current endpoint.

Run CRRG-mediated research against a comparable ordinary autoresearch baseline where practical.

Do **not** evaluate CRRG only by final score movement. Record at least:

- proxy-goal excursions;
- invalid or non-exhaustive decompositions proposed;
- successful lemmas with no downstream consumer;
- iterations spent rediscovering context already represented by the graph;
- certified graph mutations per research iteration;
- route retirements caused by real counterexamples;
- final benchmark movement, if any.

This stage tests whether CRRG improves research behavior on a real but bounded problem.

### Stage E — Soundness shadow mode in parallel

CRRG should enter the live `soundness` program in **shadow mode** as soon as Stages B and C are credible; it does not need to wait for Yukon forward research to finish.

During shadow mode:

```text
GPT-5.6 Sol live Soundness research
        │
        ├── existing FRONTIER / state discipline
        │
        └── CRRG observer
              ├── accepts certified reductions
              ├── rejects invalid refinements
              ├── records route retirement
              └── maintains an exact root lineage
```

CRRG does **not** schedule the Soundness agent during this stage.

The initial certified Soundness frontier remains:

```text
Achievable (971426 / 2097152)
        ↑
MomentRecovery.achievable_971426_of_fpMomentBudget_genericTail
       / \
      /   \
FpMomentBudgetAt momentKappa 971426
GenericTailThresholdAt momentKappa 971426
```

The deeper iteration-1132 research blueprint remains human/executor state until each proposed child has an actual Lean edge into this certified frontier.

Run shadow mode across a meaningful sample of genuine Soundness iterations. The review question is:

> Did CRRG correctly distinguish iterations that changed the certified proof state from iterations that only produced infrastructure, diagnostics, proxy theorems, or renamed open premises?

Any mismatch is investigated before CRRG gains scheduling authority.

### Stage F — CRRG-directed Soundness

Promote CRRG from observer to scheduler only when:

- Yukon retrospective reconstruction passes;
- deliberate damaged-proof tests pass;
- shadow mode shows that CRRG tracks live Soundness proof-state changes correctly;
- no graph mutation can alter the root or silently weaken a frontier leaf;
- route retirement and exceptional branches have survived real use.

At that point, the Soundness dispatcher chooses among exact CRRG leaves rather than prose-only frontier descriptions.

Each dispatched task includes:

- exact Lean theorem signature;
- complete root lineage;
- parent/refinement theorem;
- downstream consumer;
- current guards/escape branches;
- prohibition on replacing the task with an easier proxy.

The scheduler may reprioritize leaves freely, but mathematical graph mutations remain kernel-gated.

### Stage G — compare research regimes

After CRRG-directed Soundness has enough runtime, compare three regimes:

```text
1. ordinary autonomous research
2. CRRG shadow observation
3. CRRG-directed research
```

Useful evaluation dimensions include:

- reward movement;
- number of invalid target substitutions;
- number of conditional wrappers that merely introduce a new open premise;
- repeated rediscovery of already killed mechanisms;
- depth and breadth of certified frontier;
- frequency of meaningful graph compression;
- rate of certified route retirement;
- Lean effort spent on artifacts with no path to the root.

This comparison should determine whether CRRG is only an audit system or a genuinely better autonomous-research substrate.

### Why Yukon precedes Soundness control

Yukon is the preferred integration test because it is:

- a real machine-checked research benchmark rather than an artificial theorem;
- substantially smaller than the live Soundness program;
- modular enough to exercise genuine composition;
- already solved at the current endpoint, providing ground truth;
- complicated enough for agents to make the same classes of decomposition mistakes CRRG is meant to prevent.

Soundness remains the principal target and the strongest test of the research thesis, but it should not also carry the burden of debugging the CRRG semantics for the first time.

In short:

```text
Synthetic Lean tests
        ↓
Yukon retrospective reconstruction
        ↓
Yukon deliberately damaged proof
        ↓
Yukon forward research ─────────────┐
                                    │
Soundness CRRG shadow mode ─────────┤  parallel
                                    │
        ↓ once trusted              │
CRRG-directed Soundness
        ↓
A/B-style research-regime review
```

The Yukon program is the **integration test**.  
The live LDB Soundness program is the **deployment target**.

---

## 16. Migration plan from the live `soundness` branch

### Phase 0 — authority and branch policy

For CRRG work, use:

1. `state/ledger.json` for the shipped `delta_lo`;
2. the head of `state/soundness/FRONTIER.md` for the live research obligation;
3. the current-rung re-derivation in `state/SQUEEZE_SHARED.md` for rung/pin semantics;
4. compiled Lean theorem types as the only authority for graph edges.

`merger` is historical for this pilot. Do not read it to determine the live
Soundness frontier.

The existing Disprove side is left exactly as-is by CRRG. Its frozen upper
bound and existing graph/ledger role remain untouched.

### Phase 1 — standalone CRRG infrastructure

In the standalone CRRG repository, implement and test the generic core (`Goal`, `Edge`, `Split`, witness refinements, guards, escapes, frontier, typed candidates, sealing/promotion, and audit tooling).

Then, in a local downstream branch of `proximity-research`, create only `Root971426.lean`, `Current.lean`, project-specific candidate/task declarations, and the thin graph-gate wrapper.

No research theorem changes. No `Seed.lean` changes.

Acceptance test: `Current.closeRoot` is literally implemented by

```lean
MomentRecovery.achievable_971426_of_fpMomentBudget_genericTail
```

and therefore proves the exact target from exactly these two leaves:

```lean
FpMomentBudgetAt momentKappa 971426
GenericTailThresholdAt momentKappa 971426
```

### Phase 2 — freeze the root denominator before decomposition

The iteration-1132 executor policy freezes the entire remaining unconditional
obligation and rejects success-by-renaming. CRRG should encode the same
discipline mechanically.

Create an immutable root-lineage declaration recording:

```text
target radius        = 971426
landed final leaves  = FpMomentBudgetAt momentKappa 971426
                       GenericTailThresholdAt momentKappa 971426
research order k0    = 370796931
```

`k0` is metadata for the deeper proof route, not a replacement for
`momentKappa` in the landed root theorem.

No child theorem is allowed to redefine the denominator of “remaining work.”
A child either discharges/refines an existing leaf, or it is merely research
state.

### Phase 3 — ingest only landed source-faithful reductions

Walk downward from the two certified root leaves.

The current human blueprint is approximately:

```text
failed maximal-order moment shell at d=971426
  -> literal H0/H1/H2 completion source
  -> canonical cubic conductor / apolar defect
  -> one production theorem resolving rank, pure, exact-lift cases
  -> rank-free H1/H0 specializations
  -> FpMomentBudgetAt + GenericTailThresholdAt
  -> Achievable(971426/2^21)
```

Do **not** encode that prose graph wholesale.

For each arrow:

1. locate or create the exact Lean theorem;
2. quote its full type;
3. prove all side conditions from the parent;
4. preserve every exceptional branch;
5. only then refine the CRRG leaf.

The current named hard theorem
`H2CompletionQuarticResidualKernelOrStructuralTerminal` should be treated as a
candidate refinement target, not yet as trusted graph structure. Its promotion
criterion is an end-to-end Lean edge reaching the landed H2 count and the
rank-free H1/H0 consumers with no new open hypothesis.

### Phase 4 — make the executor consume exact CRRG leaves

The existing Soundness policy says successful infrastructure and conditional
hygiene do not count, and it prefers failed end-to-end attempts over successful
wrappers around new open premises. Preserve this.

An agent dispatch contains:

- the exact current leaf theorem;
- its complete root lineage;
- the frozen parent obligation;
- the required downstream consumer;
- a prohibition on replacing the leaf with a strictly easier proxy.

If an attempted theorem lands only partially, it can change the live graph only
when a certified refinement theorem proves the surviving branches. The
executor's heuristic “10–20% of the whole obligation” rule may remain a
scheduling policy, but it is not a kernel score.

### Phase 5 — explicit LDB counterexample normalization

Introduce `ListViolation d B` and progressively migrate structural splits to
witness-level classifiers. This is where the architecture becomes maximally
robust against missing cases.

### Phase 6 — MCA

Reuse the same core calculus for `mca-merger`.

Define an MCA bad-witness node mirroring the existing `MCA_Broken` vocabulary:

```lean
structure MCAViolation (d B : ℕ) where
  f1 f2 : Word KBField targetCode
  gammas : Finset KBField
  bad : ∀ γ ∈ gammas, isMCABad ... (radius d) f1 f2 γ
  tooLarge : B < gammas.card
```

Then add an adapter from `IsEmpty (MCAViolation d B)` plus the security budget to `MCA_Achievable (radius d)`.

LDB/MCA may share the generic `Goal`/`BadNode`/composition core once the private pilot stabilizes.

---

## 17. Relationship to ArkLib upstream

Do not upstream CRRG in its initial form.

After it works on the private LDB tree, consider extracting only the truly generic static reduction calculus (`Goal`, witness classification, guarded/escape split, frontier composition) into ArkLib if ArkLib maintainers see value in a noninteractive proof-decomposition layer.

The ArkLib precedent suggests the right upstream threshold: generic abstractions move only after concrete protocol developments prove the interface is reusable.

---

## 18. Acceptance criteria for v0.6

The pilot is successful if all of the following hold:

0. CRRG builds as an independent standalone Lean repository and imports no `ProximityPrize`, ArkLib application mathematics, Reed–Solomon-specific code, or `proximity-research` modules.
0a. `proximity-research` consumes CRRG as a pinned dependency; it does not contain a second copy of CRRG core semantics.
0b. Local sibling-checkout development and pinned-SHA live integration both build successfully.

1. `ResearchGraph.Current` has the exact root `Achievable (971426/2097152)`.
2. `Current.closeRoot` is type-linked directly to `MomentRecovery.achievable_971426_of_fpMomentBudget_genericTail`.
3. The initial live frontier contains exactly the two landed leaves `FpMomentBudgetAt momentKappa 971426` and `GenericTailThresholdAt momentKappa 971426`.
4. The graph records `k0 = 370796931` only as deeper-route metadata / a certified numeric fact and never substitutes it for `momentKappa` in the existing endpoint theorem.
5. A sample leaf can be refined into two children only by supplying a compiled coverage theorem.
6. A sample guarded refinement visibly retains the guard-failure branch.
7. A sample escape refinement visibly retains the exceptional branch.
8. The graph gate rejects a deliberately weakened child statement / missing branch in a negative test.
9. The main prize gate output is unchanged.
10. No aggregate “progress percentage” is emitted.
11. The Disprove side is unchanged.
12. Every candidate edge in the promotion queue has an exact compilable Lean proposition; prose-only arrows are rejected as non-CRRG state.
13. A sealed candidate target cannot be weakened in place; changing its proposition creates a new candidate ID and preserves the old target historically.
14. Candidate promotion requires a theorem inhabiting the exact sealed proposition plus the ordinary axiom/type-link gate.
15. Yukon damaged-proof tests measure candidate-promotion cost before CRRG is allowed to direct live Soundness.
16. An agent can be assigned one exact leaf or sealed candidate and receive a correct binary reward from Lean without needing the full research history in context.

---

## 19. Design summary

CRRG should make this transformation:

```text
TODAY
Grand Challenge target
    |
    |  human/state-file context
    v
huge research tree
    |
    +-- hundreds of useful but weakly scored steps
    +-- historical/superseded routes
    +-- informal case coverage risks
```

into:

```text
CRRG
Exact Grand Challenge target
    |
    | kernel Edge / Split / WitnessSplit
    v
Certified live frontier
    |
    +-- exact leaf A  -> agent gets binary theorem target
    +-- exact leaf B  -> agent gets binary theorem target
    +-- escape leaf C -> cannot be silently dropped
    +-- guarded leaf D -> failure branch remains explicit

all leaves CLOSED
    |
    | Frontier.closeRoot
    v
Achievable(d/n)
    |
    | existing ArkLibBridge
    v
ArkLib Grand Challenge witness
```

The main conceptual shift is:

> **Partial success is not a percentage. Partial success is a theorem that either closes an exact live obligation or replaces it with a kernel-certified exhaustive refinement.**

That gives agents a dense, correct local reward while preserving the only global reward that matters: movement of the actual Grand Challenge boundary.

---

## 20. Source map used for this spec

### ArkLib (inspected at commit `14a4b351d154cacd7b01ff58bf505c1572112098`)

- `ArkLib/OracleReduction/Basic.lean`
- `ArkLib/OracleReduction/Security/Basic.lean`
- `ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean`
- `ArkLib/OracleReduction/Composition/Sequential/General.lean`
- `ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean`
- `ArkLib/Data/CodingTheory/ListDecodability.lean`
- `ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean`
- `docs/wiki/repo-map.md`
- `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`

### `Barnadrot/proximity-research`

**Live Soundness authority (`soundness` branch):**
- `ProximityPrize/Squeeze/Soundness/MomentRecovery.lean`
- `ProximityPrize/Squeeze/Soundness/MomentLadder.lean`
- `ProximityPrize/Squeeze/Soundness/TightInversion.lean`
- `ProximityPrize/Squeeze/Soundness/GradedMoment.lean`
- `ProximityPrize/Squeeze/Soundness/NumericClose.lean`
- `scripts/squeeze/soundness_program.md`
- `state/soundness/FRONTIER.md`
- `state/SQUEEZE_SHARED.md`

**Stable/root interfaces carried from the existing repository design:**
- `ProximityPrize/Squeeze/Invariant.lean`
- `ProximityPrize/Squeeze/ArkLibBridge.lean`
- `scripts/squeeze/verify.sh`

**Historical/reference-only for this revision:**
- `merger` branch soundness state (not used to choose the live frontier)
- existing Disprove side (kept unchanged)
- `mca-merger: ProximityPrize/Squeeze/MCAInvariant.lean`

