import CRRG
import Test.Support.ExpectFailure

/-!
# Synthetic test: a toy research programme end to end

Everything above tests one primitive in isolation. This module assembles them
into the *shape* of a real reduction programme and drives it through a full
lifecycle, so that the pieces are exercised against each other rather than only
against themselves.

**This is not the Yukon reconstruction (Stage B) and imports nothing from any
research repository.** It is a self-contained caricature that reproduces the
structural features the real programme has:

- a rational-radius root of the form `Achievable (d / D)` with a frozen
  denominator, using Lean core's `Rat`;

Note how ℚ is used. The root *statement* names a rational radius, exactly as the
live root names `Achievable (971426 / 2097152 : ℚ)`, but every side condition is
ℕ-indexed — which is also true of the real programme, whose two landed leaves are
`FpMomentBudgetAt momentKappa 971426` and `GenericTailThresholdAt momentKappa
971426`. That split matters practically: Lean core's `Rat` division does not
reduce in the kernel, so a rational *inequality* is not provable without
Mathlib's order lemmas, whereas a rational *identity* like `radius d = d / 4096`
is `rfl`. CRRG never needs to prove a rational inequality; the mathematics lives
downstream.
- a two-premise composition theorem at the root seam, matching §7.2's
  `achievable_971426_of_fpMomentBudget_genericTail`;
- a monotone parameterized family with an explicit monotonicity theorem (§10.2);
- a counterexample node refined by a guard, with the guard-failure branch alive;
- an escape refinement whose exceptional branch stays on the frontier;
- a candidate edge carrying real composition debt, sealed and then promoted;
- a leaf refined by a certified split, and a route retired by proof.

The arithmetic is deliberately trivial. What is under test is that CRRG's
primitives compose into a coherent programme, and that the dishonest moves at
each stage are rejected.
-/

open CRRG

namespace ToyResearch

/-! ## The frozen root.

A rational radius with a fixed denominator, mirroring §7.1's `radius d = d / 2097152`
and its warning that the denominator "must not be repeated inconsistently across
task files". Here the denominator exists in exactly one place. -/

/-- The frozen denominator. Defined once; never restated. -/
def denom : Nat := 4096

/-- Integer Hamming radius as a rational. -/
def radius (d : Nat) : Rat := (d : Rat) / (denom : Rat)

/-- The frozen denominator is stated once and proved once. -/
theorem radius_def (d : Nat) : radius d = (d : Rat) / 4096 := rfl

/-- Toy stand-in for the prize predicate, at a rational radius. -/
def Achievable (r : Rat) : Prop :=
  ∃ d : Nat, r = radius d ∧ 2 * d ≤ denom ∧ d ≤ denom

/-- The frozen root: the target rung of the toy programme. -/
def target1900 : Goal := ⟨Achievable (radius 1900)⟩

/-! ## The root seam: a two-premise composition theorem.

Structurally identical to the live seam in §7.2 — two landed premises and one
theorem combining them into the root. -/

/-- Toy stand-in for `FpMomentBudgetAt`. -/
def MomentBudgetAt (d : Nat) : Prop := 2 * d ≤ denom

/-- Toy stand-in for `GenericTailThresholdAt`. -/
def TailThresholdAt (d : Nat) : Prop := d ≤ denom

/-- The composition theorem at the root seam. Both premises are consumed, and
    neither alone suffices. -/
theorem achievable_of_budget_and_tail
    (hmom : MomentBudgetAt 1900) (htail : TailThresholdAt 1900) :
    Achievable (radius 1900) :=
  ⟨1900, rfl, hmom, htail⟩

/-! ## The live frontier: exactly the two landed leaves. -/

inductive RootTask | momentBudget | tailThreshold
  deriving DecidableEq

def current1900 : Frontier target1900 where
  Task := RootTask
  leaf
    | .momentBudget => ⟨MomentBudgetAt 1900⟩
    | .tailThreshold => ⟨TailThresholdAt 1900⟩
  closeRoot h := achievable_of_budget_and_tail (h .momentBudget) (h .tailThreshold)

def currentDec : DecidableEq current1900.Task := inferInstanceAs (DecidableEq RootTask)

-- Type-link the root exactly to the project target (Spec 14.2 item 4).
example : True := current1900.rootIs (P := Achievable (radius 1900)) rfl

-- Type-link each leaf exactly to its declaration (Spec 14.2 item 5).
example : True := current1900.leafIs (P := MomentBudgetAt 1900) .momentBudget rfl
example : True := current1900.leafIs (P := TailThresholdAt 1900) .tailThreshold rfl

/- Negative: the root type-link must be exact. A different radius is a different
root, even if numerically close. -/
#expect_failure
example : True := current1900.rootIs (P := Achievable (radius 1901)) rfl

/- Negative: leaves may not be swapped. -/
#expect_failure
example : True := current1900.leafIs (P := TailThresholdAt 1900) .momentBudget rfl

/-! ## Closing the root, once both leaves are discharged. -/

-- NB the `show`. `MomentBudgetAt` is a plain `def`, as a real adapter's
-- predicates are, so instance search cannot see through it to find
-- `Decidable`. Restating the goal in its unfolded form fixes that; the kernel
-- then reduces `denom` without difficulty. See Spec §6.6.
theorem momentBudget1900 : MomentBudgetAt 1900 := by
  show 2 * 1900 ≤ denom
  decide

theorem tailThreshold1900 : TailThresholdAt 1900 := by
  show 1900 ≤ denom
  decide

example : target1900.Proved :=
  current1900.closeRoot fun
    | .momentBudget => momentBudget1900
    | .tailThreshold => tailThreshold1900

/-! ## Quantitative progress on a monotone family (§10.2).

A tail-threshold family with the monotonicity theorem supplied as a field. -/

/-- A **larger** radius is the stronger claim, mirroring `achievable_antitone`:
    establishing the property further out subsumes establishing it nearer in. -/
abbrev tailFamily : MonotoneFamily Nat where
  Stronger a b := b ≤ a
  claim d := TailThresholdAt d
  stronger_refl _ := Nat.le_refl _
  stronger_trans hab hbc := Nat.le_trans hbc hab
  monotone hab ha := Nat.le_trans hab ha

theorem tail2048 : tailFamily.claim 2048 := by
  show 2048 ≤ denom
  decide

/-- A certified improvement from radius 1900 out to 2048, same node semantics. -/
def tighten : Progress tailFamily 1900 2048 where
  improvement := ⟨by omega, by omega⟩
  proof := tail2048

-- The improvement does not abandon the original claim.
example : TailThresholdAt 1900 := tighten.implies_old

/- Negative: retreating to a smaller radius is a weaker claim, not progress. -/
#expect_failure
def loosen : Progress tailFamily 2048 1900 where
  improvement := ⟨by omega, by omega⟩
  proof := tailThreshold1900

/-! ## A counterexample node, refined by a guard.

The parent is "a violating configuration exists". The guard splits on whether
the configuration is dense; **both** sides remain live obligations. -/

structure Config where
  weight : Nat
  span : Nat

abbrev violations : BadNode := ⟨{ c : Config // c.weight ≤ 1900 }⟩
abbrev denseCase : BadNode := ⟨{ c : Config // c.weight ≤ 1900 ∧ 100 ≤ c.span }⟩
abbrev sparseCase : BadNode := ⟨{ c : Config // c.weight ≤ 1900 ∧ c.span < 100 }⟩

def densityGuard : GuardedMap violations denseCase sparseCase where
  guard c := decide (100 ≤ c.val.span)
  onPass c h := ⟨c.val, c.property, of_decide_eq_true h⟩
  onFail c h := ⟨c.val, c.property, Nat.not_le.mp (of_decide_eq_false h)⟩

-- Both branches are required. The guard-failure branch cannot be dropped.
example (hd : denseCase.Closed) (hs : sparseCase.Closed) : violations.Closed :=
  densityGuard.closed_parent hd hs

/- Negative: closing only the dense case does not close the parent. This is the
mistake §12.2 calls "drops a guard because the downstream object no longer
carries the checked data". -/
#expect_failure
example (hd : denseCase.Closed) : violations.Closed :=
  densityGuard.closed_parent hd

/-! ## An escape refinement: normalisation succeeds, or an exceptional
configuration occurs. The exception stays on the frontier. -/

abbrev normalised : BadNode := ⟨{ c : Config // c.weight ≤ 1900 ∧ c.span ≠ 0 }⟩
abbrev degenerate : BadNode := ⟨{ c : Config // c.weight ≤ 1900 ∧ c.span = 0 }⟩

def normalise : EscapeMap violations normalised degenerate where
  classify := fun (c : { c : Config // c.weight ≤ 1900 }) =>
    if h : c.val.span = 0 then
      Sum.inr ⟨c.val, c.property, h⟩
    else
      Sum.inl ⟨c.val, c.property, h⟩

example (hn : normalised.Closed) (hd : degenerate.Closed) : violations.Closed :=
  normalise.closed_parent hn hd

/- Negative: the exceptional branch cannot be silently dropped (§5.5). -/
#expect_failure
example (hn : normalised.Closed) : violations.Closed :=
  normalise.closed_parent hn

/-! ## A candidate edge carrying real composition debt (§8.2).

The research note is "the dense case feeds the moment budget". Stated that way it
is a prose arrow. As a CRRG candidate it must name every premise it consumes. -/

def e001Debt : CompositionDebt where
  premises := [denseCase.Closed, sparseCase.Closed, TailThresholdAt 1900]
  conclusion := MomentBudgetAt 1900

def e001Draft : DraftCandidate where
  id := "E001"
  sourceIds := ["denseCase", "sparseCase", "tailThreshold"]
  targetId := "momentBudget"
  expectedTheoremName := "ToyResearch.e001"
  targetProp := e001Debt.shapeA

def e001Sealed : SealedCandidate e001Draft.targetProp :=
  e001Draft.seal "toy-seal-hash" "8b521ed" "2026-08-25T00:00:00Z"

-- The sealed candidate is the promotable state; it closes nothing on its own.
example : e001Sealed.status = .sealedUnverified := rfl
example : e001Sealed.status.isPromotable = true := rfl

/-- The promotion: a theorem inhabiting the exact sealed proposition. -/
theorem e001 : e001Debt.shapeA := by
  intro _hdense _hsparse _htail
  exact momentBudget1900

def e001Promoted : ResolvedCandidate e001Draft.targetProp :=
  e001Sealed.promote e001 "toy-theorem-sha"

example : e001Promoted.status = .certified := rfl
example : e001Debt.shapeA := e001Promoted.certified_sound rfl

-- Shape A and Shape B are the same obligation (§8.2).
example : e001Debt.shapeA ↔ e001Debt.shapeB := e001Debt.shapeA_iff_shapeB

/- Negative: a candidate that names only one premise is a different, stronger
claim, and the honest proof does not inhabit it. This is exactly the "H2 ->
FpMomentBudget while silently relying on side conditions" failure. -/
#expect_failure
theorem e001Dishonest :
    (CompositionDebt.mk [denseCase.Closed] (MomentBudgetAt 1900)).shapeA := e001

/-! ## Refining a leaf by a certified split, and retiring a route.

The tail-threshold leaf is split into two cases with a compiled coverage proof;
the moment-budget leaf is retired by proof. -/

inductive TailCase | small | large
  deriving DecidableEq

def tailCover : Split (current1900.leaf .tailThreshold) where
  Branch := TailCase
  child
    | .small => ⟨1900 ≤ 2048 → TailThresholdAt 1900⟩
    | .large => ⟨¬(1900 ≤ 2048) → TailThresholdAt 1900⟩
  discharge h := if hc : 1900 ≤ 2048 then h .small hc else h .large hc

def refined : Frontier target1900 :=
  current1900.splitLeaf currentDec .tailThreshold tailCover

-- Three live obligations: the untouched sibling plus the two children.
example : target1900.Proved :=
  refined.closeRoot fun
    | .inl ⟨.momentBudget, _⟩ => momentBudget1900
    | .inl ⟨.tailThreshold, h⟩ => absurd rfl h
    | .inr .small => fun _ => tailThreshold1900
    | .inr .large => fun _ => tailThreshold1900

/-- Retire the moment-budget route, which is now proved outright. -/
def retired : Frontier target1900 :=
  current1900.retireLeaf currentDec .momentBudget momentBudget1900

example : target1900.Proved :=
  retired.closeRoot fun
    | ⟨.tailThreshold, _⟩ => tailThreshold1900
    | ⟨.momentBudget, h⟩ => absurd rfl h

-- Historical lineage survives retirement: the original frontier and the seam
-- theorem are both still well-formed objects.
example : Frontier target1900 := current1900
example : MomentBudgetAt 1900 → TailThresholdAt 1900 → Achievable (radius 1900) :=
  achievable_of_budget_and_tail

/-! ## Reporting the live frontier (§14.2 items 6 and 7). -/

def report : FrontierReport target1900 where
  frontier := current1900
  tasks := [RootTask.momentBudget, RootTask.tailThreshold]
  taskId
    | .momentBudget => "T000_MomentBudget"
    | .tailThreshold => "T001_TailThreshold"
  status
    | .momentBudget => .closed
    | .tailThreshold => .«open»

example : report.render = ["T000_MomentBudget: CLOSED", "T001_TailThreshold: OPEN"] := rfl
example : report.render.length = report.tasks.length := report.render_length

end ToyResearch
