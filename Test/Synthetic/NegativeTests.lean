import CRRG
import Test.Support.ExpectFailure

/-!
# Synthetic test: Negative tests

Spec acceptance criterion 8: the gate must **reject** a deliberately weakened
child statement or a missing branch. Every test below asserts a rejection via
`#expect_failure`; if CRRG ever became lax enough to accept one of these, the
build breaks.
-/

open CRRG

/-! ## 1. A split must cover every case.

The positive control: a two-branch split whose coverage proof exists. -/

private inductive Parity | even | odd

private def paritySplit : Split ⟨∀ (n : Nat), n = n⟩ where
  Branch := Parity
  child
    | .even => ⟨∀ (n : Nat), n % 2 = 0 → n = n⟩
    | .odd => ⟨∀ (n : Nat), ¬(n % 2 = 0) → n = n⟩
  discharge h n :=
    if hmod : n % 2 = 0 then h .even n hmod
    else h .odd n hmod

example : Goal.Proved ⟨∀ (n : Nat), n = n⟩ :=
  paritySplit.discharge fun
    | .even => fun _ _ => rfl
    | .odd => fun _ _ => rfl

/- Negative: dropping the odd branch leaves `discharge` unprovable, because the
single remaining child only speaks about even `n`. -/
#expect_failure
private def missingBranchSplit : Split ⟨∀ (n : Nat), n = n⟩ where
  Branch := Unit
  child _ := ⟨∀ (n : Nat), n % 2 = 0 → n = n⟩
  discharge h n := h () n (by rfl)

/- Negative: a `Split` may not be closed by supplying only some branches. -/
#expect_failure
example : Goal.Proved ⟨∀ (n : Nat), n = n⟩ :=
  paritySplit.discharge fun
    | .even => fun _ _ => rfl

/-! ## 2. A weakened child may not discharge the parent. -/

private def strongChild : Goal := ⟨∀ (n : Nat), n + 0 = n⟩
private def weakChild : Goal := ⟨(0 : Nat) + 0 = 0⟩
private def parentNeedsStrong : Goal := ⟨∀ (n : Nat), n + 0 = n⟩

-- Positive: the exact child discharges the parent.
private def honestEdge : Edge parentNeedsStrong strongChild := ⟨_root_.id⟩

/- Negative: the weakened child (one instance instead of all `n`) does not. -/
#expect_failure
private def weakeningEdge : Edge parentNeedsStrong weakChild := ⟨fun h => h⟩

/-! ## 3. Edge direction is rootward and cannot be reversed. -/

private def correctDirection : Edge ⟨True⟩ ⟨1 = 1⟩ := ⟨fun _ => trivial⟩

/- Negative: `Edge parent child` is `child.claim → parent.claim`, so a proof in
the leafward direction is rejected. -/
#expect_failure
private def reversedDirection : Edge ⟨(1 : Nat) = 1⟩ ⟨True⟩ := ⟨fun _ => trivial⟩

/-! ## 4. A guard must consume both truth values. -/

private def guardBoth : GuardedMap ⟨Bool⟩ ⟨Unit⟩ ⟨Unit⟩ where
  guard b := b
  onPass _ _ := ()
  onFail _ _ := ()

/- Negative: omitting `onFail` is not a `GuardedMap`. The guard-failure branch
cannot be dropped. -/
#expect_failure
private def guardMissingFail : GuardedMap ⟨Bool⟩ ⟨Unit⟩ ⟨Unit⟩ where
  guard b := b
  onPass _ _ := ()

/- Negative: `onPass` may only use the witness under `guard w = true`; it may
not be applied to a witness on the failing side. -/
#expect_failure
private def guardIgnoresGuard : GuardedMap ⟨Bool⟩ ⟨{ b : Bool // b = true }⟩ ⟨Unit⟩ where
  guard b := b
  onPass w _ := ⟨w, rfl⟩
  onFail _ _ := ()

/-! ## 5. An escape branch cannot be silently dropped. -/

private abbrev escParent : BadNode := ⟨Bool⟩
private abbrev escMain : BadNode := ⟨Unit⟩
private abbrev escEscape : BadNode := ⟨Unit⟩

private def escExample : EscapeMap escParent escMain escEscape where
  classify
    | true => Sum.inl ()
    | false => Sum.inr ()

/- Negative: closing the parent needs the escape branch too. -/
#expect_failure
example (hMain : escMain.Closed) : escParent.Closed :=
  escExample.closed_parent hMain

/-! ## 6. A classifier must be total over parent witnesses. -/

/- Negative: a `WitnessSplit` classifier that handles only one constructor. -/
#expect_failure
private def partialClassifier : WitnessSplit ⟨Bool⟩ where
  Branch := Bool
  child _ := ⟨Unit⟩
  classify
    | true => ⟨true, ()⟩

/-! ## 7. A frontier must actually use all of its leaves. -/

private def twoLeafFrontier : Frontier ⟨True ∧ True⟩ where
  Task := Bool
  leaf
    | true => ⟨True⟩
    | false => ⟨True⟩
  closeRoot h := ⟨h true, h false⟩

example : Goal.Proved ⟨True ∧ True⟩ :=
  twoLeafFrontier.closeRoot fun
    | true => trivial
    | false => trivial

/- Negative: a frontier that claims a strictly stronger root than its leaves
support cannot be built. -/
#expect_failure
private def dishonestFrontier : Frontier ⟨∀ (n : Nat), n < 5⟩ where
  Task := Unit
  leaf _ := ⟨(0 : Nat) < 5⟩
  closeRoot h := fun _ => h ()

/-! ## 8. Candidate lifecycle.

The candidate-layer rejections (proxy promotion, weakening a sealed target,
refuting without a disproof, promoting a resolved candidate) live in
`Test/Synthetic/CandidateSeal.lean`, next to the positive lifecycle tests they
contrast with. -/
