import CRRG

/-!
# Synthetic test: GuardedMap

Tests that guarded refinements retain both pass and fail branches.
-/


open CRRG

private def parentNode : BadNode := ⟨Nat⟩
private def passNode : BadNode := ⟨{ n : Nat // n < 10 }⟩
private def failNode : BadNode := ⟨{ n : Nat // ¬(n < 10) }⟩

private def guardedExample : GuardedMap parentNode passNode failNode where
  guard n := decide (n < 10)
  onPass n h := ⟨n, of_decide_eq_true h⟩
  onFail n h := ⟨n, of_decide_eq_false h⟩

-- Verify branch assignment
example : (guardedExample.toWitnessSplit.child true) = passNode := rfl
example : (guardedExample.toWitnessSplit.child false) = failNode := rfl

-- Both branches are REQUIRED to close the parent.
-- This is the key property: you cannot close the parent without
-- closing the guard-failure branch.
example (hPass : passNode.Closed) (hFail : failNode.Closed) :
    parentNode.Closed :=
  guardedExample.closed_parent hPass hFail

-- Same via WitnessSplit conversion
example (hPass : passNode.Closed) (hFail : failNode.Closed) :
    parentNode.Closed :=
  guardedExample.toWitnessSplit.closed_parent fun
    | true => hPass
    | false => hFail
