import CRRG

/-!
# Synthetic test: GuardedMap

Tests that guarded refinements retain both pass and fail branches.
-/


open CRRG

private abbrev parentNode : BadNode := ⟨Nat⟩
private abbrev passNode : BadNode := ⟨{ n : Nat // n < 10 }⟩
private abbrev failNode : BadNode := ⟨{ n : Nat // ¬(n < 10) }⟩

private def guardedExample : GuardedMap parentNode passNode failNode where
  guard n := decide (n < 10)
  onPass n h := ⟨n, of_decide_eq_true h⟩
  onFail n h := ⟨n, of_decide_eq_false h⟩

-- Verify branch assignment. The child family is an *index* of `WitnessSplit`,
-- so it is fixed by the conversion's type rather than read out of a field:
-- `toWitnessSplit`'s signature already names `GuardedMap.child passNode
-- failNode`, and these check that family assigns the branches as intended.
example : GuardedMap.child passNode failNode true = passNode := rfl
example : GuardedMap.child passNode failNode false = failNode := rfl

-- The guard-failure branch is visible in the conversion's *type*, so it cannot
-- be dropped by an abstraction that stops carrying the checked data (§5.4).
example : WitnessSplit parentNode (GuardedMap.child passNode failNode) :=
  guardedExample.toWitnessSplit

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
