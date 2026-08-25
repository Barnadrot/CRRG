import CRRG.Witness

/-!
# CRRG.Guarded

Guarded transformations that must consume both truth values of a guard.
The static analogue of ArkLib's guarded-verifier discipline.
-/


namespace CRRG

universe u v

/-- A guarded transformation on a `BadNode`.
    The guard partitions parent witnesses into pass/fail branches.
    Both branches must be handled explicitly. -/
structure GuardedMap (parent : BadNode.{u}) (pass fail : BadNode.{v}) where
  guard : parent.Witness → Bool
  onPass : (w : parent.Witness) → guard w = true → pass.Witness
  onFail : (w : parent.Witness) → guard w = false → fail.Witness

namespace GuardedMap

/-- Convert a `GuardedMap` to a `WitnessSplit` with two branches. -/
def toWitnessSplit {parent : BadNode.{u}} {pass fail : BadNode.{v}}
    (g : GuardedMap parent pass fail) :
    WitnessSplit parent where
  Branch := Bool
  child
    | true => pass
    | false => fail
  classify w :=
    match h : g.guard w with
    | true => ⟨true, g.onPass w h⟩
    | false => ⟨false, g.onFail w h⟩

/-- If both pass and fail branches are closed, the parent is closed. -/
theorem closed_parent {parent : BadNode.{u}} {pass fail : BadNode.{v}}
    (g : GuardedMap parent pass fail)
    (hPass : pass.Closed) (hFail : fail.Closed) : parent.Closed :=
  g.toWitnessSplit.closed_parent (fun
    | true => hPass
    | false => hFail)

end GuardedMap

end CRRG
