import CRRG.Witness

/-!
# CRRG.Escape

Explicit escape packages for two-way splits where a reduction either
produces the desired object or an exceptional one. The exception
remains on the frontier until separately handled.
-/


namespace CRRG

universe u v

/-- An escape map classifies each parent witness as either a main-branch
    witness or an escape-branch witness. The escape branch cannot be
    silently dropped. -/
structure EscapeMap (parent : BadNode.{u}) (main escape : BadNode.{v}) where
  classify : parent.Witness → main.Witness ⊕ escape.Witness

namespace EscapeMap

/-- The two-branch child family of an escape split: `true` is the main node,
    `false` is the exceptional node.

    Named rather than inlined because `WitnessSplit` is indexed by its child
    family, so this function appears in `toWitnessSplit`'s type — which is
    exactly where Spec §5.5 wants the exception to be: impossible to delete
    without changing a signature. -/
def child (main escape : BadNode.{v}) : Bool → BadNode.{v}
  | true => main
  | false => escape

/-- Convert an `EscapeMap` to a `WitnessSplit` with two branches. -/
def toWitnessSplit {parent : BadNode.{u}} {main escape : BadNode.{v}}
    (e : EscapeMap parent main escape) :
    WitnessSplit parent (EscapeMap.child main escape) where
  classify w :=
    match e.classify w with
    | Sum.inl m => ⟨true, m⟩
    | Sum.inr esc => ⟨false, esc⟩

/-- If both main and escape branches are closed, the parent is closed. -/
theorem closed_parent {parent : BadNode.{u}} {main escape : BadNode.{v}}
    (e : EscapeMap parent main escape)
    (hMain : main.Closed) (hEscape : escape.Closed) : parent.Closed :=
  e.toWitnessSplit.closed_parent (fun
    | true => hMain
    | false => hEscape)

end EscapeMap

end CRRG
