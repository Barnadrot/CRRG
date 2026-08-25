import CRRG.Basic
import CRRG.Split

/-!
# CRRG.Witness

Counterexample-based nodes for structural research decompositions.
`BadNode` represents a set of counterexamples; closing it means showing
the set is empty. `WitnessMap` and `WitnessSplit` compose these nodes.
-/


namespace CRRG

universe u v w

/-- A counterexample node. `Witness` is the type of bad objects;
    the node is closed when the witness type is empty. -/
structure BadNode where
  Witness : Type u

/-- A `BadNode` is closed when its witness type is empty. -/
abbrev BadNode.Closed (N : BadNode) : Prop := N.Witness → False

/-- A map from parent witnesses to child witnesses.
    If the child is closed, the parent is closed. -/
structure WitnessMap (parent : BadNode.{u}) (child : BadNode.{v}) where
  map : parent.Witness → child.Witness

namespace WitnessMap

/-- Identity witness map. -/
def id (N : BadNode.{u}) : WitnessMap N N := ⟨_root_.id⟩

/-- Compose witness maps. -/
def trans {A : BadNode.{u}} {B : BadNode.{v}} {C : BadNode.{w}}
    (ab : WitnessMap A B) (bc : WitnessMap B C) : WitnessMap A C :=
  ⟨bc.map ∘ ab.map⟩

/-- If the child is closed, the parent is closed. -/
theorem closed_parent {parent : BadNode.{u}} {child : BadNode.{v}}
    (r : WitnessMap parent child)
    (hChild : child.Closed) : parent.Closed :=
  fun w => hChild (r.map w)

/-- Convert a `WitnessMap` into a proposition-level `Edge`. -/
def toEdge {parent : BadNode.{u}} {child : BadNode.{v}}
    (r : WitnessMap parent child) :
    Edge ⟨parent.Closed⟩ ⟨child.Closed⟩ :=
  ⟨r.closed_parent⟩

end WitnessMap

/-- An exhaustive decomposition of parent witnesses into branches.
    `classify` sends every parent witness to a specific branch witness. -/
structure WitnessSplit (parent : BadNode.{u}) where
  Branch : Type v
  child : Branch → BadNode.{w}
  classify : parent.Witness → (i : Branch) × (child i).Witness

namespace WitnessSplit

/-- If all branches are closed, the parent is closed. -/
theorem closed_parent {parent : BadNode.{u}}
    (s : WitnessSplit.{u, v, w} parent)
    (hAll : ∀ i, (s.child i).Closed) : parent.Closed :=
  fun w =>
    let ⟨i, wi⟩ := s.classify w
    hAll i wi

/-- Convert a `WitnessSplit` into a proposition-level `Split`. -/
def toSplit {parent : BadNode.{u}}
    (s : WitnessSplit.{u, v, w} parent) :
    Split.{v} ⟨parent.Closed⟩ where
  Branch := s.Branch
  child i := ⟨(s.child i).Closed⟩
  discharge h := s.closed_parent h

end WitnessSplit

end CRRG
