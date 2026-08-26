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
theorem toEdge {parent : BadNode.{u}} {child : BadNode.{v}}
    (r : WitnessMap parent child) :
    Edge ⟨parent.Closed⟩ ⟨child.Closed⟩ :=
  ⟨r.closed_parent⟩

end WitnessMap

/-- An exhaustive decomposition of parent witnesses into branches.
    `classify` sends every parent witness to a specific branch witness.

    **The branch family is an index, not a field.** `WitnessSplit parent child`
    names the decomposition in its own type, which is what lets a task
    assignment be type-linked to the exact children it covers (§14.2 item 5)
    rather than merely to "some three-way split of this parent". It also puts
    `WitnessSplit` in line with every other relational type in the calculus —
    `Edge parent child`, `WitnessMap parent child`,
    `GuardedMap parent pass fail`, `EscapeMap parent main escape` — all of
    which are indexed by both endpoints.

    Two further consequences, neither of them incidental:

    - §6.6 item 4 ("where the type is incidental rather than the point of the
      abstraction, make it a parameter instead of a field") applies here. The
      *classification* is the point of a `WitnessSplit`; the index type is
      incidental. As a field, `s.Branch` behind a plain `def` would not reduce
      during instance search — the same projection hazard §6.6 documents.
    - As fields, `Branch` and `child` contributed their universes to the
      structure's sort only inside a `max`, which Lean's `checkUnivs` linter
      reports as over-parameterisation. As indices they occur on their own, so
      the calculus keeps three genuinely independent universes *and* is clean
      under a modern toolchain. Collapsing them instead would have cost real
      generality: `GuardedMap`'s branch index is `Bool : Type 0` while its pass
      and fail nodes may sit at any level. -/
structure WitnessSplit (parent : BadNode.{u}) {Branch : Type v}
    (child : Branch → BadNode.{w}) where
  classify : parent.Witness → (i : Branch) × (child i).Witness

namespace WitnessSplit

/-- If all branches are closed, the parent is closed. -/
theorem closed_parent {parent : BadNode.{u}} {Branch : Type v}
    {child : Branch → BadNode.{w}}
    (s : WitnessSplit parent child)
    (hAll : ∀ i, (child i).Closed) : parent.Closed :=
  fun w =>
    let ⟨i, wi⟩ := s.classify w
    hAll i wi

/-- Convert a `WitnessSplit` into a proposition-level `Split`. -/
def toSplit {parent : BadNode.{u}} {Branch : Type v}
    {child : Branch → BadNode.{w}}
    (s : WitnessSplit parent child) :
    Split.{v} ⟨parent.Closed⟩ where
  Branch := Branch
  child i := ⟨(child i).Closed⟩
  discharge h := s.closed_parent h

end WitnessSplit

end CRRG
