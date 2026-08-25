import CRRG.Basic
import CRRG.Split

/-!
# CRRG.Frontier

The live frontier: the kernel-authoritative set of obligations whose
complete discharge implies the root goal.
-/

namespace CRRG

universe u v

/-- A `Frontier` for a root goal is a typed package of leaf obligations
    whose complete discharge implies the root. -/
structure Frontier (root : Goal) where
  Task : Type u
  leaf : Task → Goal
  closeRoot : (∀ t, (leaf t).claim) → root.claim

namespace Frontier

/-- A trivial frontier with a single leaf equal to the root.

    Monomorphic at `Type 0` for the same reason as `Split.trivial`. -/
def trivial (root : Goal) : Frontier.{0} root where
  Task := Unit
  leaf _ := root
  closeRoot h := h ()

/-- Build a frontier from a `Split`. -/
def ofSplit {root : Goal} (s : Split.{u} root) : Frontier.{u} root where
  Task := s.Branch
  leaf := s.child
  closeRoot := s.discharge

/-- Re-root a whole frontier through an `Edge`.

    This **replaces the entire obligation set**: the result's leaves are exactly
    `inner`'s leaves. It is the right tool when `mid` is the only obligation
    standing between the leaves and `root`. To refine a single leaf of an
    existing frontier while preserving its siblings, use `refineLeaf` or
    `splitLeaf`. -/
def compose {root mid : Goal}
    (outerEdge : Edge root mid)
    (inner : Frontier.{u} mid) : Frontier.{u} root where
  Task := inner.Task
  leaf := inner.leaf
  closeRoot h := outerEdge.discharge (inner.closeRoot h)

/-- Refine a single leaf `t₀` through an `Edge`, preserving every sibling leaf.

    The task index set is unchanged; only `t₀`'s obligation is replaced by the
    (sufficient) child. Spec 6.4: "replace one leaf by a single child using an
    `Edge`; preserve all other leaves". -/
def refineLeaf {root : Goal} (F : Frontier.{u} root) (dec : DecidableEq F.Task)
    (t₀ : F.Task) {child : Goal} (e : Edge (F.leaf t₀) child) : Frontier root where
  Task := F.Task
  leaf t := @ite _ (t = t₀) (dec t t₀) child (F.leaf t)
  closeRoot h := F.closeRoot fun t =>
    @dite _ (t = t₀) (dec t t₀)
      (fun ht => ht ▸ e.discharge (by simpa [ht] using h t))
      (fun ht => by simpa [ht] using h t)

/-- Refine a single leaf `t₀` into the branches of a `Split`, preserving every
    sibling leaf.

    Spec 6.4 / 10.1: a leaf may only be replaced by children when a compiled
    coverage proof (`Split.discharge`) is supplied in the same commit. The new
    task set is "the old tasks other than `t₀`" plus "the split's branches". -/
def splitLeaf {root : Goal} (F : Frontier.{u} root) (dec : DecidableEq F.Task)
    (t₀ : F.Task) (s : Split.{v} (F.leaf t₀)) : Frontier.{max u v} root where
  Task := { t : F.Task // t ≠ t₀ } ⊕ s.Branch
  leaf
    | .inl t => F.leaf t.val
    | .inr b => s.child b
  closeRoot h := F.closeRoot fun t =>
    @dite _ (t = t₀) (dec t t₀)
      (fun ht => ht ▸ s.discharge (fun b => h (.inr b)))
      (fun ht => h (.inl ⟨t, ht⟩))

/-- Retire a leaf by discharging it from an already-established proof.

    Spec 10.3: a retired route may remain in source as a true theorem, but it
    must leave the *live* frontier. Retirement therefore requires an actual
    proof of the leaf; it is not a bookkeeping deletion. -/
def retireLeaf {root : Goal} (F : Frontier.{u} root) (dec : DecidableEq F.Task)
    (t₀ : F.Task) (proof : (F.leaf t₀).claim) : Frontier root where
  Task := { t : F.Task // t ≠ t₀ }
  leaf t := F.leaf t.val
  closeRoot h := F.closeRoot fun t =>
    @dite _ (t = t₀) (dec t t₀)
      (fun ht => ht ▸ proof)
      (fun ht => h ⟨t, ht⟩)

end Frontier

end CRRG
