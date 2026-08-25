import CRRG.Basic
import CRRG.Split

/-!
# CRRG.Frontier

The live frontier: the kernel-authoritative set of obligations whose
complete discharge implies the root goal.
-/


namespace CRRG

/-- A `Frontier` for a root goal is a typed package of leaf obligations
    whose complete discharge implies the root. -/
structure Frontier (root : Goal) where
  Task : Type
  leaf : Task → Goal
  closeRoot : (∀ t, (leaf t).claim) → root.claim

namespace Frontier

/-- A trivial frontier with a single leaf equal to the root. -/
def trivial (root : Goal) : Frontier root where
  Task := Unit
  leaf _ := root
  closeRoot h := h ()

/-- Build a frontier from a `Split`. -/
def ofSplit {root : Goal} (s : Split root) : Frontier root where
  Task := s.Branch
  leaf := s.child
  closeRoot := s.discharge

/-- Compose two frontiers: if the root of `inner` matches a leaf of `outer`,
    the combined frontier replaces that leaf with `inner`'s leaves.
    This is the generic composition; in practice, specific frontier
    constructions are written by hand for each refinement step. -/
def compose {root mid : Goal}
    (outerEdge : Edge root mid)
    (inner : Frontier mid) : Frontier root where
  Task := inner.Task
  leaf := inner.leaf
  closeRoot h := outerEdge.discharge (inner.closeRoot h)

end Frontier

end CRRG
