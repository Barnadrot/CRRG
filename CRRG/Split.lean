import CRRG.Basic

/-!
# CRRG.Split

Exact finite/dependent splits: a `Split` proves that solving all branches
is sufficient to discharge the parent.
-/


namespace CRRG

/-- An exhaustive decomposition of `parent` into sub-goals.
    `discharge` proves that solving every branch implies the parent. -/
structure Split (parent : Goal) where
  Branch : Type
  child : Branch → Goal
  discharge : (∀ i, (child i).claim) → parent.claim

namespace Split

/-- A trivial split with a single branch equal to the parent. -/
def trivial (G : Goal) : Split G where
  Branch := Unit
  child _ := G
  discharge h := h ()

/-- Convert a split into an edge from a conjunction goal.
    The conjunction goal requires all branches simultaneously. -/
def toEdge {parent : Goal} (s : Split parent) : Edge parent ⟨∀ i, (s.child i).claim⟩ :=
  ⟨s.discharge⟩

end Split

end CRRG
