import CRRG.Basic

/-!
# CRRG.Split

Exact finite/dependent splits: a `Split` proves that solving all branches
is sufficient to discharge the parent.
-/


namespace CRRG

universe u

/-- An exhaustive decomposition of `parent` into sub-goals.
    `discharge` proves that solving every branch implies the parent. -/
structure Split (parent : Goal) where
  Branch : Type u
  child : Branch → Goal
  discharge : (∀ i, (child i).claim) → parent.claim

namespace Split

/-- A trivial split with a single branch equal to the parent.

    Deliberately monomorphic at `Type 0`. `Split` itself is universe-polymorphic,
    but a *convenience* constructor whose universe nothing pins would force every
    downstream definition built from it to become polymorphic too, and the level
    would then be unsolvable at the use site. Anyone needing a trivial split at a
    higher universe can write the two-line structure instance directly. -/
def trivial (G : Goal) : Split.{0} G where
  Branch := Unit
  child _ := G
  discharge h := h ()

/-- Convert a split into an edge from a conjunction goal.
    The conjunction goal requires all branches simultaneously. -/
theorem toEdge {parent : Goal} (s : Split parent) : Edge parent ⟨∀ i, (s.child i).claim⟩ :=
  ⟨s.discharge⟩

end Split

end CRRG
