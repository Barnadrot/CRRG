/-!
# CRRGCore.Basic — goals, edges, finite splits, frontiers, transitions, chains

Foundation: **search narrowing** (SMT-style). A frontier is a finite set of open obligations whose
joint closure implies a fixed root. Every accepted mutation replaces one leaf by a finite list of
children together with a *local* coverage certificate, and the invariant
`(∀ leaf, leaf) → root` is carried by the frontier value itself.

Kept from CRRG v0.10 with the same meaning: `Goal`, `Edge` (`CRRG/Basic.lean`), `Split` with its
coverage proof (`CRRG/Split.lean`), `Frontier` with `closeRoot` (`CRRG/Frontier.lean`),
`Transition` and its composition (`CRRG/Transition.lean`).

Changed (gap G11): children and leaves are *finite lists*. An infinite family is one leaf whose
claim is a `∀`. Finiteness is what makes frontier measures well-defined (`CRRGCore.Easier`).
-/

namespace CRRGCore

/-- A research obligation. -/
structure Goal where
  claim : Prop

/-- Rootward edge: proving `child` proves `parent`. `Prop`-valued: an edge carries no data. -/
structure Edge (parent child : Goal) : Prop where
  discharge : child.claim → parent.claim

theorem Edge.refl (G : Goal) : Edge G G := ⟨id⟩

theorem Edge.trans {A B C : Goal} (ab : Edge A B) (bc : Edge B C) : Edge A C :=
  ⟨fun h => ab.discharge (bc.discharge h)⟩

/-- An exhaustive split of `parent` into a finite list of children, with its coverage proof. -/
structure Split (parent : Goal) where
  children : List Goal
  discharge : (∀ c ∈ children, c.claim) → parent.claim

/-- The one-child split induced by an edge. -/
def Edge.toSplit {parent child : Goal} (e : Edge parent child) : Split parent where
  children := [child]
  discharge h := e.discharge (h child (List.mem_singleton.mpr rfl))

/-- A frontier for a fixed root. The root is a type index, so no operation can change it. -/
structure Frontier (root : Goal) where
  leaves : List Goal
  closeRoot : (∀ g ∈ leaves, g.claim) → root.claim

def Frontier.AllClosed {root : Goal} (F : Frontier root) : Prop :=
  ∀ g ∈ F.leaves, g.claim

/-- The initial frontier: the root as its own single leaf. -/
def Frontier.initial (root : Goal) : Frontier root where
  leaves := [root]
  closeRoot h := h root (List.mem_singleton.mpr rfl)

/-! ## Positional replacement on lists -/

/-- Replace position `i` of `l` by the list `new`. -/
def replaceList {α : Type} (l : List α) (i : Nat) (new : List α) : List α :=
  l.take i ++ new ++ l.drop (i + 1)

/-- Membership in a list, split around position `i`. -/
theorem mem_around {α : Type} {l : List α} {i : Nat} (hi : i < l.length) {g : α} (hg : g ∈ l) :
    g = l[i] ∨ g ∈ l.take i ∨ g ∈ l.drop (i + 1) := by
  have hl : l = l.take i ++ (l[i] :: l.drop (i + 1)) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  rw [hl] at hg
  rcases List.mem_append.mp hg with h | h
  · exact Or.inr (Or.inl h)
  · rcases List.mem_cons.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- An element of the replaced list is a new element or an untouched old one. -/
theorem mem_replaceList {α : Type} {l : List α} {i : Nat} {new : List α} {g : α}
    (hg : g ∈ replaceList l i new) : g ∈ new ∨ g ∈ l.take i ∨ g ∈ l.drop (i + 1) := by
  unfold replaceList at hg
  rcases List.mem_append.mp hg with h | h
  · rcases List.mem_append.mp h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · exact Or.inr (Or.inr h)

theorem mem_replaceList_of_new {α : Type} {l : List α} {i : Nat} {new : List α} {g : α}
    (hg : g ∈ new) : g ∈ replaceList l i new := by
  simp [replaceList, hg]

theorem mem_replaceList_of_take {α : Type} {l : List α} {i : Nat} {new : List α} {g : α}
    (hg : g ∈ l.take i) : g ∈ replaceList l i new := by
  simp [replaceList, hg]

theorem mem_replaceList_of_drop {α : Type} {l : List α} {i : Nat} {new : List α} {g : α}
    (hg : g ∈ l.drop (i + 1)) : g ∈ replaceList l i new := by
  simp [replaceList, hg]

/-- Mapping commutes with positional replacement. -/
theorem map_replaceList {α β : Type} (f : α → β) (l : List α) (i : Nat) (new : List α) :
    (replaceList l i new).map f = replaceList (l.map f) i (new.map f) := by
  simp [replaceList, List.map_take, List.map_drop]

/-! ## The single state-changing operator on frontiers -/

/-- Replace leaf `i` by `children`, given the local certificate that the children cover it. -/
def Frontier.replaceAt {root : Goal} (F : Frontier root) (i : Fin F.leaves.length)
    (children : List Goal) (cover : (∀ c ∈ children, c.claim) → F.leaves[i].claim) :
    Frontier root where
  leaves := replaceList F.leaves i children
  closeRoot h := F.closeRoot fun g hg => by
    rcases mem_around i.isLt hg with rfl | hmem | hmem
    · exact cover fun c hc => h c (mem_replaceList_of_new hc)
    · exact h g (mem_replaceList_of_take hmem)
    · exact h g (mem_replaceList_of_drop hmem)

/-! ## Transitions and checked chains (refinement-mapping foundation) -/

/-- Closing `target` closes `source`. -/
structure Transition {root : Goal} (source target : Frontier root) : Prop where
  preserve : target.AllClosed → source.AllClosed

theorem Transition.refl {root : Goal} (F : Frontier root) : Transition F F := ⟨id⟩

theorem Transition.comp {root : Goal} {F G H : Frontier root}
    (fg : Transition F G) (gh : Transition G H) : Transition F H :=
  ⟨fun h => fg.preserve (gh.preserve h)⟩

/-- **Invariant theorem.** Every application of `replaceAt` is a transition. -/
theorem Frontier.replaceAt_transition {root : Goal} (F : Frontier root) (i : Fin F.leaves.length)
    (children : List Goal) (cover : (∀ c ∈ children, c.claim) → F.leaves[i].claim) :
    Transition F (F.replaceAt i children cover) :=
  ⟨fun h g hg => by
    rcases mem_around i.isLt hg with rfl | hmem | hmem
    · exact cover fun c hc => h c (mem_replaceList_of_new hc)
    · exact h g (mem_replaceList_of_take hmem)
    · exact h g (mem_replaceList_of_drop hmem)⟩

/-- A checked chain of transitions (reflexive–transitive closure). -/
inductive Chain {root : Goal} : Frontier root → Frontier root → Prop
  | refl (F : Frontier root) : Chain F F
  | step {F G H : Frontier root} : Chain F G → Transition G H → Chain F H

theorem Chain.toTransition {root : Goal} {F G : Frontier root} (c : Chain F G) :
    Transition F G := by
  induction c with
  | refl => exact Transition.refl _
  | step _ t ih => exact ih.comp t

/-- Closing the last frontier of any checked chain proves the root. -/
theorem Chain.closeRoot {root : Goal} {F G : Frontier root} (c : Chain F G)
    (h : G.AllClosed) : root.claim :=
  F.closeRoot (c.toTransition.preserve h)

/-- A refuted leaf kills its frontier (the decomposition), never the root. -/
theorem Frontier.dead_of_refuted {root : Goal} (F : Frontier root) {g : Goal}
    (hg : g ∈ F.leaves) (h : ¬ g.claim) : ¬ F.AllClosed :=
  fun hall => h (hall g hg)

/-- A refuted root blocks every frontier. -/
theorem Frontier.refuted_root {root : Goal} (F : Frontier root) (h : ¬ root.claim) :
    ¬ F.AllClosed :=
  fun hall => h (F.closeRoot hall)

end CRRGCore
