import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Finset.Card

/-!
# CRRGClassical.Converse — the class-cap ⇔ list-bound converse

For a linear code given as the kernel of a syndrome map `syn : α →+ β`, the list of a received word `y`
at radius `d` is in bijection with the syndrome class of `syn y`, by `c ↦ y − c`. So a list bound and a
per-syndrome class cap **of the same size** are equivalent whenever every syndrome is realized
(`syn` surjective). A per-syndrome cap is therefore the list bound restated, **by proof**.

This is *proved* for any such code, with any weight function. A development that proves only the
direction class cap ⇒ list bound gets the converse by checking that its syndrome map has this shape
(surjective, with the list and class defined as below).
-/

namespace CRRGClassical.Converse

variable {α β : Type*} [AddCommGroup α] [AddCommGroup β] [Fintype α] [DecidableEq β]
  (syn : α →+ β) (wt : α → ℕ) (d : ℕ)

/-- The list of `y` at radius `d`: codewords (syndrome zero) within weight distance `d`. -/
def listAt (y : α) : Finset α := Finset.univ.filter fun c => syn c = 0 ∧ wt (y - c) ≤ d

/-- The syndrome class of `s` at radius `d`: error patterns of weight at most `d` with syndrome `s`. -/
def classAt (s : β) : Finset α := Finset.univ.filter fun e => syn e = s ∧ wt e ≤ d

/-- *proved*: the list of `y` and the class of `syn y` have the same size (`c ↦ y − c`). -/
theorem card_listAt_eq (y : α) : (listAt syn wt d y).card = (classAt syn wt d (syn y)).card := by
  apply Finset.card_nbij' (fun c => y - c) (fun e => y - e)
  · intro c hc
    simp only [listAt, classAt, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hc ⊢
    exact ⟨by rw [map_sub, hc.1, sub_zero], hc.2⟩
  · intro e he
    simp only [listAt, classAt, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at he ⊢
    exact ⟨by rw [map_sub, he.1, sub_self], by rw [sub_sub_cancel]; exact he.2⟩
  · intro c _; simp only [sub_sub_cancel]
  · intro e _; simp only [sub_sub_cancel]

/-- *proved*: a class cap gives the list bound (the tree's direction). -/
theorem listBound_of_classCap (L : ℕ) (h : ∀ s, (classAt syn wt d s).card ≤ L) (y : α) :
    (listAt syn wt d y).card ≤ L := by
  rw [card_listAt_eq]; exact h _

/-- *proved*: **the converse**: a list bound gives the class cap of the same size, when every syndrome
is realized. -/
theorem classCap_of_listBound (hsurj : Function.Surjective syn) (L : ℕ)
    (h : ∀ y, (listAt syn wt d y).card ≤ L) (s : β) : (classAt syn wt d s).card ≤ L := by
  obtain ⟨y, rfl⟩ := hsurj s
  rw [← card_listAt_eq]; exact h y

/-- *proved*: **a per-syndrome cap and a list bound of the same size are equivalent.** -/
theorem classCap_iff_listBound (hsurj : Function.Surjective syn) (L : ℕ) :
    (∀ s, (classAt syn wt d s).card ≤ L) ↔ (∀ y, (listAt syn wt d y).card ≤ L) :=
  ⟨fun h y => listBound_of_classCap syn wt d L h y, classCap_of_listBound syn wt d hsurj L⟩

end CRRGClassical.Converse
