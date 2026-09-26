import Mathlib.Logic.Hydra
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Tactic.Abel
import CRRGCore.State

/-!
# CRRGClassical.Easier — the "certified easier" ladder on Mathlib objects

This is the first slice of the faithful classical CRRG: a **parallel** library that re-proves the core's
"certified easier" ladder with Mathlib (trusted, pinned to `c5ea00351c`). The
list-based core (`crrg-core`) is untouched. This library imports it only for the bridge.

* **Labels** form a `PartialOrder` (`a ≤ b ↔ a = b ∨ Label.lt a b`) with `WellFoundedLT`.
* **A leaf step** is `Relation.CutExpand` (replace one element by finitely many smaller ones).
  Well-foundedness is `WellFounded.cutExpand`.
* **Frontiers** are multisets, and the frontier order is `Multiset.IsDershowitzMannaLT`.
  Well-foundedness is `Multiset.wellFounded_isDershowitzMannaLT`.
* **The record-low credit rule** is `IsDershowitzMannaLT new record`. `no_infinite_credits` holds for
  any run of records.
* **The bridge**, in both directions: `DMLt l' l ↔ IsDershowitzMannaLT ↑l' ↑l`. So the two cores
  certify the same moves (`core_credit_classical`).

Everything here is *proved* (kernel), with classical axioms allowed.
-/

namespace CRRGClassical

open CRRGCore Relation Multiset

/-! ## Labels as a well-founded partial order -/

theorem Label.lt_irrefl' (a : Label) : ¬ Label.lt a a := by
  intro h; cases h; omega

theorem Label.lt_trans' {a b c : Label} (hab : Label.lt a b) (hbc : Label.lt b c) : Label.lt a c := by
  cases hab with
  | size h1 =>
    cases hbc with
    | size h2 => exact .size (Nat.lt_trans h1 h2)

instance : PartialOrder Label where
  le a b := a = b ∨ Label.lt a b
  lt := Label.lt
  le_refl a := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | hab
    · exact hbc
    · rcases hbc with rfl | hbc
      · exact Or.inr hab
      · exact Or.inr (Label.lt_trans' hab hbc)
  lt_iff_le_not_ge a b := by
    constructor
    · intro h
      refine ⟨Or.inr h, ?_⟩
      rintro (rfl | h')
      · exact Label.lt_irrefl' _ h
      · exact Label.lt_irrefl' _ (Label.lt_trans' h h')
    · rintro ⟨rfl | h, hn⟩
      · exact absurd (Or.inl rfl) hn
      · exact h
  le_antisymm a b hab hba := by
    rcases hab with rfl | hab
    · rfl
    · rcases hba with rfl | hba
      · rfl
      · exact absurd (Label.lt_trans' hab hba) (Label.lt_irrefl' _)

instance : WellFoundedLT Label := ⟨Label.lt_wf⟩

theorem lt_eq : ((· < ·) : Label → Label → Prop) = Label.lt := rfl

/-! ## Leaf steps are `CutExpand` -/

/-- A list, split around position `i`, as a multiset. -/
theorem coe_split {α : Type} (l : List α) (i : Nat) (hi : i < l.length) :
    (l : Multiset α) = l[i] ::ₘ (↑(l.take i) + ↑(l.drop (i + 1))) := by
  have hl : l = l.take i ++ l[i] :: l.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  conv_lhs => rw [hl]
  rw [← Multiset.coe_add, ← Multiset.cons_coe, Multiset.add_cons]

/-- A positional step is a `CutExpand` of the list images. -/
theorem step_cutExpand {α : Type} {r : α → α → Prop} {l' l : List α} (h : Step r l' l) :
    CutExpand r (l' : Multiset α) (l : Multiset α) := by
  obtain ⟨i, hi, t, ht, rfl⟩ := h
  refine ⟨(t : Multiset α), l[i], fun a ha => ht a (Multiset.mem_coe.mp ha), ?_⟩
  rw [coe_split l i hi, ← singleton_add]
  simp only [replaceList, ← Multiset.coe_add]
  abel

/-- **Shorter proof** of the core's `Step.wf`, from Mathlib's `WellFounded.cutExpand`. -/
theorem Step.wf' {α : Type} {r : α → α → Prop} (hr : WellFounded r) : WellFounded (Step r) :=
  Subrelation.wf (fun h => step_cutExpand h) (InvImage.wf (fun l : List α => (l : Multiset α))
    hr.cutExpand)

/-- `PermStep` is exactly `CutExpand` on the list images (for an irreflexive relation). -/
theorem permStep_iff_cutExpand {α : Type} [DecidableEq α] {r : α → α → Prop} [Std.Irrefl r]
    {l' l : List α} : PermStep r l' l ↔ CutExpand r (l' : Multiset α) (l : Multiset α) := by
  constructor
  · rintro ⟨m, hp, hs⟩
    rw [Multiset.coe_eq_coe.mpr hp]
    exact step_cutExpand hs
  · intro h
    obtain ⟨t, a, ht, ha, he⟩ := cutExpand_iff.mp h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (Multiset.mem_coe.mp ha)
    refine ⟨replaceList l i t.toList, ?_, ⟨i, hi, t.toList, fun x hx =>
      ht x (Multiset.mem_toList.mp hx), rfl⟩⟩
    apply Multiset.coe_eq_coe.mp
    rw [he, coe_split l i hi, Multiset.erase_cons_head]
    simp only [replaceList, ← Multiset.coe_add, Multiset.coe_toList]
    abel

instance : Std.Irrefl Label.lt := ⟨Label.lt_irrefl'⟩

/-- `DMLt` is the transitive closure of `CutExpand` on the list images. -/
theorem dmlt_iff_transGen {l' l : List Label} :
    DMLt l' l ↔ TransGen (CutExpand Label.lt) (l' : Multiset Label) (l : Multiset Label) := by
  constructor
  · intro h
    exact TransGen.lift (fun l : List Label => (l : Multiset Label))
      (fun a b hab => permStep_iff_cutExpand.mp hab) h
  · intro h
    suffices key : ∀ {M N : Multiset Label}, TransGen (CutExpand Label.lt) M N →
        ∀ l' l : List Label, (l' : Multiset Label) = M → (l : Multiset Label) = N → DMLt l' l from
      key h l' l rfl rfl
    intro M N hMN
    induction hMN with
    | single hr =>
      intro l' l h1 h2
      subst h1 h2
      exact .single (permStep_iff_cutExpand.mpr hr)
    | @tail c N' _ hcN ih =>
      intro l' l h1 h2
      obtain ⟨lc, rfl⟩ := Quot.exists_rep c
      subst h2
      exact .tail (ih l' lc h1 rfl) (permStep_iff_cutExpand.mpr hcN)

/-! ## `TransGen CutExpand` is the Dershowitz–Manna order -/

section DM

variable {α : Type} [Preorder α] [DecidableEq α]

instance : Std.Irrefl ((· < ·) : α → α → Prop) := ⟨lt_irrefl⟩

theorem isDM_of_cutExpand {M N : Multiset α} (h : CutExpand (· < ·) M N) :
    IsDershowitzMannaLT M N := by
  obtain ⟨t, a, ht, ha, rfl⟩ := cutExpand_iff.mp h
  refine ⟨N.erase a, t, {a}, by simp, rfl, ?_, fun y hy => ⟨a, Multiset.mem_singleton_self a, ht y hy⟩⟩
  rw [add_comm, singleton_add, Multiset.cons_erase ha]

theorem transGen_of_isDM_aux : ∀ (Z X Y : Multiset α), Z ≠ 0 → (∀ y ∈ Y, ∃ z ∈ Z, y < z) →
    TransGen (CutExpand (· < ·)) (X + Y) (X + Z) := by
  intro Z
  induction Z using Multiset.induction_on with
  | empty => intro X Y h; exact absurd rfl h
  | cons z Z' ih =>
    intro X Y _ hY
    classical
    set Yz := Y.filter (· < z)
    set Y' := Y.filter (fun y => ¬ y < z)
    have hYs : Y = Yz + Y' := (Multiset.filter_add_not _ Y).symm
    have step : CutExpand (· < ·) (X + Yz + Z') (X + z ::ₘ Z') := by
      refine ⟨Yz, z, fun a ha => (Multiset.mem_filter.mp ha).2, ?_⟩
      rw [← singleton_add]; abel
    have hY' : ∀ y ∈ Y', ∃ z' ∈ Z', y < z' := by
      intro y hy
      obtain ⟨hyY, hnz⟩ := Multiset.mem_filter.mp hy
      obtain ⟨z0, hz0, hlt⟩ := hY y hyY
      rcases Multiset.mem_cons.mp hz0 with rfl | hz0'
      · exact absurd hlt hnz
      · exact ⟨z0, hz0', hlt⟩
    by_cases hZ' : Z' = 0
    · have hY'0 : Y' = 0 := by
        rw [Multiset.eq_zero_iff_forall_notMem]
        intro y hy
        obtain ⟨z', hz', _⟩ := hY' y hy
        rw [hZ'] at hz'; exact absurd hz' (Multiset.notMem_zero _)
      rw [hYs, hY'0, add_zero]
      have : X + Yz = X + Yz + Z' := by rw [hZ', add_zero]
      rw [this]
      exact .single step
    · have := ih (X + Yz) Y' hZ' hY'
      rw [hYs, ← add_assoc]
      exact .tail this step

/-- **The bridge to Mathlib's order**: `TransGen CutExpand` is `IsDershowitzMannaLT`. -/
theorem transGen_cutExpand_iff_isDM {M N : Multiset α} :
    TransGen (CutExpand (· < ·)) M N ↔ IsDershowitzMannaLT M N := by
  constructor
  · intro h
    induction h with
    | single h => exact isDM_of_cutExpand h
    | tail _ h ih => exact ih.trans (isDM_of_cutExpand h)
  · rintro ⟨X, Y, Z, hZ, rfl, rfl, hYZ⟩
    exact transGen_of_isDM_aux Z X Y (by simpa using hZ) hYZ

end DM

/-- **The two cores certify the same moves**: `DMLt l' l ↔ IsDershowitzMannaLT ↑l' ↑l`. -/
theorem dmlt_iff_isDM {l' l : List Label} :
    DMLt l' l ↔ IsDershowitzMannaLT (l' : Multiset Label) (l : Multiset Label) := by
  rw [dmlt_iff_transGen, ← transGen_cutExpand_iff_isDM]
  rfl

/-- **Shorter proof** of the core's `DMLt.wf`, from `Multiset.wellFounded_isDershowitzMannaLT`. -/
theorem DMLt.wf' : WellFounded DMLt :=
  Subrelation.wf (fun h => dmlt_iff_isDM.mp h)
    (InvImage.wf (fun l : List Label => (l : Multiset Label)) wellFounded_isDershowitzMannaLT)

/-! ## The record-low credit rule and `no_infinite_credits` on multisets -/

section Runs

variable {α : Type} [Preorder α] [WellFoundedLT α]

/-- The record-low credit rule on multisets: a move is credited iff its new frontier is
Dershowitz–Manna below the record. -/
def Credited (record new : Multiset α) : Prop := IsDershowitzMannaLT new record

/-- A run of records: each step keeps the record (uncredited: refute, learn, uncredited commit) or
lowers it (credited commit). -/
def RecordRun (rec : ℕ → Multiset α) : Prop :=
  ∀ i, rec (i + 1) = rec i ∨ Credited (rec i) (rec (i + 1))

omit [WellFoundedLT α] in
theorem RecordRun.mono {rec : ℕ → Multiset α} (h : RecordRun rec) (i : ℕ) :
    ∀ k, rec (i + k) = rec i ∨ IsDershowitzMannaLT (rec (i + k)) (rec i) := by
  intro k
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rcases h (i + k) with he | hc <;> rcases ih with he' | hc'
    · exact Or.inl (he.trans he')
    · exact Or.inr (he ▸ hc')
    · exact Or.inr (he' ▸ hc)
    · exact Or.inr (hc.trans hc')

/-- **No run earns infinitely many credits**: the analogue of the core's `no_infinite_credits`. -/
theorem no_infinite_credits (rec : ℕ → Multiset α) (h : RecordRun rec) :
    ¬ ∀ i, ∃ j, i ≤ j ∧ Credited (rec j) (rec (j + 1)) := by
  intro hinf
  have key : ∀ r, Acc IsDershowitzMannaLT r → ∀ i, rec i = r → False := by
    intro r hr
    induction hr with
    | intro r _ ih =>
      intro i hi
      obtain ⟨j, hij, hc⟩ := hinf i
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
      have hdrop : IsDershowitzMannaLT (rec (i + k + 1)) r := by
        rcases RecordRun.mono h i k with he | hlt
        · rw [← hi, ← he]; exact hc
        · rw [← hi]; exact hc.trans hlt
      exact ih _ hdrop (i + k + 1) rfl
  exact key _ (wellFounded_isDershowitzMannaLT.apply (rec 0)) 0 rfl

end Runs

/-- **The core's credit rule is the classical one**: a move the list-based core credits
(`creditOf = certifiedEasier`) has its new frontier Dershowitz–Manna below the record, as multisets. -/
theorem core_credit_classical {root : Goal} (S : State root) (m : Move S)
    (h : S.creditOf m = .certifiedEasier) :
    Credited (S.record : Multiset Label) (S.newLabels m : Multiset Label) :=
  dmlt_iff_isDM.mp (State.creditOf_sound S m h)

/-- A credited commit of the core lowers the record in Mathlib's order. -/
theorem core_commit_classical {root : Goal} (S S' : State root) (m : Move S)
    (h : State.commit S m = .ok (S', .certifiedEasier)) :
    IsDershowitzMannaLT (S'.record : Multiset Label) (S.record : Multiset Label) :=
  dmlt_iff_isDM.mp (State.commit_credit_record S S' m h)

/-- **The core's `no_infinite_credits`, re-derived from the classical one.** The records of any core
run, read as multisets, form a classical `RecordRun`, and every credited core step is a classical
credit. So the Mathlib theorem `no_infinite_credits` gives the core's statement. -/
theorem core_no_infinite_credits_classical {root : Goal} (s : ℕ → State root)
    (hs : ∀ i, State.Advance (s i) (s (i + 1))) :
    ¬ ∀ i, ∃ j, i ≤ j ∧ State.Credited (s j) (s (j + 1)) := by
  intro hinf
  let rec_ : ℕ → Multiset Label := fun i => ((s i).record : Multiset Label)
  have hrun : RecordRun rec_ := by
    intro i
    rcases State.advance_record (hs i) with he | hlt
    · exact Or.inl (by simp only [rec_, he])
    · exact Or.inr (dmlt_iff_isDM.mp hlt)
  apply no_infinite_credits rec_ hrun
  intro i
  obtain ⟨j, hij, m, hm⟩ := hinf i
  exact ⟨j, hij, core_commit_classical _ _ m hm⟩

end CRRGClassical
