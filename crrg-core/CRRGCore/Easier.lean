import CRRGCore.Basic

/-!
# CRRGCore.Easier — "certified easier" as types, and the multiset lift (no Mathlib)

A sufficient sub-obligation is never logically weaker than its parent (`residual_sufficient`),
so "easier" has to be a property of proof difficulty. It can be:
* rung 1, **closed**;
* rung 2, **decided by computation**: a `MechCert` together with the kernel-evaluated result
  `decide () = true`. This settles the goal, so it closes the leaf;
* rung 3, a **strict decrease** of an owner-pinned measure.

Leaves carry a `Label`:
* `sized f n`, for an instance of owner-pinned family `f` of size `n`;
* `top`, for an unmeasured leaf.

Only comparable measured labels are ordered, and `Label.lt` is well-founded (`Label.lt_wf`).

The multiset lift is the positional form of the Dershowitz–Manna step, `Step r l' l`: replace
one element of `l` by finitely many elements, each `r`-below it. We prove `Step r` well-founded
whenever `r` is (`Step.wf`), directly and without Mathlib. The proof is an append lemma plus
singletons, after the proof of Mathlib's `WellFounded.cutExpand` (`Mathlib/Logic/Hydra.lean`).
Frontier moves are exactly positional replacements, so no quotient by permutation is needed.
-/

namespace CRRGCore

/-! ## The logical fact -/

/-- In `X ⇐ {Y, Z}` with `Y` closed, the residual `Z` is sufficient for `X`, so it is at least as
strong as `X`. It is never weaker. -/
theorem residual_sufficient {X Y Z : Prop} (hY : Y) (cover : Y → Z → X) : Z → X :=
  cover hY

/-- Equivalence needs the reduction to be two-way. -/
theorem residual_equiv_of_two_way {X Y Z : Prop} (hY : Y) (cover : Y → Z → X) (back : X → Z) :
    Z ↔ X :=
  ⟨cover hY, back⟩

/-- Reducing `n ≥ 0` to `n ≥ 1` is a sound one-way reduction to a strictly stronger, here false,
obligation: sufficiency does not imply easiness. -/
example : ∃ n : Nat, (n ≥ 1 → n ≥ 0) ∧ ¬ (n ≥ 1) := ⟨0, fun _ => Nat.zero_le _, by decide⟩

/-! ## Labels -/

/-- The label of a leaf. -/
inductive Label where
  /-- rung 3: instance of owner-pinned family `family`, with pinned size `size` -/
  | sized (family : Nat) (size : Nat)
  /-- unmeasured -/
  | top
  deriving DecidableEq, Repr

/-- The label order. Only **comparable measured** labels are ordered: same family, strictly
smaller size. `top` is below nothing and above nothing, so acquiring a measure (top → sized) is
never a decrease. That removes the review's item-4 credit case by construction. There is no
exchange rate between families. -/
inductive Label.lt : Label → Label → Prop
  | size {f m n : Nat} : m < n → Label.lt (.sized f m) (.sized f n)

/-- Decidable form of the label order. -/
def Label.ltb : Label → Label → Bool
  | .sized f m, .sized g n => decide (f = g) && decide (m < n)
  | _, _ => false

theorem Label.ltb_iff (a b : Label) : a.ltb b = true ↔ Label.lt a b := by
  constructor
  · intro h
    match a, b, h with
    | .sized f m, .sized g n, h =>
      have h' : decide (f = g) = true ∧ decide (m < n) = true := by
        have := h
        unfold Label.ltb at this
        rw [Bool.and_eq_true] at this
        exact this
      have hfg : f = g := of_decide_eq_true h'.1
      have hmn : m < n := of_decide_eq_true h'.2
      subst hfg
      exact .size hmn
    | .sized _ _, .top, h => exact absurd h Bool.false_ne_true
    | .top, .sized _ _, h => exact absurd h Bool.false_ne_true
    | .top, .top, h => exact absurd h Bool.false_ne_true
  · intro h
    cases h with
    | @size f m n hlt =>
      show (decide (f = f) && decide (m < n)) = true
      rw [Bool.and_eq_true]
      exact ⟨decide_eq_true rfl, decide_eq_true hlt⟩

instance : DecidableRel Label.lt := fun a b =>
  decidable_of_iff _ (Label.ltb_iff a b)

theorem Label.sized_acc (f n : Nat) : Acc Label.lt (.sized f n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    exact Acc.intro _ fun y hy => by
      cases hy with
      | size hmn => exact ih _ hmn

/-- **The label order is well-founded.** -/
theorem Label.lt_wf : WellFounded Label.lt := by
  constructor
  intro a
  cases a with
  | sized f n => exact Label.sized_acc f n
  | top => exact Acc.intro _ fun y hy => by cases hy

/-- An unmeasured leaf replaced by an unmeasured child is not a decrease. -/
theorem Label.not_lt_top_top : ¬ Label.lt .top .top := fun h => by cases h

/-- **Acquiring a measure earns nothing**: no label is below `top`. -/
theorem Label.not_lt_top (l : Label) : ¬ Label.lt l .top := fun h => by cases h

/-- Moving to another family never counts, whatever the sizes. -/
theorem Label.not_lt_cross {f g m n : Nat} (hfg : f ≠ g) :
    ¬ Label.lt (.sized f m) (.sized g n) := fun h => by
  cases h
  exact hfg rfl

/-- Growing a measured leaf (a larger size in the same family) is not a decrease. -/
theorem Label.not_lt_grow {f m n : Nat} (h : n ≤ m) : ¬ Label.lt (.sized f m) (.sized f n) :=
  fun hl => by cases hl; omega

/-! ## The positional Dershowitz–Manna step and its well-foundedness -/

/-- `Step r l' l`: `l'` is `l` with the element at position `i` replaced by a finite list `t` of
elements each `r`-below it. `t = []` is allowed: that is a closure. -/
def Step {α : Type} (r : α → α → Prop) (l' l : List α) : Prop :=
  ∃ i, ∃ h : i < l.length, ∃ t : List α, (∀ x ∈ t, r x l[i]) ∧ l' = replaceList l i t

theorem Step.not_nil {α : Type} {r : α → α → Prop} (l' : List α) : ¬ Step r l' [] := by
  rintro ⟨i, h, _⟩
  simp at h

/-- Steps on the left part of an append. -/
theorem Step.append_left {α : Type} {l₁ l₂ : List α} {i : Nat}
    (hi : i < l₁.length) (t : List α) :
    replaceList (l₁ ++ l₂) i t = replaceList l₁ i t ++ l₂ := by
  unfold replaceList
  rw [List.take_append_of_le_length (Nat.le_of_lt hi),
    List.drop_append_of_le_length (show i + 1 ≤ l₁.length by omega)]
  simp [List.append_assoc]

/-- Steps on the right part of an append. -/
theorem Step.append_right {α : Type} {l₁ l₂ : List α} {i : Nat}
    (hi : l₁.length ≤ i) (t : List α) :
    replaceList (l₁ ++ l₂) i t = l₁ ++ replaceList l₂ (i - l₁.length) t := by
  unfold replaceList
  have h1 : i + 1 - l₁.length = i - l₁.length + 1 := by omega
  rw [List.take_append, List.drop_append, List.take_of_length_le hi,
    List.drop_of_length_le (show l₁.length ≤ i + 1 by omega), h1]
  simp [List.append_assoc]

/-- **Append lemma.** Accessibility is closed under append. -/
theorem Step.acc_append {α : Type} {r : α → α → Prop} :
    ∀ l₁ : List α, Acc (Step r) l₁ → ∀ l₂ : List α, Acc (Step r) l₂ →
      Acc (Step r) (l₁ ++ l₂) := by
  intro l₁ h₁
  induction h₁ with
  | intro l₁ _ ih₁ =>
    intro l₂ h₂
    induction h₂ with
    | intro l₂ h₂' ih₂ =>
      constructor
      rintro y ⟨i, hi, t, ht, rfl⟩
      by_cases hlt : i < l₁.length
      · rw [Step.append_left hlt t]
        have hget : (l₁ ++ l₂)[i] = l₁[i] := List.getElem_append_left hlt
        exact ih₁ _ ⟨i, hlt, t, fun x hx => hget ▸ ht x hx, rfl⟩ l₂ (Acc.intro l₂ h₂')
      · have hle : l₁.length ≤ i := Nat.le_of_not_lt hlt
        rw [Step.append_right hle t]
        have hi2 : i - l₁.length < l₂.length := by simp at hi; omega
        have hget : (l₁ ++ l₂)[i] = l₂[i - l₁.length] := List.getElem_append_right hle
        exact ih₂ _ ⟨i - l₁.length, hi2, t, fun x hx => hget ▸ ht x hx, rfl⟩

/-- A list all of whose singletons are accessible is accessible. -/
theorem Step.acc_of_singletons {α : Type} {r : α → α → Prop} :
    ∀ l : List α, (∀ x ∈ l, Acc (Step r) [x]) → Acc (Step r) l
  | [], _ => Acc.intro _ fun y hy => absurd hy (Step.not_nil y)
  | x :: l, h => by
    have := Step.acc_append [x] (h x (List.mem_cons_self ..)) l
      (Step.acc_of_singletons l fun y hy => h y (List.mem_cons_of_mem _ hy))
    simpa using this

/-- A singleton `[a]` is accessible whenever `a` is `r`-accessible. -/
theorem Step.acc_singleton {α : Type} {r : α → α → Prop} {a : α} (ha : Acc r a) :
    Acc (Step r) [a] := by
  induction ha with
  | intro a _ ih =>
    constructor
    rintro y ⟨i, hi, t, ht, rfl⟩
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simp only [replaceList, List.take_zero, List.nil_append, List.drop_succ_cons, List.drop_nil,
      List.append_nil]
    exact Step.acc_of_singletons t fun x hx => ih x (ht x hx)

/-- **The multiset lift is well-founded.** Replacing one element by finitely many strictly
smaller ones cannot go on forever. -/
theorem Step.wf {α : Type} {r : α → α → Prop} (hr : WellFounded r) : WellFounded (Step r) :=
  ⟨fun l => Step.acc_of_singletons l fun x _ => Step.acc_singleton (hr.apply x)⟩

/-- **Local decrease gives a frontier decrease.** If every child label is below the replaced
leaf's label, the frontier's label list takes one `Step`. -/
theorem Step.of_local {α : Type} {r : α → α → Prop} (l : List α) (i : Nat) (hi : i < l.length)
    (t : List α) (hdec : ∀ x ∈ t, r x l[i]) : Step r (replaceList l i t) l :=
  ⟨i, hi, t, hdec, rfl⟩

/-! ## The multiset form: steps up to permutation (for the record-low rule) -/

/-- `PermStep r l' l`: `l'` is, up to permutation, one positional `Step` below `l`. This is the
multiset one-step Dershowitz–Manna relation (`CutExpand`) on lists. -/
def PermStep {α : Type} (r : α → α → Prop) (l' l : List α) : Prop :=
  ∃ m, l'.Perm m ∧ Step r m l

/-- A step from a list can be replayed from any permutation of it. -/
theorem Step.perm_commute {α : Type} {r : α → α → Prop} {l₁ l₂ m : List α}
    (hp : l₁.Perm l₂) (hs : Step r m l₁) : ∃ m', m.Perm m' ∧ Step r m' l₂ := by
  obtain ⟨i, hi, t, ht, rfl⟩ := hs
  have hmem : l₁[i] ∈ l₂ := hp.mem_iff.mp (List.getElem_mem hi)
  obtain ⟨C, D, hCD⟩ := List.append_of_mem hmem
  have hsplit : l₁ = l₁.take i ++ l₁[i] :: l₁.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hAB : (l₁.take i ++ l₁.drop (i + 1)).Perm (C ++ D) := by
    have h1 : (l₁.take i ++ l₁[i] :: l₁.drop (i + 1)).Perm (C ++ l₁[i] :: D) := by
      rw [← hsplit, ← hCD]; exact hp
    have h2 : (l₁[i] :: (l₁.take i ++ l₁.drop (i + 1))).Perm (l₁[i] :: (C ++ D)) :=
      (List.perm_middle.symm.trans h1).trans List.perm_middle
    exact (List.perm_cons _).mp h2
  refine ⟨C ++ t ++ D, ?_, ⟨C.length, ?_, t, ?_, ?_⟩⟩
  · show (replaceList l₁ i t).Perm (C ++ t ++ D)
    unfold replaceList
    have e1 : (l₁.take i ++ t ++ l₁.drop (i + 1)).Perm (t ++ (l₁.take i ++ l₁.drop (i + 1))) := by
      have := (List.perm_append_comm (l₁ := l₁.take i) (l₂ := t)).append_right (l₁.drop (i + 1))
      simpa [List.append_assoc] using this
    have e2 : (t ++ (C ++ D)).Perm (C ++ t ++ D) := by
      have := (List.perm_append_comm (l₁ := t) (l₂ := C)).append_right D
      simpa [List.append_assoc] using this
    exact e1.trans ((hAB.append_left t).trans e2)
  · rw [hCD]; simp
  · intro x hx
    have := ht x hx
    have hget : l₂[C.length]'(by rw [hCD]; simp) = l₁[i] := by
      simp [hCD]
    rw [hget]; exact this
  · rw [hCD]
    simp [replaceList, List.append_assoc]

/-- Predecessors are preserved by permutation, so accessibility transfers. -/
theorem PermStep.acc_of_perm {α : Type} {r : α → α → Prop} {l₁ l₂ : List α}
    (hp : l₁.Perm l₂) (h : Acc (PermStep r) l₂) : Acc (PermStep r) l₁ := by
  constructor
  rintro y ⟨m, hy, hs⟩
  obtain ⟨m', h'', hs'⟩ := Step.perm_commute hp hs
  exact h.inv ⟨m', hy.trans h'', hs'⟩

/-- **The multiset lift is well-founded** (up to permutation). -/
theorem PermStep.wf {α : Type} {r : α → α → Prop} (hr : WellFounded r) :
    WellFounded (PermStep r) := by
  constructor
  intro l
  induction (Step.wf hr).apply l with
  | intro l _ ih =>
    constructor
    rintro y ⟨m, hy, hs⟩
    exact PermStep.acc_of_perm hy (ih m hs)

/-- The Dershowitz–Manna order on label lists: the transitive closure of `PermStep`. -/
def DMLt (l' l : List Label) : Prop := Relation.TransGen (PermStep Label.lt) l' l

/-- **The lifted order is well-founded.** -/
theorem DMLt.wf : WellFounded DMLt := (PermStep.wf Label.lt_wf).transGen

/-- A positional step is a DM decrease. -/
theorem DMLt.of_step {l' l : List Label} (h : Step Label.lt l' l) : DMLt l' l :=
  .single ⟨l', List.Perm.refl _, h⟩

/-- Label lists of frontiers are well-founded under certified-easier steps. -/
theorem labelStep_wf : WellFounded (Step Label.lt) := Step.wf Label.lt_wf

/-! ## Rung certificates -/

/-- A two-way decision procedure for a goal. **Rung 2 settles in the kernel** (review item 5): a
certificate counts only together with a proof `h : decide () = true`, typically `rfl`. That proof
makes the kernel evaluate the program, and the goal is then *closed* (`MechCert.settle`,
`Move.closeByComputation`). So successful rung 2 is rung 1 with computational evidence.
`Nonempty (MechCert g)` alone grants nothing: classically it is `g ∨ ¬g`. -/
structure MechCert (g : Goal) where
  decide : Unit → Bool
  sound_true : decide () = true → g.claim
  sound_false : decide () = false → ¬ g.claim

/-- Settlement of rung 2: an evaluated certificate proves the goal. -/
theorem MechCert.settle {g : Goal} (c : MechCert g) (h : c.decide () = true) : g.claim :=
  c.sound_true h

/-- An evaluated negative certificate refutes the goal. -/
theorem MechCert.refute {g : Goal} (c : MechCert g) (h : c.decide () = false) : ¬ g.claim :=
  c.sound_false h

/-- An owner-pinned family: an index type, the claim at each index, and a size. -/
structure Family where
  Idx : Type
  claim : Idx → Prop
  size : Idx → Nat

/-- Why rung 3 is the right notion: a uniform step to strictly smaller instances closes the whole
family. -/
theorem Family.close_of_step (F : Family)
    (step : ∀ p, (∀ q, F.size q < F.size p → F.claim q) → F.claim p) : ∀ p, F.claim p := by
  intro p
  have key : ∀ n, ∀ p, F.size p ≤ n → F.claim p := by
    intro n
    induction n with
    | zero => exact fun p hp => step p fun q hq => absurd hq (by omega)
    | succ n ih => exact fun p hp => step p fun q hq => ih q (by omega)
  exact key (F.size p) p (Nat.le_refl _)

end CRRGCore
