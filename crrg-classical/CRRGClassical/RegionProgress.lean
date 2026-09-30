import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Pairwise

set_option autoImplicit false

/-!
# L-03: finite restriction frontiers

Open and proved closed regions form a nonempty-region, disjoint partition of the
fixed finite root region. Only exact splits and proof-backed closes are counted.
The ambient type may be finite; finiteness of the root region alone suffices.
This model is independent of the sufficient-frontier `CRRGCore.State` semantics.
-/

namespace CRRGClassical.RegionProgress

open scoped BigOperators

variable {Θ : Type*} [DecidableEq Θ]

def Obl (Φ : Θ → Prop) (R : Finset Θ) : Prop := ∀ θ ∈ R, Φ θ

def regionsUnion : List (Finset Θ) → Finset Θ
  | [] => ∅
  | R :: rest => R ∪ regionsUnion rest

theorem mem_regionsUnion (θ : Θ) (rs : List (Finset Θ)) :
    θ ∈ regionsUnion rs ↔ ∃ R ∈ rs, θ ∈ R := by
  induction rs with
  | nil => simp [regionsUnion]
  | cons R rs ih => simp [regionsUnion, ih]

/-- Finite ordered collections; pairwise disjointness is across open and closed regions. -/
structure Model (Φ : Θ → Prop) (R₀ : Finset Θ) where
  openRegions : List (Finset Θ)
  closedRegions : List (Finset Θ)
  nonempty : ∀ R ∈ openRegions ++ closedRegions, R.Nonempty
  disjoint : (openRegions ++ closedRegions).Pairwise Disjoint
  cover : regionsUnion (openRegions ++ closedRegions) = R₀
  closed_proved : ∀ R ∈ closedRegions, Obl Φ R

variable {Φ : Θ → Prop} {R₀ : Finset Θ}

def initial (Φ : Θ → Prop) (R₀ : Finset Θ) : Model Φ R₀ :=
  if h : R₀ = ∅ then
    { openRegions := [], closedRegions := []
      nonempty := by simp
      disjoint := by simp
      cover := by simp [regionsUnion, h]
      closed_proved := by simp }
  else
    { openRegions := [R₀], closedRegions := []
      nonempty := by simpa using Finset.nonempty_iff_ne_empty.mpr h
      disjoint := by simp
      cover := by simp [regionsUnion]
      closed_proved := by simp }

theorem region_subset_root (S : Model Φ R₀) {R : Finset Θ}
    (hR : R ∈ S.openRegions ++ S.closedRegions) : R ⊆ R₀ := by
  intro θ hθ
  rw [← S.cover, mem_regionsUnion]
  exact ⟨R, hR, hθ⟩

theorem root_iff_open (S : Model Φ R₀) :
    Obl Φ R₀ ↔ ∀ R ∈ S.openRegions, Obl Φ R := by
  constructor
  · intro h R hR θ hθ
    exact h θ (region_subset_root S (List.mem_append_left _ hR) hθ)
  · intro h θ hθ
    rw [← S.cover, mem_regionsUnion] at hθ
    obtain ⟨R, hR, hθ⟩ := hθ
    rcases List.mem_append.mp hR with hopen | hclosed
    · exact h R hopen θ hθ
    · exact S.closed_proved R hclosed θ hθ

theorem frontier_counterexample_refutes_root (S : Model Φ R₀) {R : Finset Θ}
    (hR : R ∈ S.openRegions) {θ : Θ} (hθ : θ ∈ R) (hbad : ¬ Φ θ) : ¬ Obl Φ R₀ := by
  intro hroot
  exact hbad (hroot θ (region_subset_root S (List.mem_append_left _ hR) hθ))

def total (w : Θ → ℕ) (rs : List (Finset Θ)) : ℕ :=
  (rs.map (fun R => ∑ θ ∈ R, w θ)).sum

omit [DecidableEq Θ] in
theorem total_nil (w : Θ → ℕ) : total w [] = 0 := rfl

omit [DecidableEq Θ] in
theorem total_cons (w : Θ → ℕ) (R : Finset Θ) (rs : List (Finset Θ)) :
    total w (R :: rs) = (∑ θ ∈ R, w θ) + total w rs := rfl

omit [DecidableEq Θ] in
theorem total_append (w : Θ → ℕ) (rs ts : List (Finset Θ)) :
    total w (rs ++ ts) = total w rs + total w ts := by
  simp [total]

theorem total_eq_union (w : Θ → ℕ) (rs : List (Finset Θ))
    (hd : rs.Pairwise Disjoint) : total w rs = ∑ θ ∈ regionsUnion rs, w θ := by
  induction rs with
  | nil => simp [total, regionsUnion]
  | cons R rs ih =>
    obtain ⟨hR, hrest⟩ := List.pairwise_cons.mp hd
    have hdis : Disjoint R (regionsUnion rs) := by
      apply Finset.disjoint_left.mpr
      intro θ hθ hθ'
      obtain ⟨T, hT, ht⟩ := (mem_regionsUnion θ rs).mp hθ'
      exact Finset.disjoint_left.mp (hR T hT) hθ ht
    rw [total_cons, regionsUnion, Finset.sum_union hdis, ih hrest]

def mass (w : Θ → ℕ) (S : Model Φ R₀) : ℕ := total w S.openRegions

omit [DecidableEq Θ] in
theorem total_one_eq_card (R : Finset Θ) : (∑ _θ ∈ R, (1 : ℕ)) = R.card := by simp

theorem open_mass_le_root (S : Model Φ R₀) : mass (fun _ => 1) S ≤ R₀.card := by
  have h := total_eq_union (fun _ => 1) (S.openRegions ++ S.closedRegions) S.disjoint
  rw [total_append, S.cover, total_one_eq_card] at h
  unfold mass
  omega

omit [DecidableEq Θ] in
theorem length_le_total (rs : List (Finset Θ)) (hne : ∀ R ∈ rs, R.Nonempty) :
    rs.length ≤ total (fun _ => 1) rs := by
  induction rs with
  | nil => simp [total]
  | cons R rs ih =>
    have hpos := Finset.card_pos.mpr (hne R (by simp))
    have hrest := ih (fun T hT => hne T (by simp [hT]))
    rw [List.length_cons, total_cons, total_one_eq_card]
    omega

def potential (S : Model Φ R₀) : ℕ := 2 * mass (fun _ => 1) S - S.openRegions.length

theorem potential_le_root (S : Model Φ R₀) : potential S ≤ 2 * R₀.card - 1 := by
  have hmass := open_mass_le_root S
  by_cases he : S.openRegions = []
  · simp [potential, mass, he, total]
  · have hlen : 0 < S.openRegions.length := List.length_pos_iff.mpr he
    unfold potential
    omega

/-- An exact split into at least two nonempty, pairwise disjoint children. -/
structure SplitStep (S T : Model Φ R₀) where
  before : List (Finset Θ)
  after : List (Finset Θ)
  parent : Finset Θ
  children : List (Finset Θ)
  source : S.openRegions = before ++ parent :: after
  target : T.openRegions = before ++ children ++ after
  closed : T.closedRegions = S.closedRegions
  arity : 2 ≤ children.length
  nonempty : ∀ R ∈ children, R.Nonempty
  disjoint : children.Pairwise Disjoint
  exactUnion : regionsUnion children = parent

/-- A nonempty region is retired only with a proof of its full obligation. -/
structure CloseStep (S T : Model Φ R₀) where
  before : List (Finset Θ)
  after : List (Finset Θ)
  region : Finset Θ
  source : S.openRegions = before ++ region :: after
  target : T.openRegions = before ++ after
  closed : T.closedRegions = region :: S.closedRegions
  nonempty : region.Nonempty
  proof : Obl Φ region

theorem split_weight_conserved (w : Θ → ℕ) {S T : Model Φ R₀} (h : SplitStep S T) :
    mass w T = mass w S := by
  have hsum := total_eq_union w h.children h.disjoint
  rw [h.exactUnion] at hsum
  simp only [mass, h.target, h.source, total_append, total_cons]
  omega

theorem split_length_grows {S T : Model Φ R₀} (h : SplitStep S T) :
    S.openRegions.length + 1 ≤ T.openRegions.length := by
  have ha := h.arity
  simp only [h.source, h.target, List.length_append, List.length_cons]
  omega

theorem close_weight_balance (w : Θ → ℕ) {S T : Model Φ R₀} (h : CloseStep S T) :
    mass w S = mass w T + ∑ θ ∈ h.region, w θ := by
  simp only [mass, h.target, h.source, total_append, total_cons]
  omega

theorem close_weight_decreases (w : Θ → ℕ) (hw : ∀ θ, 0 < w θ)
    {S T : Model Φ R₀} (h : CloseStep S T) : mass w T < mass w S := by
  obtain ⟨θ, hθ⟩ := h.nonempty
  have hle := Finset.single_le_sum (fun x _ => Nat.zero_le (w x)) hθ
  have hpos := hw θ
  have hbalance := close_weight_balance w h
  omega

theorem close_length {S T : Model Φ R₀} (h : CloseStep S T) :
    S.openRegions.length = T.openRegions.length + 1 := by
  simp only [h.source, h.target, List.length_append, List.length_cons]
  omega

/-- The only counted steps. No attempt, speculative work, or stutter constructor exists. -/
inductive Step : Model Φ R₀ → Model Φ R₀ → ℕ → ℕ → Prop
  | split {S T} (h : SplitStep S T) : Step S T 1 0
  | close {S T} (h : CloseStep S T) : Step S T 0 1

theorem step_potential {S T : Model Φ R₀} {splits closes : ℕ}
    (h : Step S T splits closes) : splits + closes + potential T ≤ potential S := by
  have hlenT : T.openRegions.length ≤ mass (fun _ => 1) T :=
    length_le_total T.openRegions (fun R hR => T.nonempty R (List.mem_append_left _ hR))
  cases h with
  | split h =>
    have hm := split_weight_conserved (fun _ => 1) h
    have hl := split_length_grows h
    unfold potential
    omega
  | close h =>
    have hm := close_weight_balance (fun _ => 1) h
    rw [total_one_eq_card] at hm
    have hp := Finset.card_pos.mpr h.nonempty
    have hl := close_length h
    unfold potential
    omega

/-- A finite valid trace, with its actual split and close counts. -/
inductive Trace (S₀ : Model Φ R₀) : Model Φ R₀ → ℕ → ℕ → Prop
  | nil : Trace S₀ S₀ 0 0
  | snoc {S T : Model Φ R₀} {s c ds dc : ℕ}
      (prior : Trace S₀ S s c) (step : Step S T ds dc) : Trace S₀ T (s + ds) (c + dc)

theorem trace_potential {S T : Model Φ R₀} {splits closes : ℕ}
    (h : Trace S T splits closes) : splits + closes + potential T ≤ potential S := by
  induction h with
  | nil => simp
  | snoc _ hstep ih =>
    have := step_potential hstep
    omega

/-- At most `2 * |R₀| - 1` actual operations, from any valid partition of the root. -/
theorem split_close_bound {S T : Model Φ R₀} {splitCount closeCount : ℕ}
    (h : Trace S T splitCount closeCount) : splitCount + closeCount ≤ 2 * R₀.card - 1 := by
  have ht := trace_potential h
  have hp := potential_le_root S
  omega

theorem trace_zero_eq {S T : Model Φ R₀} {splits closes : ℕ}
    (h : Trace S T splits closes) (hz : splits + closes = 0) : T = S := by
  cases h with
  | nil => rfl
  | snoc hp hs => cases hs <;> omega

/-- The empty root has no split or close: every valid finite trace is zero-step. -/
theorem empty_root_zero_steps {S T : Model Φ R₀} {splits closes : ℕ}
    (h : Trace S T splits closes) (h0 : R₀ = ∅) :
    splits = 0 ∧ closes = 0 ∧ T = S := by
  have hb := split_close_bound h
  simp only [h0, Finset.card_empty, Nat.mul_zero, Nat.zero_sub] at hb
  have hz : splits + closes = 0 := by omega
  exact ⟨by omega, by omega, trace_zero_eq h hz⟩

end CRRGClassical.RegionProgress
