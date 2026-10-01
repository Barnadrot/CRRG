import CRRGClassical.Easier
import Mathlib.Order.Interval.Finset.Nat

/-!
# CRRGClassical.State — the credit machinery over multisets

This ports `CRRGCore/State.lean`'s credit machinery to Mathlib's Dershowitz–Manna order.

**Design choice.** The core's `State` keeps its `List Label` record. Every statement here reads the
record and the new frontier as **multisets** (`↑S.record`, `↑(S.newLabels m)`) through the bridge
`dmlt_iff_isDM`. This keeps a single `State` (no duplicate), keeps `commit` and the credit check
**computable** (the runner `#eval`s them), and makes every order statement a Mathlib one.

| Core (list order `DMLt`) | Classical (multiset order `IsDershowitzMannaLT`) | Label |
|---|---|---|
| `Move.recordCert : Option (PLift (DMLt …))` | `Move.withCert m h` from `h : IsDershowitzMannaLT ↑new ↑record` | proved |
| `creditOf_sound` | `creditOf_sound_classical` (= the runner theorem `runner_credit_sound`) | proved |
| `commit_credit_record` | `commit_credit_record_classical` | proved |
| `easierSucc_wf` | `easierSucc_wf_classical`: `InvImage.wf` of `wellFounded_isDershowitzMannaLT` | proved |
| `advance_record`, `run_record_mono`, `no_infinite_credits` | `recordRun_of_advance` (a `RecordRun`) + `no_infinite_credits` | proved |

Crux-family regions as `Finset` intervals, with admission order-independence as a **general** theorem
(`sdiff_sdiff_comm`), are at the end.
-/

namespace CRRGClassical

open CRRGCore Relation Multiset

variable {root : Goal}

/-! ## The record certificate from a Mathlib proof -/

/-- A move with a record certificate given as a **Mathlib** proof: the new frontier is
Dershowitz–Manna below the record, as multisets. It is converted to the core's `DMLt` through the
bridge. -/
def _root_.CRRGCore.Move.withCert {S : State root} (m : Move S)
    (h : IsDershowitzMannaLT
      (replaceList S.leafLabels m.pos (m.children.map (Child.label S.reg)) : Multiset Label)
      (S.record : Multiset Label)) : Move S :=
  { m with recordCert := some ⟨dmlt_iff_isDM.mpr h⟩ }

/-- *proved*: a move carrying a Mathlib record certificate is credited. -/
theorem withCert_credited {S : State root} (m : Move S) (h) :
    S.creditOf (m.withCert h) = .certifiedEasier := by
  simp [State.creditOf, Move.withCert]

/-! ## The credit rule over multisets -/

/-- *proved*: **the computable check is sound for the classical credit.** When the runner's
`#eval` of the core's `creditOf` returns `certifiedEasier`, the new frontier is Dershowitz–Manna below
the record in Mathlib's order. The runner cites this theorem. -/
theorem runner_credit_sound (S : State root) (m : Move S) (h : S.creditOf m = .certifiedEasier) :
    Credited (S.record : Multiset Label) (S.newLabels m : Multiset Label) :=
  core_credit_classical S m h

/-- *proved*: `creditOf_sound` over multisets. -/
theorem creditOf_sound_classical (S : State root) (m : Move S)
    (h : S.creditOf m = .certifiedEasier) :
    IsDershowitzMannaLT (S.newLabels m : Multiset Label) (S.record : Multiset Label) :=
  runner_credit_sound S m h

/-- *proved*: `commit_credit_record` over multisets. -/
theorem commit_credit_record_classical (S S' : State root) (m : Move S)
    (h : State.commit S m = .ok (S', .certifiedEasier)) :
    IsDershowitzMannaLT (S'.record : Multiset Label) (S.record : Multiset Label) :=
  core_commit_classical S S' m h

/-- *proved*: `easierSucc_wf` as `InvImage.wf` of Mathlib's `wellFounded_isDershowitzMannaLT`. -/
theorem easierSucc_wf_classical : WellFounded (@State.EasierSucc root) :=
  Subrelation.wf (fun {_ _} ⟨m, hm⟩ => commit_credit_record_classical _ _ m hm)
    (InvImage.wf (fun S : State root => (S.record : Multiset Label)) wellFounded_isDershowitzMannaLT)

/-! ## Runs: a `RecordRun` instance -/

/-- *proved*: the records of any core run, read as multisets, form a classical `RecordRun`. This
replaces `advance_record` and `run_record_mono`. -/
theorem recordRun_of_advance (s : ℕ → State root) (hs : ∀ i, State.Advance (s i) (s (i + 1))) :
    RecordRun (fun i => ((s i).record : Multiset Label)) := by
  intro i
  rcases State.advance_record (hs i) with he | hlt
  · exact Or.inl (by simp only [he])
  · exact Or.inr (dmlt_iff_isDM.mp hlt)

/-- *proved*: **no core run earns infinitely many credits**, from the classical `RecordRun` and
`no_infinite_credits`. -/
theorem no_infinite_credits_state (s : ℕ → State root)
    (hs : ∀ i, State.Advance (s i) (s (i + 1))) :
    ¬ ∀ i, ∃ j, i ≤ j ∧ State.Credited (s j) (s (j + 1)) := by
  intro hinf
  apply no_infinite_credits _ (recordRun_of_advance s hs)
  intro i
  obtain ⟨j, hij, m, hm⟩ := hinf i
  exact ⟨j, hij, commit_credit_record_classical _ _ m hm⟩

/-! ## Crux-family regions as `Finset` intervals -/

section Regions

/-- An admitted result closes finitely many intervals of a region. -/
def Region.admit (closed : List (ℕ × ℕ)) (r : Finset ℕ) : Finset ℕ :=
  closed.foldl (fun acc ab => acc \ Finset.Icc ab.1 ab.2) r

theorem Region.admit_eq (closed : List (ℕ × ℕ)) (r : Finset ℕ) :
    Region.admit closed r = r \ (closed.map fun ab => Finset.Icc ab.1 ab.2).foldr (· ∪ ·) ∅ := by
  induction closed generalizing r with
  | nil => simp [Region.admit]
  | cons ab rest ih =>
    simp only [Region.admit, List.foldl_cons] at ih ⊢
    rw [ih, List.map_cons, List.foldr_cons, sdiff_sdiff_left]
    rfl

/-- *proved*: **admission order does not matter, in general.** Two admitted results give the same
region in either order. This is the general form of crrg-core's instance check
`CruxFamily.admit_order_irrelevant`. -/
theorem Region.admit_comm (e₁ e₂ : List (ℕ × ℕ)) (r : Finset ℕ) :
    Region.admit e₂ (Region.admit e₁ r) = Region.admit e₁ (Region.admit e₂ r) := by
  rw [Region.admit_eq, Region.admit_eq, Region.admit_eq, Region.admit_eq, sdiff_sdiff_comm]

/-- *proved*: admission only shrinks a region. -/
theorem Region.admit_subset (e : List (ℕ × ℕ)) (r : Finset ℕ) : Region.admit e r ⊆ r := by
  rw [Region.admit_eq]; exact Finset.sdiff_subset

end Regions

/-! ## Part 2, M3: records and credited frontiers stay below the initial label -/

theorem dmlt_le_some {l' l : List Label} (h : DMLt l' l) :
    ∀ x ∈ l', ∃ y ∈ l, x ≤ y := by
  obtain ⟨X, Y, Z, _, hnew, hold, hYZ⟩ := dmlt_iff_isDM.mp h
  intro x hx
  have hx' : x ∈ X + Y := hnew ▸ (Multiset.mem_coe.mpr hx)
  rcases Multiset.mem_add.mp hx' with hxX | hxY
  · exact ⟨x, Multiset.mem_coe.mp (hold.symm ▸ Multiset.mem_add.mpr (.inl hxX)), le_rfl⟩
  · obtain ⟨y, hy, hxy⟩ := hYZ x hxY
    exact ⟨y, Multiset.mem_coe.mp (hold.symm ▸ Multiset.mem_add.mpr (.inr hy)), le_of_lt hxy⟩

theorem run_record_mono_stutter (s : ℕ → State root)
    (hs : ∀ i, State.Advance (s i) (s (i + 1)) ∨ s (i + 1) = s i)
    (i j : ℕ) (hij : i ≤ j) :
    (s j).record = (s i).record ∨ DMLt (s j).record (s i).record := by
  induction j, hij using Nat.le_induction with
  | base => exact .inl rfl
  | succ j _ ih =>
    have hstep : (s (j + 1)).record = (s j).record ∨
        DMLt (s (j + 1)).record (s j).record := by
      rcases hs j with h | h
      · exact State.advance_record h
      · exact .inl (congrArg State.record h)
    rcases hstep with heq | hlt
    · rwa [heq]
    · right
      rcases ih with heq | hlt'
      · rwa [heq] at hlt
      · exact Relation.TransGen.trans hlt hlt'

theorem record_le_root (s : ℕ → State root)
    (hs : ∀ i, State.Advance (s i) (s (i + 1)) ∨ s (i + 1) = s i)
    {ℓ₀ : Label} (h0 : (s 0).record = [ℓ₀]) : ∀ i, ∀ x ∈ (s i).record, x ≤ ℓ₀ := by
  intro i x hx
  rcases run_record_mono_stutter s hs 0 i (Nat.zero_le _) with heq | hlt
  · rw [heq, h0] at hx
    have : x = ℓ₀ := by simpa using hx
    subst x; exact le_rfl
  · obtain ⟨y, hy, hxy⟩ := dmlt_le_some hlt x hx
    rw [h0] at hy
    have : y = ℓ₀ := by simpa using hy
    subst y; exact hxy

theorem credited_frontier_record {S S' : State root} (hc : State.Credited S S') :
    S'.leafLabels = S'.record := by
  obtain ⟨m, hm⟩ := hc
  rw [State.commit_leafLabels S S' m _ hm, State.commit_record S S' m _ hm,
    ← State.commit_tag S S' m _ hm]

theorem credited_le_root (s : ℕ → State root)
    (hs : ∀ i, State.Advance (s i) (s (i + 1)) ∨ s (i + 1) = s i)
    {ℓ₀ : Label} (h0 : (s 0).record = [ℓ₀]) {i : ℕ}
    (hc : State.Credited (s i) (s (i + 1))) :
    ∀ x ∈ (s (i + 1)).leafLabels, x ≤ ℓ₀ := by
  rw [credited_frontier_record hc]
  exact record_le_root s hs h0 (i + 1)

theorem dmlt_top_iff_nil (l : List Label) : DMLt l [.top] ↔ l = [] := by
  rw [dmlt_iff_isDM]
  change IsDershowitzMannaLT (l : Multiset Label) {Label.top} ↔ l = []
  rw [dm_singleton_iff]
  constructor
  · intro h
    cases l with
    | nil => rfl
    | cons a rest => exact (Label.not_lt_top a (h a (by simp))).elim
  · rintro rfl; simp

theorem dmlt_not_nil (l : List Label) : ¬ DMLt l [] := by
  intro h
  obtain ⟨X, Y, Z, hZ, _, heq, _⟩ := dmlt_iff_isDM.mp h
  have hcard := congrArg Multiset.card heq
  simp only [Multiset.coe_nil, Multiset.card_zero, Multiset.card_add] at hcard
  exact hZ (Multiset.card_eq_zero.mp (by omega))

theorem top_root_credit (s : ℕ → State root)
    (hs : ∀ i, State.Advance (s i) (s (i + 1)) ∨ s (i + 1) = s i)
    (h0 : (s 0).record = [.top]) {i : ℕ}
    (hc : State.Credited (s i) (s (i + 1))) :
    (s (i + 1)).leaves = [] ∧ root.claim ∧
      ∀ j, i < j → ¬ State.Credited (s j) (s (j + 1)) := by
  obtain ⟨m, hm⟩ := hc
  have hdrop := State.commit_credit_record (s i) (s (i + 1)) m hm
  have hbelow : DMLt (s (i + 1)).record [.top] := by
    rcases run_record_mono_stutter s hs 0 i (Nat.zero_le _) with heq | hlt
    · simpa [heq, h0] using hdrop
    · simpa [h0] using Relation.TransGen.trans hdrop hlt
  have hempty := (dmlt_top_iff_nil _).mp hbelow
  have hlabels := (credited_frontier_record ⟨m, hm⟩).trans hempty
  have hleaves : (s (i + 1)).leaves = [] := by simpa [State.leafLabels] using hlabels
  refine ⟨hleaves, (s (i + 1)).closeRoot (by simp [hleaves]), ?_⟩
  intro j hij ⟨mj, hmj⟩
  have hrec : (s j).record = [] := by
    rcases run_record_mono_stutter s hs (i + 1) j hij with heq | hlt
    · exact heq.trans hempty
    · exact (dmlt_not_nil _ (hempty ▸ hlt)).elim
  have := State.commit_credit_record (s j) (s (j + 1)) mj hmj
  rw [hrec] at this
  exact dmlt_not_nil _ this

theorem newLabels_nil_shape {S : State root} (m : Move S) (h : S.newLabels m = []) :
    S.leaves.length = 1 ∧ m.children = [] := by
  have hlen := congrArg List.length h
  simp only [State.newLabels, replaceList, List.length_append, List.length_take,
    List.length_map, List.length_drop, List.length_nil, State.length_leafLabels] at hlen
  have hp := m.pos.isLt
  have hmin : min m.pos.val S.leaves.length = m.pos.val := Nat.min_eq_left (Nat.le_of_lt hp)
  rw [hmin] at hlen
  refine ⟨by omega, ?_⟩
  have : m.children.length = 0 := by omega
  simpa using this

theorem creditOf_top_iff {S : State root} (m : Move S) (h : S.record = [.top]) :
    S.creditOf m = .certifiedEasier ↔
      S.leaves.length = 1 ∧ m.children = [] ∧
        (S.leafLabels = [.top] ∨ m.recordCert.isSome) := by
  constructor
  · intro hc
    have hd := State.creditOf_sound S m hc
    rw [h] at hd
    obtain ⟨hlen, hchildren⟩ := newLabels_nil_shape m ((dmlt_top_iff_nil _).mp hd)
    refine ⟨hlen, hchildren, ?_⟩
    unfold State.creditOf at hc
    split at hc
    · rename_i hb
      rw [Bool.or_eq_true, Bool.and_eq_true] at hb
      rcases hb with ⟨_, heq⟩ | hcert
      · exact .inl ((of_decide_eq_true heq).trans h)
      · exact .inr hcert
    · cases hc
  · rintro ⟨_, hchildren, heq | hcert⟩
    · unfold State.creditOf
      apply if_pos
      rw [Bool.or_eq_true, Bool.and_eq_true]
      exact .inl ⟨by simp [State.localEasier, hchildren], decide_eq_true (heq.trans h.symm)⟩
    · unfold State.creditOf
      apply if_pos
      rw [Bool.or_eq_true]
      exact .inr hcert

end CRRGClassical
