import CRRGClassical.State

/-!
# CRRGClassical.Stall — a stall and exit rule per crux

Each delivered contract on a crux (or on one lane of it) has a typed outcome:
- `credited`: a certified-easier commit;
- `newConflict`: a new learned conflict (a refutation);
- `dry`: neither. Admitted but uncredited moves, rejected proposals, and ledger-only results
  (witnesses, identities, diagnoses) are all dry: the ledger is never counted as progress.

The **streak** is the number of dry outcomes since the last progress, and a crux **parks** at streak
`≥ k`. Parking is a predicate on the outcome log. It never touches the route's state.

*Proved*:
- parking implies the last `k` contracts earned no credit and no conflict (`parked_last_dry`);
- a credit or a conflict always unparks (`progress_unparks`);
- a run with only finitely many progress steps eventually parks (`eventually_parked`);
- **compatibility with `no_infinite_credits`**: on a core run, a crux that never parks must keep producing
  new learned conflicts forever (`unparked_needs_conflicts`). Credits alone cannot keep it open, and
  parking cannot hide credit, because every credit resets the streak.
-/

namespace CRRGClassical

open CRRGCore

/-- A delivered contract's typed outcome. -/
inductive Outcome where
  | credited | newConflict | dry
  deriving DecidableEq, Repr

/-- Progress: a credit or a new learned conflict. -/
def Outcome.progress : Outcome → Bool
  | .dry => false
  | _ => true

/-- The streak of a log, newest first: dry outcomes since the last progress. -/
def streak : List Outcome → ℕ
  | [] => 0
  | o :: rest => if o.progress then 0 else streak rest + 1

/-- A crux parks at streak `≥ k`. -/
def parked (k : ℕ) (log : List Outcome) : Prop := k ≤ streak log

instance (k : ℕ) (log : List Outcome) : Decidable (parked k log) := by
  unfold parked; infer_instance

/-- *proved*: a credit or a conflict unparks (for `k ≥ 1`). -/
theorem progress_unparks {k : ℕ} (hk : 1 ≤ k) (o : Outcome) (ho : o.progress = true)
    (log : List Outcome) : ¬ parked k (o :: log) := by
  simp [parked, streak, ho]; omega

/-- *proved*: parked means the last `k` contracts were all dry: no credit and no conflict. -/
theorem parked_last_dry : ∀ (k : ℕ) (log : List Outcome), parked k log →
    ∀ i < k, log[i]? = some .dry
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, [], h, _, _ => by simp [parked, streak] at h
  | k + 1, o :: rest, h, i, hi => by
    unfold parked streak at h
    split at h
    · omega
    · rename_i hp
      have ho : o = .dry := by cases o <;> simp_all [Outcome.progress]
      cases i with
      | zero => simp [ho]
      | succ i =>
        have := parked_last_dry k rest (by unfold parked; omega) i (by omega)
        simpa using this

/-- The history of an outcome sequence up to `t`, newest first. -/
def hist (o : ℕ → Outcome) : ℕ → List Outcome
  | 0 => []
  | t + 1 => o t :: hist o t

theorem streak_hist_ge (o : ℕ → Outcome) (N : ℕ) (hN : ∀ i ≥ N, o i = .dry) :
    ∀ t, N ≤ t → t - N ≤ streak (hist o t) := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    rcases Nat.eq_or_lt_of_le ht with h | h
    · rw [← h]; simp
    · have := ih (by omega)
      simp only [hist, streak, hN t (by omega), Outcome.progress]
      simp; omega

/-- *proved*: finitely many progress steps means the crux eventually parks. -/
theorem eventually_parked (o : ℕ → Outcome) (k : ℕ) (hfin : ∃ N, ∀ i ≥ N, o i = .dry) :
    ∃ T, ∀ t ≥ T, parked k (hist o t) := by
  obtain ⟨N, hN⟩ := hfin
  exact ⟨N + k, fun t ht => by
    have := streak_hist_ge o N hN t (by omega)
    unfold parked; omega⟩

/-- *proved*: **compatibility with `no_infinite_credits`.** On a core run whose `credited` outcomes are
credited commits, a crux that never parks has new learned conflicts beyond every index. Credit alone
cannot keep a stalled crux open, and parking cannot hide a credit (`progress_unparks`). -/
theorem unparked_needs_conflicts {root : Goal} (s : ℕ → State root)
    (hs : ∀ i, State.Advance (s i) (s (i + 1))) (o : ℕ → Outcome)
    (ho : ∀ i, o i = .credited → State.Credited (s i) (s (i + 1))) (k : ℕ)
    (hopen : ∀ T, ∃ t ≥ T, ¬ parked k (hist o t)) :
    ∀ N, ∃ i ≥ N, o i = .newConflict := by
  intro N
  by_contra hno
  push Not at hno
  apply no_infinite_credits_state s hs
  intro M
  by_contra hM
  push Not at hM
  obtain ⟨T, hT⟩ := eventually_parked o k ⟨max N M, fun i hi => by
    have h1 := hno i (le_of_max_le_left hi)
    cases hoi : o i with
    | dry => rfl
    | newConflict => exact absurd hoi h1
    | credited => exact absurd (ho i hoi) (hM i (le_of_max_le_right hi))⟩
  obtain ⟨t, ht, hnp⟩ := hopen T
  exact hnp (hT t ht)

end CRRGClassical
