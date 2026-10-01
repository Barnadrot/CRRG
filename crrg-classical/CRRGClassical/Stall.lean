import CRRGClassical.State
import CRRGCore.Gate

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

/-! ## Part 2, M5: stutters and faithfully typed lane logs -/

theorem recordRun_of_stutter {root : Goal} (s : ℕ → State root)
    (hs : ∀ i, State.Advance (s i) (s (i + 1)) ∨ s (i + 1) = s i) :
    RecordRun (fun i => ((s i).record : Multiset Label)) := by
  intro i
  rcases hs i with hi | hi
  · rcases State.advance_record hi with heq | hlt
    · exact .inl (congrArg (fun l : List Label => (l : Multiset Label)) heq)
    · exact .inr (dmlt_iff_isDM.mp hlt)
  · exact .inl (congrArg (fun S : State root => (S.record : Multiset Label)) hi)

theorem no_infinite_credits_stutter {root : Goal} (s : ℕ → State root)
    (hs : ∀ i, State.Advance (s i) (s (i + 1)) ∨ s (i + 1) = s i) :
    ¬ ∀ i, ∃ j, i ≤ j ∧ State.Credited (s j) (s (j + 1)) := by
  intro h
  apply no_infinite_credits _ (recordRun_of_stutter s hs)
  intro i
  obtain ⟨j, hij, m, hm⟩ := h i
  exact ⟨j, hij, core_commit_classical _ _ m hm⟩

/-- Each lane outcome refers to its actual run step; new conflicts are fresh keys. -/
structure Faithful {root : Goal} (s : ℕ → State root) (π : ℕ → ℕ)
    (o : ℕ → Outcome) : Prop where
  credited : ∀ j, o j = .credited → State.Credited (s (π j)) (s (π j + 1))
  newConflict : ∀ j, o j = .newConflict →
    ∃ key ∈ (s (π j + 1)).conflicts, key ∉ (s (π j)).conflicts

theorem dichotomy {root : Goal} (s : ℕ → State root)
    (hs : ∀ i, State.Advance (s i) (s (i + 1)) ∨ s (i + 1) = s i)
    (π : ℕ → ℕ) (hπ : StrictMono π) (o : ℕ → Outcome) (hf : Faithful s π o) (k : ℕ) :
    (∃ T, ∀ t ≥ T, parked k (hist o t)) ∨
      ∀ N, ∃ j ≥ N, ∃ key ∈ (s (π j + 1)).conflicts, key ∉ (s (π j)).conflicts := by
  classical
  by_cases hconf : ∀ N, ∃ j ≥ N, ∃ key ∈ (s (π j + 1)).conflicts,
      key ∉ (s (π j)).conflicts
  · exact .inr hconf
  · left
    obtain ⟨N, hN⟩ := not_forall.mp hconf
    obtain ⟨M, hM⟩ := not_forall.mp (no_infinite_credits_stutter s hs)
    have hle : ∀ n, n ≤ π n := by
      intro n
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih => exact (Nat.succ_le_succ ih).trans (hπ (Nat.lt_succ_self n))
    apply eventually_parked o k
    refine ⟨max N M, fun j hj => ?_⟩
    cases ho : o j with
    | dry => rfl
    | newConflict => exact (hN ⟨j, le_of_max_le_left hj, hf.newConflict j ho⟩).elim
    | credited =>
      exact (hM ⟨π j, (le_of_max_le_right hj).trans (hle j), hf.credited j ho⟩).elim

/-- Fresh conflict outcomes carry actual certified refutations in the new registry. -/
theorem faithful_newConflict_refuted {root : Goal} {s : ℕ → State root}
    {π : ℕ → ℕ} {o : ℕ → Outcome} (hf : Faithful s π o) {j : ℕ}
    (ho : o j = .newConflict) :
    ∃ key ∈ (s (π j + 1)).conflicts,
      key ∉ (s (π j)).conflicts ∧ ¬ holds (s (π j + 1)).reg key := by
  obtain ⟨key, hk, hnew⟩ := hf.newConflict j ho
  exact ⟨key, hk, hnew, (s (π j + 1)).conflicts_sound key hk⟩

/-- Keys fresh at strictly later lane steps cannot repeat an earlier learned key. -/
theorem fresh_keys_distinct {root : Goal} (s : ℕ → State root)
    (hs : ∀ i, State.Advance (s i) (s (i + 1)) ∨ s (i + 1) = s i)
    (π : ℕ → ℕ) (hπ : StrictMono π) {i j a b : ℕ} (hij : i < j)
    (ha : a ∈ (s (π i + 1)).conflicts) (hb : b ∉ (s (π j)).conflicts) : a ≠ b := by
  intro heq
  subst b
  exact hb (State.run_conflicts_mono s hs (hπ hij) a ha)

/-- Progress at an actual lane attempt resets parking only at positive thresholds. -/
theorem lane_progress_unparks (o : ℕ → Outcome) (j k : ℕ) (hk : 1 ≤ k)
    (ho : (o j).progress = true) : ¬ parked k (hist o (j + 1)) :=
  progress_unparks hk (o j) ho (hist o j)

/-! ## Part 3, L-06: the designed gate's chronological lane projection -/

def gateOutcome : CRRGCore.AttemptOutcome → Outcome
  | .credited => .credited
  | .newConflict => .newConflict
  | .dry => .dry

/-- An infinite chronological, exhaustive projection of the actual appended lane entries. -/
structure LaneProjection {root : Goal} {P W : Type} (c : ℕ → Gate root P W)
    (lane : ℕ) (π : ℕ → ℕ) (entry : ℕ → Attempt) : Prop where
  increasing : StrictMono π
  lane_eq : ∀ j, (entry j).lane = lane
  logged : ∀ j, (c (π j + 1)).journal = (c (π j)).journal ++ [entry j]
  exhaustive : ∀ t e, (c (t + 1)).journal = (c t).journal ++ [e] → e.lane = lane →
    ∃ j, π j = t

theorem lane_projection_faithful {root : Goal} {P W : Type} {run}
    (c : ℕ → Gate root P W) (hc : ∀ n, Gate.Step run (c n) (c (n + 1)))
    (lane : ℕ) (π : ℕ → ℕ) (entry : ℕ → Attempt) (hp : LaneProjection c lane π entry) :
    Faithful (fun t => (c t).b) π (fun j => gateOutcome (entry j).outcome) := by
  constructor
  · intro j hj
    have hs := Gate.appended_event_sound (hc (π j)) (hp.logged j)
    cases he : (entry j).outcome <;> simp_all [gateOutcome, Gate.EventSound]
  · intro j hj
    have hs := Gate.appended_event_sound (hc (π j)) (hp.logged j)
    cases he : (entry j).outcome <;> simp_all [gateOutcome, Gate.EventSound]

/-- Proposition A.6 for the designed model and each infinite actual lane projection. -/
theorem gate_lane_dichotomy {root : Goal} {P W : Type} {run}
    (c : ℕ → Gate root P W) (hc : ∀ n, Gate.Step run (c n) (c (n + 1)))
    (lane : ℕ) (π : ℕ → ℕ) (entry : ℕ → Attempt) (hp : LaneProjection c lane π entry) (k : ℕ) :
    (∃ T, ∀ t ≥ T, parked k (hist (fun j => gateOutcome (entry j).outcome) t)) ∨
      ∀ N, ∃ j ≥ N, ∃ key ∈ (c (π j + 1)).b.conflicts, key ∉ (c (π j)).b.conflicts := by
  apply dichotomy (fun t => (c t).b) _ π hp.increasing _
    (lane_projection_faithful c hc lane π entry hp) k
  intro n
  exact (Gate.step_refines (hc n)).symm

end CRRGClassical
