import CRRGCore.State

/-! L-06: a designed atomic gate, not a proof about the deployed implementation. -/
namespace CRRGCore

inductive AttemptOutcome where
  | credited | newConflict | dry
  deriving DecidableEq, Repr

structure Attempt where
  id : Nat
  lane : Nat
  outcome : AttemptOutcome
  verdict : Option Tag
  deriving Repr

structure Gate (root : Goal) (P W : Type) where
  b : State root
  queue : List P
  work : W
  journal : List Attempt

namespace Gate

variable {root : Goal} {P W : Type}

def tagOutcome : Tag → AttemptOutcome
  | .certifiedEasier => .credited
  | .notCertifiedEasier => .dry

def negativeOutcome (S : State root) (key : Nat) : AttemptOutcome :=
  if S.conflicts.contains key then .dry else .newConflict

def logEntry (c : Gate root P W) (lane : Nat) (outcome : AttemptOutcome)
    (verdict : Option Tag := none) : List Attempt :=
  c.journal ++ [⟨c.journal.length, lane, outcome, verdict⟩]

inductive Step (run : P → (b : State root) → Option (Move b)) :
    Gate root P W → Gate root P W → Prop
  | work {c} (w : W) (ps : List P) : Step run c { c with work := w, queue := c.queue ++ ps }
  | crash {c} (w : W) : Step run c { c with work := w, queue := [] }
  | skip {c} : Step run c c
  | accept {c} (lane : Nat) (p : P) (ps : List P) (hq : c.queue = p :: ps)
      (m : Move c.b) (hm : run p c.b = some m) (b' : State root) (t : Tag)
      (hc : State.commit c.b m = .ok (b', t)) :
      Step run c { c with b := b', queue := ps, journal := logEntry c lane (tagOutcome t) (some t) }
  | reject {c} (lane : Nat) (p : P) (ps : List P) (hq : c.queue = p :: ps)
      (hr : ∀ m, run p c.b = some m → ∀ b' t, State.commit c.b m ≠ .ok (b', t)) :
      Step run c { c with queue := ps, journal := logEntry c lane .dry }
  | refute {c} (lane : Nat) (i : Fin c.b.leaves.length) (h : ¬ (c.b.leafGoal i).claim) :
      Step run c { c with
        b := c.b.refute i h
        journal := logEntry c lane (negativeOutcome c.b c.b.leaves[i]) }
  | learn {c} (lane k' : Nat) (hk' : k' < c.b.reg.length) (k : Nat)
      (hk : k ∈ c.b.conflicts) (imp : holds c.b.reg k' → holds c.b.reg k) :
      Step run c { c with
        b := c.b.learn k' hk' k hk imp
        journal := logEntry c lane (negativeOutcome c.b k') }

def Init (fams : List Family) (ℓ₀ : Label) (h : LabelOK fams root ℓ₀)
    (c : Gate root P W) : Prop :=
  c.b = State.initial root fams ℓ₀ h ∧ c.queue = [] ∧ c.journal = []

theorem step_refines {run} {c c' : Gate root P W} (h : Step run c c') :
    c'.b = c.b ∨ State.Advance c.b c'.b := by
  cases h with
  | work => exact .inl rfl
  | crash => exact .inl rfl
  | skip => exact .inl rfl
  | accept lane p ps hq m hm b' t hc => exact .inr (.commit m t b' hc)
  | reject => exact .inl rfl
  | refute lane i h => exact .inr (.refute i h)
  | learn lane k' hk' k hk imp => exact .inr (.learn k' hk' k hk imp)

theorem refines {run} {fams : List Family} {ℓ₀ : Label} {h : LabelOK fams root ℓ₀}
    (c : Nat → Gate root P W) (h0 : Init fams ℓ₀ h (c 0))
    (hc : ∀ n, Step run (c n) (c (n + 1))) :
    (c 0).b = State.initial root fams ℓ₀ h ∧
      ∀ n, (c (n + 1)).b = (c n).b ∨ State.Advance (c n).b (c (n + 1)).b :=
  ⟨h0.1, fun n => step_refines (hc n)⟩

theorem records_mono {run} (c : Nat → Gate root P W)
    (hc : ∀ n, Step run (c n) (c (n + 1))) (i j : Nat) (hij : i ≤ j) :
    (c j).b.record = (c i).b.record ∨ DMLt (c j).b.record (c i).b.record := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact .inl rfl
  | succ j ih =>
    by_cases hle : i ≤ j
    · have ih := ih hle
      have hn : (c (j + 1)).b.record = (c j).b.record ∨
          DMLt (c (j + 1)).b.record (c j).b.record := by
        rcases step_refines (hc j) with heq | ha
        · exact .inl (congrArg State.record heq)
        · exact State.advance_record ha
      rcases hn with heq | hlt
      · rwa [heq]
      · right
        rcases ih with heq | hlt'
        · rwa [heq] at hlt
        · exact Relation.TransGen.trans hlt hlt'
    · have : i = j + 1 := by omega
      subst i; exact .inl rfl

theorem no_infinite_credits {run} (c : Nat → Gate root P W)
    (hc : ∀ n, Step run (c n) (c (n + 1))) :
    ¬ ∀ i, ∃ j, i ≤ j ∧ State.Credited (c j).b (c (j + 1)).b := by
  intro hinf
  have key : ∀ r, Acc DMLt r → ∀ i, (c i).b.record = r → False := by
    intro r hr
    induction hr with
    | intro r _ ih =>
      intro i hi
      obtain ⟨j, hij, m, hm⟩ := hinf i
      have hd := State.commit_credit_record (c j).b (c (j + 1)).b m hm
      apply ih (c (j + 1)).b.record _ (j + 1) rfl
      rw [← hi]
      rcases records_mono c hc i j hij with heq | hlt
      · rwa [← heq]
      · exact Relation.TransGen.trans hd hlt
  exact key _ (DMLt.wf.apply _) 0 rfl

def EventSound (S T : State root) : AttemptOutcome → Prop
  | .credited => State.Credited S T
  | .newConflict => ∃ key ∈ T.conflicts, key ∉ S.conflicts
  | .dry => True

theorem negative_event_sound {S T : State root} (key : Nat)
    (ht : T.conflicts = key :: S.conflicts) : EventSound S T (negativeOutcome S key) := by
  unfold negativeOutcome
  split
  · trivial
  · rename_i hn
    exact ⟨key, by simp [ht], by simpa using hn⟩

theorem step_journal {run} {c c' : Gate root P W} (h : Step run c c') :
    c'.journal = c.journal ∨ ∃ e : Attempt,
      e.id = c.journal.length ∧ c'.journal = c.journal ++ [e] ∧ EventSound c.b c'.b e.outcome := by
  cases h with
  | work => exact .inl rfl
  | crash => exact .inl rfl
  | skip => exact .inl rfl
  | accept lane p ps hq m hm b' t hc =>
    refine .inr ⟨_, rfl, rfl, ?_⟩
    cases t with
    | certifiedEasier => exact ⟨m, hc⟩
    | notCertifiedEasier => trivial
  | reject => exact .inr ⟨_, rfl, rfl, trivial⟩
  | refute lane i h => exact .inr ⟨_, rfl, rfl, negative_event_sound _ rfl⟩
  | learn lane k' hk' k hk imp => exact .inr ⟨_, rfl, rfl, negative_event_sound _ rfl⟩

theorem appended_event_sound {run} {c c' : Gate root P W} {e : Attempt}
    (h : Step run c c') (he : c'.journal = c.journal ++ [e]) : EventSound c.b c'.b e.outcome := by
  rcases step_journal h with hz | ⟨e', _, he', hs⟩
  · have := congrArg List.length (hz.symm.trans he)
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    exact (Nat.ne_of_lt (Nat.lt_succ_self _) this).elim
  · have heq : e' = e := by simpa using List.append_cancel_left (he'.symm.trans he)
    subst e'; exact hs

def JournalOK (c : Gate root P W) : Prop := c.journal.map Attempt.id = List.range c.journal.length

theorem step_journal_ok {run} {c c' : Gate root P W} (h : Step run c c')
    (hok : JournalOK c) : JournalOK c' := by
  rcases step_journal h with heq | ⟨e, hid, heq, _⟩
  · simpa [JournalOK, heq] using hok
  · simpa [JournalOK, heq, hid, List.range_succ] using hok

theorem run_journal_ok {run} (c : Nat → Gate root P W)
    (hc : ∀ n, Step run (c n) (c (n + 1))) (h0 : (c 0).journal = []) :
    ∀ n, JournalOK (c n) := by
  intro n
  induction n with
  | zero => simp [JournalOK, h0]
  | succ n ih => exact step_journal_ok (hc n) ih

theorem journal_ids_unique {c : Gate root P W} (h : JournalOK c) :
    (c.journal.map Attempt.id).Nodup := by
  rw [h]
  have hr : ∀ n, (List.range n).Nodup := by
    intro n
    induction n with
    | zero => exact List.Pairwise.nil
    | succ n ih =>
      rw [List.range_succ]
      apply List.pairwise_append.mpr
      refine ⟨ih, List.Pairwise.cons (fun _ h => by cases h) List.Pairwise.nil, ?_⟩
      intro a ha b hb
      have hb : b = n := List.mem_singleton.mp hb
      subst b
      exact Nat.ne_of_lt (List.mem_range.mp ha)
  exact hr _

/-- Value-based judging: one occurrence also witnesses judging of equal queued values. -/
def Judges (run : P → (b : State root) → Option (Move b)) (p : P)
    (c c' : Gate root P W) : Prop :=
  c.queue.head? = some p ∧ c'.queue = c.queue.tail ∧
    c'.journal.length = c.journal.length + 1 ∧ Step run c c'

/-- Deterministically judge the head on lane zero; once empty, stutter. -/
def pump (run : P → (b : State root) → Option (Move b)) (c : Gate root P W) : Gate root P W :=
  match c.queue with
  | [] => c
  | p :: ps =>
    match run p c.b with
    | none => { c with queue := ps, journal := logEntry c 0 .dry }
    | some m =>
      match State.commit c.b m with
      | .error _ => { c with queue := ps, journal := logEntry c 0 .dry }
      | .ok (b', t) =>
        { c with b := b', queue := ps, journal := logEntry c 0 (tagOutcome t) (some t) }

theorem pump_step (run : P → (b : State root) → Option (Move b)) (c : Gate root P W) :
    Step run c (pump run c) := by
  cases hq : c.queue with
  | nil => simpa [pump, hq] using (Step.skip (run := run) (c := c))
  | cons p ps =>
    cases hr : run p c.b with
    | none =>
      have hs : Step run c { c with queue := ps, journal := logEntry c 0 .dry } :=
        Step.reject 0 p ps hq (by intro m hm; rw [hr] at hm; cases hm)
      simpa [pump, hq, hr] using hs
    | some m =>
      cases hc : State.commit c.b m with
      | error e =>
        have hs : Step run c { c with queue := ps, journal := logEntry c 0 .dry } :=
          Step.reject 0 p ps hq (by
            intro m' hm b' t hh
            have : m' = m := Option.some.inj (hm.symm.trans hr)
            subst m'
            rw [hc] at hh; cases hh)
        simpa [pump, hq, hr, hc] using hs
      | ok result =>
        obtain ⟨b', t⟩ := result
        simpa [pump, hq, hr, hc] using Step.accept 0 p ps hq m hr b' t hc

theorem pump_queue (run : P → (b : State root) → Option (Move b)) (c : Gate root P W) :
    (pump run c).queue = c.queue.tail := by
  cases hq : c.queue with
  | nil => simp [pump, hq]
  | cons p ps =>
    cases hr : run p c.b with
    | none => simp [pump, hq, hr]
    | some m => cases hc : State.commit c.b m <;> simp [pump, hq, hr, hc]

theorem pump_judges (run : P → (b : State root) → Option (Move b)) (c : Gate root P W)
    (p : P) (hp : c.queue.head? = some p) : Judges run p c (pump run c) := by
  refine ⟨hp, pump_queue run c, ?_, pump_step run c⟩
  cases hq : c.queue with
  | nil => simp [hq] at hp
  | cons q qs =>
    cases hr : run q c.b with
    | none => simp [pump, hq, hr, logEntry]
    | some m => cases hc : State.commit c.b m <;> simp [pump, hq, hr, hc, logEntry]

def drain (run : P → (b : State root) → Option (Move b)) (c : Gate root P W) : Nat → Gate root P W
  | 0 => c
  | n + 1 => pump run (drain run c n)

theorem drain_step (run : P → (b : State root) → Option (Move b)) (c : Gate root P W) (n : Nat) :
    Step run (drain run c n) (drain run c (n + 1)) := pump_step run _

theorem drain_queue (run : P → (b : State root) → Option (Move b)) (c : Gate root P W) (n : Nat) :
    (drain run c n).queue = c.queue.drop n := by
  induction n with
  | zero => simp [drain]
  | succ n ih => simp only [drain, pump_queue, ih, List.tail_drop]

theorem drain_fair (run : P → (b : State root) → Option (Move b)) (c : Gate root P W)
    (i : Nat) (p : P) (hp : p ∈ (drain run c i).queue) :
    ∃ j ≥ i, Judges run p (drain run c j) (drain run c (j + 1)) := by
  rw [drain_queue] at hp
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp
  refine ⟨i + k, by omega, pump_judges run _ p ?_⟩
  rw [drain_queue, ← List.drop_drop, List.head?_drop]
  exact hk

theorem fair_extension {run} (n : Nat) (c : Nat → Gate root P W)
    (hc : ∀ i < n, Step run (c i) (c (i + 1))) :
    ∃ d : Nat → Gate root P W, (∀ i ≤ n, d i = c i) ∧
      (∀ i, Step run (d i) (d (i + 1))) ∧
      ∀ i ≥ n, ∀ p ∈ (d i).queue, ∃ j ≥ i, Judges run p (d j) (d (j + 1)) := by
  let d : Nat → Gate root P W := fun t => if t < n then c t else drain run (c n) (t - n)
  have hkeep : ∀ i ≤ n, d i = c i := by
    intro i hi
    by_cases hlt : i < n
    · simp [d, hlt]
    · have : i = n := by omega
      subst i; simp [d, drain]
  have htail : ∀ i, n ≤ i → d i = drain run (c n) (i - n) := by
    intro i hi
    simp [d, show ¬ i < n by omega]
  refine ⟨d, hkeep, ?_, ?_⟩
  · intro i
    by_cases hi : i < n
    · rw [hkeep i (by omega), hkeep (i + 1) (by omega)]
      exact hc i hi
    · rw [htail i (by omega), htail (i + 1) (by omega)]
      have he : i + 1 - n = (i - n) + 1 := by omega
      rw [he]
      exact drain_step run (c n) (i - n)
  · intro i hi p hp
    rw [htail i hi] at hp
    obtain ⟨j, hij, hj⟩ := drain_fair run (c n) (i - n) p hp
    refine ⟨n + j, by omega, ?_⟩
    rw [htail (n + j) (by omega), htail (n + j + 1) (by omega)]
    simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using hj

end Gate
end CRRGCore
