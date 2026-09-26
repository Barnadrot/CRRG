import CRRGClassical.State

/-!
# CRRGClassical.Ledger — an evidence ledger for non-move results

The ledger holds results that are not frontier moves, typed:
- **lower-bound witnesses**;
- **exact identities** (the statement and its proof);
- **vacuity diagnoses**;
- **obstructions**.

Recording is append-only and timestamped. It **never changes the frontier or the credit** (*proved*:
recording leaves the route's `State` untouched, so leaves, conflicts, record and `easierCount` are
unchanged). Entries stay **citable as a new ingredient**. Once a method family's price leaf is refuted,
a re-priced proposal in that family is admitted to the kernel step only if it cites a ledger entry
recorded **after** the refutation (the new-ingredient gate).
-/

namespace CRRGClassical

open CRRGCore

/-- A ledger entry, typed. -/
inductive Entry where
  /-- An exhibited list of `size` members at `radius` on `instance_`. -/
  | lowerBound (instance_ : String) (radius size : ℕ) (source : String)
  /-- An exact identity: the statement and its proof. -/
  | identity (name : String) (statement : Prop) (proof : statement) (source : String)
  /-- A vacuity diagnosis of a hypothesis. -/
  | diagnosis (hypothesis verdict source : String)
  /-- An obstruction to a method. -/
  | obstruction (method formula source : String)

/-- A route with its ledger and a clock. -/
structure LedgeredRoute (root : Goal) where
  state : State root
  ledger : List (ℕ × Entry)
  clock : ℕ

/-- Record an entry at the current time. -/
def LedgeredRoute.record {root : Goal} (R : LedgeredRoute root) (e : Entry) : LedgeredRoute root :=
  ⟨R.state, (R.clock, e) :: R.ledger, R.clock + 1⟩

/-- *proved*: **recording never changes the frontier or the credit**. The route's state is untouched,
so its leaves, conflicts, record and `easierCount` are unchanged. -/
theorem record_state {root : Goal} (R : LedgeredRoute root) (e : Entry) :
    (R.record e).state = R.state := rfl

theorem record_frontier_credit {root : Goal} (R : LedgeredRoute root) (e : Entry) :
    (R.record e).state.leaves = R.state.leaves ∧ (R.record e).state.conflicts = R.state.conflicts ∧
    (R.record e).state.easierCount = R.state.easierCount ∧
    (R.record e).state.record = R.state.record := ⟨rfl, rfl, rfl, rfl⟩

/-- *proved*: any sequence of recordings leaves the state unchanged. -/
theorem recordAll_state {root : Goal} (R : LedgeredRoute root) (es : List Entry) :
    (es.foldl LedgeredRoute.record R).state = R.state := by
  induction es generalizing R with
  | nil => rfl
  | cons e es ih => exact ih (R.record e)

/-- A method proposal in a family: its price leaf and an optional cited ledger entry (by time). -/
structure Proposal where
  family : String
  price : Prop
  ingredient : Option ℕ

/-- The new-ingredient gate. If the family's price leaf was refuted at time `t`, the proposal must
cite a ledger entry recorded after `t`. -/
def admitProposal {root : Goal} (R : LedgeredRoute root) (refutedAt : String → Option ℕ)
    (p : Proposal) : Bool :=
  match refutedAt p.family with
  | none => true
  | some t =>
    match p.ingredient with
    | none => false
    | some i => decide (t < i) && R.ledger.any (fun e => e.1 == i)

/-- *proved*: after a refutation, a proposal with no ingredient is refused. -/
theorem no_ingredient_refused {root : Goal} (R : LedgeredRoute root) (refutedAt : String → Option ℕ)
    (p : Proposal) (t : ℕ) (ht : refutedAt p.family = some t) (hi : p.ingredient = none) :
    admitProposal R refutedAt p = false := by
  simp [admitProposal, ht, hi]

/-- *proved*: an admitted re-priced proposal cites a ledger entry recorded after the refutation. -/
theorem admitted_cites_new {root : Goal} (R : LedgeredRoute root) (refutedAt : String → Option ℕ)
    (p : Proposal) (t : ℕ) (ht : refutedAt p.family = some t)
    (h : admitProposal R refutedAt p = true) :
    ∃ i, p.ingredient = some i ∧ t < i ∧ ∃ e, (i, e) ∈ R.ledger := by
  simp only [admitProposal, ht] at h
  cases hi : p.ingredient with
  | none => simp [hi] at h
  | some i =>
    simp only [hi, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at h
    obtain ⟨hti, ⟨⟨j, e⟩, hmem, rfl⟩⟩ := h
    exact ⟨j, rfl, hti, e, hmem⟩

/-- *proved*: the gate is a pure check; it never changes the route (the kernel commit still decides). -/
theorem admitProposal_pure {root : Goal} (R : LedgeredRoute root) (refutedAt : String → Option ℕ)
    (p : Proposal) : (if admitProposal R refutedAt p then R else R) = R := by
  split <;> rfl

end CRRGClassical
