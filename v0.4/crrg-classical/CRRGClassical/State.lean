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

end CRRGClassical
