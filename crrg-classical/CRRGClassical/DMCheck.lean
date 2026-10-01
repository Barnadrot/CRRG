import CRRGClassical.Easier

/-!
# L-02: a computed DM checker and proof-producing record certificates

Cancel common occurrences using multiset subtraction. The residual record must be
nonempty, and every residual new label must be strictly below a residual record label.
Multiplicity is preserved; no linear ordering of different families or `top` is imposed.
-/

namespace CRRGClassical

open CRRGCore Multiset

/-- For disjoint supports, there can be no retained common part in a DM witness. -/
theorem dm_disjoint_iff (A B : Multiset Label) (hdis : ∀ a ∈ A, a ∉ B) :
    IsDershowitzMannaLT A B ↔ B ≠ 0 ∧ ∀ a ∈ A, ∃ b ∈ B, Label.lt a b := by
  constructor
  · rintro ⟨X, Y, Z, hZ, hA, hB, hYZ⟩
    have hX : X = 0 := by
      apply eq_zero_iff_forall_notMem.mpr
      intro x hx
      have hxA : x ∈ A := by rw [hA]; exact mem_add.mpr (.inl hx)
      have hxB : x ∈ B := by rw [hB]; exact mem_add.mpr (.inl hx)
      exact hdis x hxA hxB
    subst X
    simp only [zero_add] at hA hB
    subst Y Z
    exact ⟨hZ, hYZ⟩
  · rintro ⟨hB, hAB⟩
    exact ⟨0, A, B, hB, by simp, by simp, hAB⟩

/-- Cancel the entire intersection to obtain a finite residual comparison. -/
theorem dm_residual_iff (A B : Multiset Label) :
    IsDershowitzMannaLT A B ↔
      B - A ≠ 0 ∧ ∀ a ∈ A - B, ∃ b ∈ B - A, Label.lt a b := by
  have hB : B - A + A ∩ B = B := by rw [inter_comm, sub_add_inter]
  have hc := dm_add_cancel (A - B) (B - A) (A ∩ B)
  rw [sub_add_inter, hB] at hc
  apply hc.trans
  apply dm_disjoint_iff
  intro a ha hb
  exact Nat.lt_asymm (mem_sub.mp ha) (mem_sub.mp hb)

/-- Computed cancellation followed by finite bounded comparisons. -/
def dmCheck (new record : List Label) : Bool :=
  let added : Multiset Label := (new : Multiset Label) - (record : Multiset Label)
  let removed : Multiset Label := (record : Multiset Label) - (new : Multiset Label)
  letI : ∀ a : Label, Decidable (∃ b ∈ removed, Label.lt a b) :=
    fun _ => Multiset.decidableExistsMultiset
  letI : Decidable (∀ a ∈ added, ∃ b ∈ removed, Label.lt a b) :=
    Multiset.decidableForallMultiset
  decide (removed ≠ 0 ∧ ∀ a ∈ added, ∃ b ∈ removed, Label.lt a b)

theorem dmCheck_sound_complete (new record : List Label) :
    dmCheck new record = true ↔ DMLt new record := by
  unfold dmCheck
  simp only [decide_eq_true_eq, ← dm_residual_iff, dmlt_iff_isDM]

/-- Generate a kernel proof of the record decrease when the checker succeeds. -/
def dmCertificate (new record : List Label) : Option (PLift (DMLt new record)) :=
  if h : dmCheck new record = true then
    some ⟨(dmCheck_sound_complete new record).mp h⟩
  else none

theorem dmCertificate_isSome (new record : List Label) :
    (dmCertificate new record).isSome = true ↔ DMLt new record := by
  simpa [dmCertificate] using dmCheck_sound_complete new record

/-- Attach a computed gamma to an existing move, preserving its children and coverage. -/
def withComputedCert {root : Goal} {S : State root} (m : Move S) : Move S :=
  { m with recordCert := dmCertificate (S.newLabels m) S.record }

/-- With computed gamma, the existing credit rule detects every DM decrease. -/
theorem withComputedCert_credited_iff {root : Goal} {S : State root} (m : Move S) :
    S.creditOf (withComputedCert m) = .certifiedEasier ↔ DMLt (S.newLabels m) S.record := by
  constructor
  · intro h
    exact State.creditOf_sound S (withComputedCert m) h
  · intro h
    have hc := (dmCertificate_isSome (S.newLabels m) S.record).mpr h
    unfold State.creditOf
    apply if_pos
    rw [Bool.or_eq_true]
    exact .inr hc

end CRRGClassical
