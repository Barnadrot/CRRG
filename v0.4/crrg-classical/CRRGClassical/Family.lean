import CRRGClassical.State
import CRRGExamples.CruxFamily

/-!
# CRRGClassical.Family — crux families on Mathlib objects

The crux-family object of crrg-core (`CRRGExamples.CruxFamily`), with its state on Mathlib objects:
- named escape leaves are a `Finset String`;
- regions are `Finset ℕ`, narrowed by `Region.admit`;
- the family's evidence is a `Finset String`.

The members, guards, `usable` and `Claim` are reused from crrg-core, so this is the same family.

Every theorem in the first part is *proved* **in general**, including order independence. For any
two evidence lists that are permutations of each other, admission gives the same family
(`admitAll_perm`). The synthetic instance at the end is one application (`demo_orders_agree`, by
`List.reverse_perm`, not by `decide`).
-/

namespace CRRGClassical

open CRRGCore CRRGExamples.CruxFamily

/-- An admitted result: the named leaves it closes and the intervals it bills on each region. -/
structure FamEvidence where
  id : String
  closes : Finset String
  xClosed : List (ℕ × ℕ)
  yClosed : List (ℕ × ℕ)

/-- A member's state: its named open leaves and its open regions. -/
structure FamMemberState where
  member : Member
  named : Finset String
  xOpen : Finset ℕ
  yOpen : Finset ℕ

/-- Admission narrows a member's leaves **only if the member can use the edge**. -/
def FamMemberState.admit (e : FamEvidence) (s : FamMemberState) : FamMemberState :=
  if usable s.member then
    { s with named := s.named \ e.closes, xOpen := Region.admit e.xClosed s.xOpen,
             yOpen := Region.admit e.yClosed s.yOpen }
  else s

/-- The family: its admitted evidence and its members' states. -/
structure ClassicalFamily where
  evidence : Finset String
  states : List FamMemberState

/-- One admitted result updates every member through the same function. -/
def ClassicalFamily.admit (e : FamEvidence) (F : ClassicalFamily) : ClassicalFamily :=
  ⟨insert e.id F.evidence, F.states.map (FamMemberState.admit e)⟩

/-- Admit a list of results, in order. -/
def ClassicalFamily.admitAll (F : ClassicalFamily) (es : List FamEvidence) : ClassicalFamily :=
  es.foldl (fun G e => G.admit e) F

/-! ## The member-update theorems, in general -/

/-- *proved*: a member whose guard fails cannot claim the edge. -/
theorem no_claim_without_guard' (m : Member) (h : ¬ guard m.inst) : ¬ Claim m :=
  no_claim_without_guard m h

/-- *proved*: every member is updated by the same rule. -/
theorem admit_pointwise' (e : FamEvidence) (F : ClassicalFamily) (i : ℕ) :
    (F.admit e).states[i]? = (F.states[i]?).map (FamMemberState.admit e) := by
  simp [ClassicalFamily.admit]

/-- *proved*: admission keeps the member list. -/
theorem admit_members' (e : FamEvidence) (F : ClassicalFamily) :
    (F.admit e).states.map (·.member) = F.states.map (·.member) := by
  simp only [ClassicalFamily.admit, List.map_map]
  congr 1
  funext s
  simp only [Function.comp_apply, FamMemberState.admit]
  split <;> rfl

/-- *proved*: a member that does not discharge the guard is untouched. -/
theorem admit_nondischarging' (e : FamEvidence) (s : FamMemberState) (h : ¬ guard s.member.inst) :
    s.admit e = s := by
  simp [FamMemberState.admit, usable, h]

/-- *proved*: an exclusion node is untouched, even when its guard holds. -/
theorem admit_exclusion' (e : FamEvidence) (s : FamMemberState) (h : s.member.kind = .exclusion) :
    s.admit e = s := by
  simp [FamMemberState.admit, usable, h]

/-- *proved*: admission never opens anything: named leaves and both regions only shrink. -/
theorem admit_monotone (e : FamEvidence) (s : FamMemberState) :
    (s.admit e).named ⊆ s.named ∧ (s.admit e).xOpen ⊆ s.xOpen ∧ (s.admit e).yOpen ⊆ s.yOpen := by
  unfold FamMemberState.admit
  split
  · exact ⟨Finset.sdiff_subset, Region.admit_subset _ _, Region.admit_subset _ _⟩
  · exact ⟨subset_rfl, subset_rfl, subset_rfl⟩

/-- *proved*: `admit_named_monotone` in crrg-core's form. -/
theorem admit_named_monotone' (e : FamEvidence) (s : FamMemberState) (n : String) :
    n ∈ (s.admit e).named → n ∈ s.named :=
  fun h => (admit_monotone e s).1 h

/-- *proved*: two admissions commute on each member. -/
theorem memberAdmit_comm (e₁ e₂ : FamEvidence) (s : FamMemberState) :
    (s.admit e₁).admit e₂ = (s.admit e₂).admit e₁ := by
  unfold FamMemberState.admit
  by_cases hu : usable s.member
  · simp only [hu, if_true]
    rw [sdiff_sdiff_comm, Region.admit_comm e₁.xClosed e₂.xClosed,
      Region.admit_comm e₁.yClosed e₂.yClosed]
  · simp only [hu, if_false]

/-- *proved*: **two admissions commute on the family**, in general. -/
theorem admit_comm (e₁ e₂ : FamEvidence) (F : ClassicalFamily) :
    (F.admit e₁).admit e₂ = (F.admit e₂).admit e₁ := by
  simp only [ClassicalFamily.admit, List.map_map]
  congr 1
  · exact Finset.insert_comm _ _ _
  · congr 1
    funext s
    exact memberAdmit_comm e₁ e₂ s

/-- *proved*: **admission order is irrelevant**. Admitting any permutation of the same evidence list
gives the same family. -/
theorem admitAll_perm {es₁ es₂ : List FamEvidence} (h : es₁.Perm es₂) (F : ClassicalFamily) :
    F.admitAll es₁ = F.admitAll es₂ := by
  induction h generalizing F with
  | nil => rfl
  | cons e _ ih => exact ih (F.admit e)
  | swap e₁ e₂ l =>
    simp only [ClassicalFamily.admitAll, List.foldl_cons]
    rw [admit_comm]
  | trans _ _ ih₁ ih₂ => exact (ih₁ F).trans (ih₂ F)

/-! ## A synthetic instance

The members and guard are crrg-core's synthetic ones (`CRRGExamples.CruxFamily.members`), and the
four results mirror its `ev1`–`ev4`. They model no particular problem. -/

/-- The open regions of a member that can use the edge, at registration. -/
def xOpen0 : Finset ℕ := Finset.Icc 0 99
def yOpen0 : Finset ℕ := Finset.Icc 0 49

/-- The named leaves of a member that can use the edge. -/
def usableNamed : Finset String := {"case-a", "case-b", "case-c"}

/-- The synthetic family at registration. Members that can use the edge start with the named leaves
and both regions; the others keep their own leaf. -/
def demo0 : ClassicalFamily :=
  ⟨∅, members.map fun m =>
    if usable m then ⟨m, usableNamed, xOpen0, yOpen0⟩
    else ⟨m, if guard m.inst then {"exclusion-form"} else {"own-instantiation"}, ∅, ∅⟩⟩

def ev1' : FamEvidence := ⟨"ev-1", {"case-a"}, [(60, 99)], []⟩
def ev2' : FamEvidence := ⟨"ev-2", {"case-b"}, [(0, 29), (25, 44)], []⟩
def ev3' : FamEvidence := ⟨"ev-3", ∅, [(45, 59)], []⟩
def ev4' : FamEvidence := ⟨"ev-4", ∅, [], [(30, 49)]⟩

/-- The order in which the results were admitted. -/
def evidenceOrder : List FamEvidence := [ev1', ev2', ev3', ev4']

/-- *proved*: the admitted order and its reverse give the **same family**, by `admitAll_perm` and
`List.reverse_perm` (not by `decide`). -/
theorem demo_orders_agree :
    demo0.admitAll evidenceOrder = demo0.admitAll evidenceOrder.reverse :=
  admitAll_perm (List.reverse_perm _).symm demo0

/-- *proved*: any order of the four results gives the same family. -/
theorem demo_any_order (es : List FamEvidence) (h : es.Perm evidenceOrder) :
    demo0.admitAll es = demo0.admitAll evidenceOrder :=
  admitAll_perm h demo0

/-- *proved*: after `ev-1` and `ev-2`, the `x` region is open exactly on `[45, 59]`. -/
theorem demo_x_after_two :
    Region.admit ev2'.xClosed (Region.admit ev1'.xClosed xOpen0) = Finset.Icc 45 59 := by
  simp only [ev1', ev2', xOpen0, Region.admit, List.foldl_cons, List.foldl_nil]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_Icc]
  omega

/-- *proved*: after `ev-1`, `ev-2` and `ev-3`, the `x` region is empty. -/
theorem demo_x_closed :
    Region.admit ev3'.xClosed
      (Region.admit ev2'.xClosed (Region.admit ev1'.xClosed xOpen0)) = ∅ := by
  simp only [ev1', ev2', ev3', xOpen0, Region.admit, List.foldl_cons, List.foldl_nil]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.notMem_empty, iff_false]
  omega

/-- *proved*: after `ev-4`, the `y` region stays open exactly on `[0, 29]`. -/
theorem demo_y_after : Region.admit ev4'.yClosed yOpen0 = Finset.Icc 0 29 := by
  simp only [ev4', yOpen0, Region.admit, List.foldl_cons, List.foldl_nil]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_Icc]
  omega

end CRRGClassical
