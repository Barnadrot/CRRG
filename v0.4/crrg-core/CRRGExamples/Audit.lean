import CRRGExamples.Negatives
import CRRGTools

/-!
# Examples 8–12: the meta audits, the private constructor, and the capstone route

Negative controls are wrapped in `#guard_msgs`, so the *failure* itself is checked by the build.
If a control ever stopped failing, the build would break.
-/

namespace CRRGExamples

open CRRGCore CRRGTools

/-! ## 8. Rung 2 audit (informational): a real decision procedure passes; classical placeholders fail

Rung 2 is settled in the kernel (`Move.closeByComputation … rfl`, example 3). This audit only reports
on the certificate's own definition. -/

#crrg_check_mech evenCert

/-- A vacuous "decision procedure" built from classical decidability. -/
noncomputable def badCert (p : Prop) : MechCert ⟨p⟩ where
  decide _ := @decide p (Classical.propDecidable p)
  sound_true h := @of_decide_eq_true p (Classical.propDecidable p) h
  sound_false h := @of_decide_eq_false p (Classical.propDecidable p) h

/-- error: crrg: CRRGExamples.badCert is noncomputable, so it is not a rung-2 decision procedure -/
#guard_msgs in
#crrg_check_mech badCert

/-- Computable, but its proof uses `Classical.choice` (via `Classical.byContradiction`). -/
def choiceCert : MechCert ⟨True⟩ where
  decide _ := true
  sound_true _ := Classical.byContradiction fun h => h trivial
  sound_false h := absurd h (by decide)

/-- error: crrg: CRRGExamples.choiceCert depends on Classical.choice, so it is not a rung-2 decision procedure -/
#guard_msgs in
#crrg_check_mech choiceCert

/-! ## 9. Restatement detection (D1) and kernel-term seals -/

#crrg_assert_restatement ListBound ClassCap

/-- error: crrg: CRRGExamples.ListBound and CRRGExamples.R are not definitionally equal -/
#guard_msgs in
#crrg_assert_restatement ListBound R

/- The seals of `ListBound` and `ClassCap` differ: seals identify kernel terms, while D1 detects
definitional restatements. The two are complementary. -/
#crrg_seal ListBound
#crrg_seal ClassCap

/-! ## 10. R1 on definitions: a new definition needs an agreement lemma with the sealed ones -/

namespace Sealed
/-- A sealed root definition (a stand-in for a frozen target definition). -/
def Bound (n : Nat) : Prop := n + 0 = n
end Sealed

/-- A new definition introduced by a transition. -/
def NewQuantity (n : Nat) : Prop := 0 + n = n

/-- A leaf stated through the new definition. -/
def Leaf : Prop := ∀ n, NewQuantity n

/-- error: crrg: definitions without a sealed namespace or a typed agreement lemma: [CRRGExamples.NewQuantity] -/
#guard_msgs in
#crrg_check_defs Leaf [CRRGExamples.Sealed]

/-- A vacuous "agreement" that never mentions a sealed definition: it does not count. -/
@[crrg_agree] theorem newQuantity_vacuous (n : Nat) : NewQuantity n → True := fun _ => trivial

/-- error: crrg: definitions without a sealed namespace or a typed agreement lemma: [CRRGExamples.NewQuantity] -/
#guard_msgs in
#crrg_check_defs Leaf [CRRGExamples.Sealed]

/-- The review's forgery (item 8): a conjunction of two tautologies mentions both names but relates
nothing. Under the typed rule it does not count. -/
@[crrg_agree] theorem newQuantity_fake (n : Nat) :
    (NewQuantity n → NewQuantity n) ∧ (Sealed.Bound n → Sealed.Bound n) := ⟨id, id⟩

/-- error: crrg: definitions without a sealed namespace or a typed agreement lemma: [CRRGExamples.NewQuantity] -/
#guard_msgs in
#crrg_check_defs Leaf [CRRGExamples.Sealed]

/-- The agreement lemma: the new definition agrees with the sealed one. -/
@[crrg_agree] theorem newQuantity_agree (n : Nat) : NewQuantity n ↔ Sealed.Bound n :=
  ⟨fun _ => rfl, fun _ => Nat.zero_add n⟩

#crrg_check_defs Leaf [CRRGExamples.Sealed]

/-! ## 11. Lineage by construction: states cannot be forged outside `CRRGCore.State` -/

/-- error: Unknown constant `CRRGCore.State.mk` -/
#guard_msgs in
example : State ⟨True⟩ := State.mk [] [] [] [] [] 0 0 [] sorry sorry sorry sorry sorry sorry

/-- error: invalid {...} notation, constructor for `State` is marked as private -/
#guard_msgs in
example : State ⟨True⟩ :=
  { fams := [], reg := [], leaves := [], conflicts := [], history := [], easierCount := 0,
    commitCount := 0, record := [], root_key := sorry, leaves_valid := sorry, conflicts_valid := sorry,
    conflicts_sound := sorry, closeRoot := sorry, history_ok := sorry }

/- The legitimate examples pass the lineage audit: nothing outside `CRRGCore` names a private core
declaration. `CRRGExamples/Lineage.lean` shows the audit catching a metaprogrammed forgery. -/
#crrg_check_lineage

/-! ## 11b. D1 at admission (review item 6): the runner's `#crrg_admit` step -/

/-- A definitional restatement of the refuted `1 = 2`, under a new name. -/
def OneEqTwo : Prop := 1 = 2

def readmitDefeq : Move F2 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new ⟨⟨OneEqTwo⟩, .top, trivial⟩]
  cover h := by
    have h1 : OneEqTwo := h _ (List.mem_singleton.mpr rfl)
    exact absurd (show 1 = 2 from h1) (by decide)

/-- The kernel's key check alone would accept it under a new key… -/
example : tagOf? (State.commit F2 readmitDefeq) = some .notCertifiedEasier := rfl

/- …so the runner runs D1 at admission, which rejects it against learned conflict 1. -/
/-- error: crrg admission: fresh claim OneEqTwo is definitionally equal to learned conflict 1 -/
#guard_msgs in
#crrg_admit F2 readmitDefeq

/- A propositional (not definitional) restatement passes D1; `learn` handles it (example 5, F4). -/
#crrg_admit F2 readmitRestated

/-- A fresh claim definitionally equal to a live registered obligation is reported for key reuse. -/
def restateR : Move F2 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new ⟨⟨R⟩, .top, trivial⟩]
  cover h := h _ (List.mem_singleton.mpr rfl)

#crrg_admit F2 restateR

/-! ## 12. The route's root is the capstone -/

/-- Stand-in for a frozen target statement at parameter `d`. -/
def Capstone (d : Nat) : Prop := d ≤ 10

/-- Any route at `d = 7` that closes proves exactly `Capstone 7`. -/
example (R : CertRoute Capstone 7) (h : R.frontier.AllClosed) : Capstone 7 := R.closes h

/-- A route at `d = 7`, closed in one move. -/
def route7 : CertRoute Capstone 7 :=
  stateOr (State.commit (State.initial ⟨Capstone 7⟩ [])
    (Move.close _ ⟨0, Nat.zero_lt_one⟩ (show 7 ≤ 10 by decide))) (State.initial ⟨Capstone 7⟩ [])

example : route7.leaves = [] := rfl

/-- The capstone at `d = 7`, obtained from the closed route. -/
example : Capstone 7 :=
  route7.closes ((State.allClosed_iff route7).mpr fun k hk => by
    have h : route7.leaves = [] := rfl
    rw [h] at hk
    cases hk)

end CRRGExamples
