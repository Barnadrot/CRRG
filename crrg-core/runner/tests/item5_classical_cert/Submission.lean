import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
noncomputable def classicalCert (p : Prop) : MechCert ⟨p⟩ where
  decide _ := @decide p (Classical.propDecidable p)
  sound_true h := @of_decide_eq_true p (Classical.propDecidable p) h
  sound_false h := @of_decide_eq_false p (Classical.propDecidable p) h
def move : Move (E1 8) :=
  Move.closeByComputation (E1 8) ⟨0, Nat.zero_lt_one⟩ (classicalCert _) rfl
end Sub
