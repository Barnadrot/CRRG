import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
#eval (2 + 2 : Nat)
def move : Move (E1 8) :=
  Move.closeByComputation (E1 8) ⟨0, Nat.zero_lt_one⟩ (evenCert 8) rfl
end Sub
