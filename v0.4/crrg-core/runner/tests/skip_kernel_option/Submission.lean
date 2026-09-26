import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
set_option debug.skipKernelTC true
def move : Move (E1 8) :=
  Move.closeByComputation (E1 8) ⟨0, Nat.zero_lt_one⟩ (evenCert 8) rfl
end Sub
