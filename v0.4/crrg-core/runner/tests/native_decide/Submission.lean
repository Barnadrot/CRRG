import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
def move : Move (E1 8) :=
  Move.close (E1 8) ⟨0, Nat.zero_lt_one⟩ (show 8 % 2 = 0 by native_decide)
end Sub
