import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
def move : Move (E1 3) :=
  Move.close (E1 3) ⟨0, Nat.zero_lt_one⟩ sorry
end Sub
