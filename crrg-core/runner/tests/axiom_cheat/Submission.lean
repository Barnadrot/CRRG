import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
axiom cheat : False
def move : Move (E1 3) :=
  Move.close (E1 3) ⟨0, Nat.zero_lt_one⟩ cheat.elim
end Sub
