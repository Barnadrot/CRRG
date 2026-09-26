import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
def move : Move dead :=
  Move.ofEdge dead ⟨0, Nat.zero_lt_one⟩ ⟨1 = 2 ∧ True⟩ ⟨fun h => h.1⟩
end Sub
