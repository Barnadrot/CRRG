import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
def move : Move C0 :=
  Move.ofEdge C0 ⟨0, Nat.zero_lt_one⟩ ⟨ClassCap⟩ ⟨fun h n => (h n).symm⟩
end Sub
