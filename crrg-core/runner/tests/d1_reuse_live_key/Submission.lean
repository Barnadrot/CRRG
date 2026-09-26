import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
def move : Move F2 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new ⟨⟨R⟩, .top, trivial⟩]
  cover h := h _ (List.mem_singleton.mpr rfl)
end Sub
