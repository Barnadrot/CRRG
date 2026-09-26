import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
def move : Move G0 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new (rangeEntry (0, 9))]
  cover h := h _ (List.mem_singleton.mpr rfl)
end Sub
