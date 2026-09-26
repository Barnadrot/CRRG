import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
def move : Move Q2 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new ⟨⟨swapped 11⟩, .top, trivial⟩]
  cover h := by
    have h1 : swapped 11 := h _ (List.mem_singleton.mpr rfl)
    exact absurd ((direct_iff_swapped 11).mpr h1) (by unfold direct; decide)
end Sub
