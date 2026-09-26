import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
def OneEqTwo : Prop := 1 = 2
def move : Move F2 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new ⟨⟨OneEqTwo⟩, .top, trivial⟩]
  cover h := by
    have h1 : OneEqTwo := h _ (List.mem_singleton.mpr rfl)
    exact absurd (show 1 = 2 from h1) (by decide)
end Sub
