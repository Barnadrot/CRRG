import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
def move : Move G0 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new (rangeEntry (0, 4)), .new (rangeEntry (5, 9))]
  cover h := (rangeSplit Pt 0 4 9).discharge fun c hc => by
    simp [rangeSplit] at hc
    rcases hc with rfl | rfl
    · exact h (.new (rangeEntry (0, 4))) (by simp)
    · exact h (.new (rangeEntry (5, 9))) (by simp)
end Sub
