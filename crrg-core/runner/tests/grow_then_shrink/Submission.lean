import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
def move : Move G1g where
  pos := ⟨0, by decide⟩
  children := [.old 1, .new (rangeEntry (5, 19))]
  cover h := by
    have hv : 1 < G1g.reg.length := by decide
    have h1 : rangeFam.claim (0, 4) := (holds_iff hv).mp (h (.old 1) (by simp))
    have h2 : rangeFam.claim (5, 19) := h (.new (rangeEntry (5, 19))) (by simp)
    show ∀ x, 0 ≤ x → x ≤ 19 → Pt x
    intro x h0 h19
    by_cases hx : x ≤ 4
    · exact h1 x h0 hx
    · exact h2 x (by omega) h19
end Sub
