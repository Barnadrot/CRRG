import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
def move : Move G0 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new (rangeEntry (0, 19))]
  cover h := by
    have hp : rangeFam.claim (0, 19) := h _ (List.mem_singleton.mpr rfl)
    show ∀ x, 0 ≤ x → x ≤ 9 → Pt x
    exact fun x h0 h9 => hp x h0 (by omega)
end Sub
