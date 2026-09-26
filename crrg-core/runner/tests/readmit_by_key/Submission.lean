import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
def move : Move F2 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.old 1]
  cover h := by
    have h1 : holds F2.reg 1 := h (.old 1) (List.mem_singleton.mpr rfl)
    have hv : 1 < F2.reg.length := by decide
    have h12 : 1 = 2 := (holds_iff hv).mp h1
    exact absurd h12 (by decide)
end Sub
