import CRRGTools
-- Seal probe (review item 7, rename pair; before). Same theorem name and statement shape;
-- only the auxiliary's name changes. Policy: the seal is name-sensitive, so the seals differ.
namespace Probe.Rename
def oldAux (n : Nat) : Prop := n ≤ 10 ∧ 2 ≤ n
theorem target : oldAux 7 := by unfold oldAux; decide
end Probe.Rename
#crrg_seal Probe.Rename.target
