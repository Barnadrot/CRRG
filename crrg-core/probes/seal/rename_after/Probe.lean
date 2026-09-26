import CRRGTools
-- Seal probe (review item 7, rename pair; after). Same theorem name and statement shape;
-- only the auxiliary's name changes. Policy: the seal is name-sensitive, so the seals differ.
namespace Probe.Rename
def newAux (n : Nat) : Prop := n ≤ 10 ∧ 2 ≤ n
theorem target : newAux 7 := by unfold newAux; decide
end Probe.Rename
#crrg_seal Probe.Rename.target
