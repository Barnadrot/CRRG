import CRRGTools
-- Seal probe (review item 7, inductive pair; before). Same names and types; only the
-- constructor's index changes (Claim 7). The seal must follow the constructors and differ.
namespace Probe.Shape
inductive Claim : Nat → Prop where
  | witness : Claim 7
def root : Prop := Claim 7
end Probe.Shape
#crrg_seal Probe.Shape.root
