import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
namespace Sealed
def Bound (n : Nat) : Prop := n + 0 = n
end Sealed
def NewQuantity (n : Nat) : Prop := 0 + n = n
def Leaf : Prop := ∀ n, NewQuantity n
theorem spec0 : NewQuantity 0 ↔ Sealed.Bound 0 := ⟨fun _ => rfl, fun _ => rfl⟩
def move : Move (H0 (∀ n, Sealed.Bound n)) :=
  Move.ofEdge (H0 (∀ n, Sealed.Bound n)) ⟨0, Nat.zero_lt_one⟩ ⟨Leaf⟩
    ⟨fun _ _ => rfl⟩
end Sub
