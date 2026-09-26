import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
namespace Sealed
def Bound (n : Nat) : Prop := n + 0 = n
end Sealed
def NewQuantity (n : Nat) : Prop := 0 + n = n
def Leaf : Prop := ∀ n, NewQuantity n
theorem fake (n : Nat) :
    (NewQuantity n → NewQuantity n) ∧ (Sealed.Bound n → Sealed.Bound n) := ⟨id, id⟩
def move : Move (H0 (∀ n, Sealed.Bound n)) :=
  Move.ofEdge (H0 (∀ n, Sealed.Bound n)) ⟨0, Nat.zero_lt_one⟩ ⟨Leaf⟩
    ⟨fun _ _ => rfl⟩
end Sub
