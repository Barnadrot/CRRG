import CRRG

/-!
# Synthetic test: Edge composition

Tests `Edge`, `Edge.id`, `Edge.trans` on small propositions.
-/


open CRRG

private def goalA : Goal := ⟨True⟩
private def goalB : Goal := ⟨1 + 1 = 2⟩
private def goalC : Goal := ⟨Nat.succ 0 = 1⟩

private theorem edgeAB : Edge goalA goalB :=
  ⟨fun _ => trivial⟩

private theorem edgeBC : Edge goalB goalC :=
  ⟨fun _ => rfl⟩

private theorem edgeAC : Edge goalA goalC :=
  edgeAB.trans edgeBC

example : goalA.Proved := edgeAC.discharge rfl

example : goalA.Proved := (Edge.id goalA).discharge trivial

example : goalA.Proved :=
  (edgeAB.trans (Edge.id goalB)).discharge rfl
