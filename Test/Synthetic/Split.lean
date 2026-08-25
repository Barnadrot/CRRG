import CRRG

/-!
# Synthetic test: Split

Tests exhaustive `Split` on a two-branch decomposition.
-/


open CRRG

private def parentGoal : Goal := ⟨∀ (n : Nat), n = n⟩

private inductive TwoBranch | left | right

private def twoSplit : Split parentGoal where
  Branch := TwoBranch
  child
    | .left => ⟨∀ (n : Nat), n < 5 → n = n⟩
    | .right => ⟨∀ (n : Nat), ¬(n < 5) → n = n⟩
  discharge h n :=
    if hlt : n < 5 then
      h .left n hlt
    else
      h .right n hlt

example : parentGoal.Proved :=
  twoSplit.discharge fun
    | .left => fun _ _ => rfl
    | .right => fun _ _ => rfl

-- Trivial single-branch split
private def singleSplit : Split ⟨True⟩ := Split.trivial ⟨True⟩

example : Goal.Proved ⟨True⟩ := singleSplit.discharge fun () => trivial

-- Split.ofSplit creates a frontier
example : Frontier ⟨True⟩ := Frontier.ofSplit (Split.trivial ⟨True⟩)
