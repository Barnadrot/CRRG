import CRRG

/-!
# Synthetic test: EscapeMap

Tests that escape refinements keep the exceptional branch explicit.
-/


open CRRG

private abbrev parentNode : BadNode := ⟨Int⟩
private abbrev mainNode : BadNode := ⟨{ z : Int // z ≥ 0 }⟩
private abbrev escapeNode : BadNode := ⟨{ z : Int // z < 0 }⟩

private def escapeExample : EscapeMap parentNode mainNode escapeNode where
  classify := fun (z : Int) =>
    if h : z ≥ 0 then
      Sum.inl ⟨z, h⟩
    else
      Sum.inr ⟨z, by omega⟩

-- Verify branch assignment. The child family is an *index* of `WitnessSplit`,
-- so it is fixed by the conversion's type rather than read out of a field.
example : EscapeMap.child mainNode escapeNode true = mainNode := rfl
example : EscapeMap.child mainNode escapeNode false = escapeNode := rfl

-- The exceptional branch is visible in the conversion's *type*: deleting it
-- would change a signature, not just a proof (§5.5).
example : WitnessSplit parentNode (EscapeMap.child mainNode escapeNode) :=
  escapeExample.toWitnessSplit

-- Both main AND escape branches are required to close the parent.
-- The escape branch cannot be silently dropped.
example (hMain : mainNode.Closed) (hEscape : escapeNode.Closed) :
    parentNode.Closed :=
  escapeExample.closed_parent hMain hEscape

-- Same via WitnessSplit conversion
example (hMain : mainNode.Closed) (hEscape : escapeNode.Closed) :
    parentNode.Closed :=
  escapeExample.toWitnessSplit.closed_parent fun
    | true => hMain
    | false => hEscape
