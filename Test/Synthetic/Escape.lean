/-!
# Synthetic test: EscapeMap

Tests that escape refinements keep the exceptional branch explicit.
-/

import CRRG

open CRRG

private def parentNode : BadNode := ⟨Int⟩
private def mainNode : BadNode := ⟨{ z : Int // z ≥ 0 }⟩
private def escapeNode : BadNode := ⟨{ z : Int // z < 0 }⟩

private def escapeExample : EscapeMap parentNode mainNode escapeNode where
  classify z :=
    if h : z ≥ 0 then
      Sum.inl ⟨z, h⟩
    else
      Sum.inr ⟨z, by omega⟩

-- Verify branch assignment
example : (escapeExample.toWitnessSplit.child true) = mainNode := rfl
example : (escapeExample.toWitnessSplit.child false) = escapeNode := rfl

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
