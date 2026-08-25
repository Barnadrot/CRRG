/-!
# CRRG.Escape

Explicit escape packages for two-way splits where a reduction either
produces the desired object or an exceptional one. The exception
remains on the frontier until separately handled.
-/

import CRRG.Witness

namespace CRRG

/-- An escape map classifies each parent witness as either a main-branch
    witness or an escape-branch witness. The escape branch cannot be
    silently dropped. -/
structure EscapeMap (parent main escape : BadNode) where
  classify : parent.Witness → main.Witness ⊕ escape.Witness

namespace EscapeMap

/-- Convert an `EscapeMap` to a `WitnessSplit` with two branches. -/
def toWitnessSplit {parent main escape : BadNode}
    (e : EscapeMap parent main escape) :
    WitnessSplit parent where
  Branch := Bool
  child
    | true => main
    | false => escape
  classify w :=
    match e.classify w with
    | Sum.inl m => ⟨true, m⟩
    | Sum.inr esc => ⟨false, esc⟩

/-- If both main and escape branches are closed, the parent is closed. -/
theorem closed_parent {parent main escape : BadNode}
    (e : EscapeMap parent main escape)
    (hMain : main.Closed) (hEscape : escape.Closed) : parent.Closed :=
  e.toWitnessSplit.closed_parent (fun
    | true => hMain
    | false => hEscape)

end EscapeMap

end CRRG
