import CRRG

/-!
# Synthetic test: WitnessMap and WitnessSplit

Covers the Stage A items "witness-level `WitnessSplit`" and
"DAG reuse where one theorem discharges multiple parents".
-/

open CRRG

private abbrev bigNode : BadNode := ⟨Nat × Nat⟩
private abbrev leftNode : BadNode := ⟨Nat⟩
private abbrev rightNode : BadNode := ⟨Nat⟩

private def projLeft : WitnessMap bigNode leftNode := ⟨Prod.fst⟩
private def projRight : WitnessMap bigNode rightNode := ⟨Prod.snd⟩

-- Closing either child closes the parent (a witness map is a rootward edge).
example (h : leftNode.Closed) : bigNode.Closed := projLeft.closed_parent h
example (h : rightNode.Closed) : bigNode.Closed := projRight.closed_parent h

-- WitnessMap composition is rootward-transitive.
private abbrev tripleNode : BadNode := ⟨Nat × Nat × Nat⟩
private def tripleToBig : WitnessMap tripleNode bigNode :=
  ⟨fun w => (w.1, w.2.1)⟩
private def tripleToLeft : WitnessMap tripleNode leftNode :=
  tripleToBig.trans projLeft

example (h : leftNode.Closed) : tripleNode.Closed := tripleToLeft.closed_parent h

-- Identity map.
example (h : leftNode.Closed) : leftNode.Closed :=
  (WitnessMap.id leftNode).closed_parent h

/-! ## DAG reuse: one closed child discharges two distinct parents. -/

private abbrev sharedChild : BadNode := ⟨Empty⟩
private abbrev parentP : BadNode := ⟨Empty⟩
private abbrev parentQ : BadNode := ⟨Empty⟩

private def pToShared : WitnessMap parentP sharedChild := ⟨_root_.id⟩
private def qToShared : WitnessMap parentQ sharedChild := ⟨_root_.id⟩

private theorem sharedClosed : sharedChild.Closed := fun e => e.elim

-- The single theorem `sharedClosed` discharges both parents.
example : parentP.Closed := pToShared.closed_parent sharedClosed
example : parentQ.Closed := qToShared.closed_parent sharedClosed

-- The same reuse at proposition level, via `toEdge`.
example : Goal.Proved ⟨parentP.Closed⟩ :=
  (pToShared.toEdge).discharge sharedClosed
example : Goal.Proved ⟨parentQ.Closed⟩ :=
  (qToShared.toEdge).discharge sharedClosed

/-! ## WitnessSplit: exhaustive classification of every parent witness. -/

private abbrev intNode : BadNode := ⟨Int⟩
private abbrev nonNegNode : BadNode := ⟨{ z : Int // 0 ≤ z }⟩
private abbrev negNode : BadNode := ⟨{ z : Int // z < 0 }⟩

private def signSplit : WitnessSplit intNode where
  Branch := Bool
  child
    | true => nonNegNode
    | false => negNode
  classify := fun (z : Int) =>
    if h : 0 ≤ z then ⟨true, ⟨z, h⟩⟩ else ⟨false, ⟨z, by omega⟩⟩

example (h0 : nonNegNode.Closed) (h1 : negNode.Closed) : intNode.Closed :=
  signSplit.closed_parent fun
    | true => h0
    | false => h1

-- The induced proposition-level `Split` has the same branch structure.
example : signSplit.toSplit.Branch = Bool := rfl
