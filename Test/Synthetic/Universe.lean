import CRRG

/-!
# Synthetic test: universe polymorphism

`Goal` is universe-free (its claim is a `Prop`), but `BadNode.Witness`,
`Split.Branch` and `Frontier.Task` are `Type u`. These tests exercise witnesses
and index types *above* `Type 0`, which the monomorphic version could not
express at all.

They also confirm that ordinary `Type 0` usage still elaborates with no
universe annotations anywhere — the polymorphism must not leak into everyday
downstream code.
-/

open CRRG

/-! ## A `BadNode` whose witness type lives in `Type 1`. -/

-- A counterexample that carries a type, not just data: this cannot live in
-- `Type 0`, so a monomorphic `BadNode` could not host it.
private abbrev bigWitness : BadNode.{1} := ⟨(α : Type) × (α → α)⟩
private abbrev smallWitness : BadNode.{0} := ⟨Nat⟩

-- A witness map *across* universes: parent in `Type 1`, child in `Type 0`.
private def forget : WitnessMap bigWitness smallWitness :=
  ⟨fun _ => 0⟩

example (h : smallWitness.Closed) : bigWitness.Closed := forget.closed_parent h

-- Closing the higher-universe node directly.
private abbrev emptyBig : BadNode.{1} := ⟨(α : Type) × (α → Empty) × α⟩
private theorem emptyBigClosed : emptyBig.Closed :=
  fun ⟨_, f, a⟩ => (f a).elim

example : emptyBig.Closed := emptyBigClosed

/-! ## A `Split` indexed by a `Type 1` branch type. -/

private def bigSplit : Split.{1} ⟨True⟩ where
  Branch := ULift Bool
  child _ := ⟨True⟩
  discharge h := h (ULift.up true)

example : Goal.Proved ⟨True⟩ := bigSplit.discharge fun _ => trivial

/-! ## A `Frontier` whose task index lives in `Type 1`. -/

private def bigFrontier : Frontier.{1} ⟨True⟩ where
  Task := ULift Unit
  leaf _ := ⟨True⟩
  closeRoot h := h (ULift.up ())

example : Goal.Proved ⟨True⟩ := bigFrontier.closeRoot fun _ => trivial

/-! ## Ordinary `Type 0` usage needs no annotations. -/

private abbrev plainNode : BadNode := ⟨Nat⟩
private def plainSplit : Split ⟨True⟩ := Split.trivial _
private def plainFrontier : Frontier ⟨True⟩ := Frontier.ofSplit plainSplit

example : Goal.Proved ⟨True⟩ := plainFrontier.closeRoot fun _ => trivial
example (h : plainNode.Closed) : plainNode.Closed := (WitnessMap.id plainNode).closed_parent h

/-! ## A guarded refinement across universes. -/

private abbrev gParent : BadNode.{1} := ⟨ULift Bool⟩
private abbrev gPass : BadNode.{1} := ⟨ULift Unit⟩
private abbrev gFail : BadNode.{1} := ⟨ULift Unit⟩

private def gMap : GuardedMap gParent gPass gFail where
  guard b := b.down
  onPass _ _ := ULift.up ()
  onFail _ _ := ULift.up ()

example (hp : gPass.Closed) (hf : gFail.Closed) : gParent.Closed :=
  gMap.closed_parent hp hf
