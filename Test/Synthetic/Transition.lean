import CRRG

/-!
# Synthetic test: first-class frontier transitions

Covers Spec 20: identity, composition, root-closure transport, and the
transition each frontier operator induces.

Positive tests only, deliberately. A `Transition` is a one-field `Prop`; the
only way to get one wrong is to fail to prove `preserve`, which surfaces as a
build failure rather than as a check that could silently pass. Rejection of
weakened frontiers is already pinned in `Test/Synthetic/NegativeTests.lean`.
-/

open CRRG

/-! ## Identity and composition on toy frontiers. -/

private def unitRoot : Goal := ⟨True⟩

private def triv : Frontier unitRoot := Frontier.trivial unitRoot

private theorem trivRefl : Frontier.Transition triv triv :=
  Frontier.Transition.refl triv

-- Identity composed with identity is again a transition...
example : Frontier.Transition triv triv := trivRefl.comp trivRefl

-- ...and it transports root closure.
example : unitRoot.Proved := trivRefl.closeRoot fun _ => _root_.trivial

/-! ## Composition across universes.

`splitLeaf` lands in `max u v`, so a real chain is heterogeneous in level and
`comp` needs three universe parameters. This is the smallest test that a
monomorphic `Transition` would fail. -/

private def bigTriv : Frontier.{1} unitRoot where
  Task := ULift Unit
  leaf _ := unitRoot
  closeRoot h := h (ULift.up ())

private theorem smallToBig : Frontier.Transition triv bigTriv :=
  ⟨fun h _ => h (ULift.up ())⟩

private theorem bigToSmall : Frontier.Transition bigTriv triv :=
  ⟨fun h _ => h ()⟩

example : Frontier.Transition triv triv := smallToBig.comp bigToSmall

example : unitRoot.Proved :=
  (smallToBig.comp bigToSmall).closeRoot fun _ => _root_.trivial

/-! ## An explicit certified chain `F0 --T1--> F1 --T2--> F2`.

Each step is produced by a real operator, so each transition comes from the
induced-transition theorems rather than being asserted here. -/

private def chainRoot : Goal := ⟨(∀ n : Nat, n + 0 = n) ∧ True⟩

private def F0 : Frontier chainRoot := Frontier.trivial chainRoot

private def F0dec : DecidableEq F0.Task := inferInstanceAs (DecidableEq Unit)

/-! ### Step 1 — refine the single obligation to a stronger one. -/

private def stronger : Goal := ⟨∀ n : Nat, n + 0 = n ∧ 0 + n = n⟩

private theorem edge0 : Edge (F0.leaf ()) stronger :=
  ⟨fun h => ⟨fun n => (h n).1, _root_.trivial⟩⟩

private def F1 : Frontier chainRoot := F0.refineLeaf F0dec () edge0

private theorem T1 : Frontier.Transition F0 F1 :=
  F0.refineLeaf_transition F0dec () edge0

-- The task index is unchanged by an `Edge` refinement, so the same instance
-- serves the next step.
private def F1dec : DecidableEq F1.Task := F0dec

/-! ### Step 2 — split that obligation into its two halves. -/

private def cover : Split (F1.leaf ()) where
  Branch := Fin 2
  child
    | 0 => ⟨∀ n : Nat, n + 0 = n⟩
    | 1 => ⟨∀ n : Nat, 0 + n = n⟩
  discharge h n := ⟨h 0 n, h 1 n⟩

private def F2 : Frontier chainRoot := F1.splitLeaf F1dec () cover

private theorem T2 : Frontier.Transition F1 F2 :=
  F1.splitLeaf_transition F1dec () cover

/-- The chain collapsed into one kernel-produced certificate. -/
private theorem T02 : Frontier.Transition F0 F2 := T1.comp T2

/- Stated separately for the reason recorded in `Test/Synthetic/Refinement.lean`:
at the use site below the branch type is `cover.Branch`, a projection of an
ordinary `def`, which numeral elaboration does not unfold — `0` there reports a
missing `OfNat cover.Branch 0` instance. Written here, where the index type is
plainly `Fin 2`, the literals elaborate. -/
private theorem coverClosed : ∀ i : Fin 2, (cover.child i).claim
  | 0 => fun n => Nat.add_zero n
  | 1 => fun n => Nat.zero_add n

-- Closing the *final* frontier discharges the *original* root, through the
-- composite alone. The intermediate states are never re-proved.
example : chainRoot.Proved :=
  T02.closeRoot fun
    | .inl ⟨(), h⟩ => absurd rfl h
    | .inr b => coverClosed b

/-! ## Retirement induces a transition too.

Retiring the last live leaf leaves a frontier with an empty task type, so the
composite certificate closes the root outright. -/

private theorem strongerProof : (F1.leaf ()).claim :=
  fun n => ⟨Nat.add_zero n, Nat.zero_add n⟩

private def F1' : Frontier chainRoot := F1.retireLeaf F1dec () strongerProof

private theorem T1' : Frontier.Transition F1 F1' :=
  F1.retireLeaf_transition F1dec () strongerProof

example : chainRoot.Proved :=
  (T1.comp T1').closeRoot fun ⟨(), h⟩ => absurd rfl h
