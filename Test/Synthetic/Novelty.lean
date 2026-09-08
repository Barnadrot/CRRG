import CRRG

/-!
# Synthetic test: the second-order cycle counter

Covers Spec 31 on a two-element obligation key at the default threshold of 3.
Everything is `rfl` or `decide` on concrete data — seconds, not a gate invocation
(Spec 35).

No `#expect_failure`: every rule is a positive equation about the resulting
state, and the one property that sounds negative — a required obligation refuses
a normal-mode open — is pinned positively, as `modeAllowed … false = false`.
-/

open CRRG

private inductive NKey | a | b
  deriving DecidableEq

private def C0 : CycleState NKey := CycleState.initial NKey

/-- Complete `n` stall cycles at one key. -/
private def bump (s : CycleState NKey) (o : NKey) : Nat → CycleState NKey
  | 0 => s
  | n + 1 => (bump s o n).completeCycle o

/-! ## The Spec 31.1 walk at threshold 3. -/

example : C0.threshold = 3 := rfl
example : C0.cycles .a = 0 := rfl
example : C0.required .a = false := by decide

-- Two completed cycles are counted and do not require novelty.
example : (bump C0 .a 2).cycles .a = 2 := by decide
example : (bump C0 .a 2).required .a = false := by decide

-- The third does.
example : (bump C0 .a 3).cycles .a = 3 := by decide
example : (bump C0 .a 3).required .a = true := by decide

-- ...and it stays required as cycles keep accumulating: this is a threshold, not
-- a multiple, unlike the first-order block.
example : (bump C0 .a 5).required .a = true := by decide

/-! ## Mode enforcement (Spec 31.4). -/

example : (bump C0 .a 2).modeAllowed .a false = true := by decide
example : (bump C0 .a 3).modeAllowed .a false = false := by decide
example : (bump C0 .a 3).modeAllowed .a true = true := by decide

-- Novelty mode is always allowed — it is the demanded mode, never a bypass.
example : C0.modeAllowed .a true = true := by decide

/-! ## Certified movement resets the second order (Spec 31.4). -/

example : ((bump C0 .a 3).admittedReset .a).cycles .a = 0 := by decide
example : ((bump C0 .a 3).admittedReset .a).required .a = false := by decide
example : ((bump C0 .a 3).admittedReset .a).modeAllowed .a false = true := by decide

-- From any depth, not just from exactly the threshold.
example : ((bump C0 .a 7).admittedReset .a).cycles .a = 0 := by decide

/-! ## Non-events change nothing.

A checkpoint, an integrity event, a terminal no-transition: each moves the
first-order machine or nothing, and none completes a cycle. -/

example : (bump C0 .a 2).inert .a = bump C0 .a 2 := rfl
example : ((bump C0 .a 2).inert .a).cycles .a = 2 := by decide

/-! ## Isolation: one obligation's history never touches another's. -/

private def mixed : CycleState NKey := bump (bump C0 .b 1) .a 3

example : mixed.cycles .a = 3 := by decide
example : mixed.required .a = true := by decide
example : mixed.cycles .b = 1 := by decide
example : mixed.required .b = false := by decide

-- `b` may still open in normal mode while `a` demands novelty.
example : mixed.modeAllowed .b false = true := by decide
example : mixed.modeAllowed .a false = false := by decide

-- Resetting `a` leaves `b` alone.
example : (mixed.admittedReset .a).cycles .b = 1 := by decide

/-! ## The generic laws, instantiated.

The module states these for any obligation type; these are their regression tests
at the concrete key, so a future edit to the generic proof shows up here. -/

example : (bump C0 .a 2).required .a = false :=
  CycleState.two_cycles_not_required NKey.a

example : (bump C0 .a 3).required .a = true :=
  CycleState.three_cycles_required NKey.a

example : (bump C0 .a 3).modeAllowed .a false = false :=
  CycleState.three_cycles_normal_refused NKey.a

example (h : NKey.b ≠ NKey.a) : (mixed.completeCycle .a).required .b = mixed.required .b :=
  CycleState.required_of_ne mixed NKey.a NKey.b h
