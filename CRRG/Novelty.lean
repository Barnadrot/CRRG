import CRRG.Stall

/-!
# CRRG.Novelty

Spec 31's second-order state, as a generic state machine.

**What this counts, and how it differs from `Stall`.** `CRRG.Stall` is
first-order: it counts terminal no-transitions and blocks an obligation when they
reach a multiple of its threshold. Live evidence showed that machine can itself
circle — stall, respond with a new mechanism, no transition, stall again — so this
module counts one level up: **completed stall cycles**, where a cycle is a block
event followed by its recorded response (Spec 31.1). At the deployment default of
three completed cycles since the last admitted transition, the obligation is
`NOVELTY_REQUIRED`.

**The coupling is the deployment's, not this module's.** `completeCycle` is an
increment and nothing more. *When* a cycle completes — a stall response recorded
while the obligation is blocked — is the caller's rule, and it lives in the
deployment's replay (`scripts/crrg-episode`), where the block flag and the
response row are both visible. This module deliberately cannot see either. Keeping
the judgement out here is what stops two definitions of "a cycle" existing.

**What the state means, and what it does not (Spec 31.2).** It is an
orchestration fact: repeated attempts under recorded mechanisms have not produced
certified movement, so the next research on this obligation should prioritise
inventing a new mechanism over more routine formalisation around the same
obstruction. It is **not** a mathematical novelty certificate — it asserts nothing
about whether the needed theorem is objectively novel, whether the literature
contains a solution, or whether the recorded mechanisms are semantically
exhaustive. It is **not an escalation**: it never asks an owner to choose
mathematics and never pauses research, it changes the *mode* of research and not
its continuation. And the count never feeds a score, a reward or a rendered
aggregate (Spec 1).

**Reset is Spec 22's rule, one level up.** An admitted transition that materially
changes, closes or retires the obligation zeroes its cycles, exactly as it zeroes
its no-transition count (Spec 31.4). Nothing else does.

`CRRG.Stall` is untouched by this module: it is imported, not modified.
-/

namespace CRRG

universe u

/-- Spec 31.1's deployment default: three completed stall cycles since the last
    admitted transition put an obligation in `NOVELTY_REQUIRED`. -/
def defaultCycleThreshold : Nat := 3

/-- Per-obligation completed-cycle state.

    `threshold` travels with the state for the same reason it does in
    `StallState`: a deployment carries its own rule without a second copy of the
    machine. Total function, not a finite map — every key has a count at all
    times, so there is no absent-key case to get wrong. -/
structure CycleState (Obl : Type u) where
  threshold : Nat
  cycles : Obl → Nat

namespace CycleState

variable {Obl : Type u}

/-! ## Key-agnostic part

Nothing here compares two obligations, so none of it needs decidable equality —
only the point updates further down do. -/

/-- Nothing recorded yet: every obligation at zero completed cycles. -/
def initial (Obl : Type u) (threshold : Nat := defaultCycleThreshold) :
    CycleState Obl where
  threshold := threshold
  cycles _ := 0

@[simp] theorem initial_cycles (t : Nat) (o : Obl) : (initial Obl t).cycles o = 0 := rfl

@[simp] theorem initial_threshold (t : Nat) : (initial Obl t).threshold = t := rfl

/-- Is this obligation in `NOVELTY_REQUIRED`? -/
def required (s : CycleState Obl) (o : Obl) : Bool :=
  decide (s.threshold ≤ s.cycles o)

/-- May an episode open on this obligation in the mode the caller declared?

    When the obligation is required, only a novelty-mode episode; otherwise
    either. Deliberately shaped like `StallState.mayLaunch`'s override: the
    permissive input is the *declared mode*, not a bypass. -/
def modeAllowed (s : CycleState Obl) (o : Obl) (noveltyMode : Bool) : Bool :=
  noveltyMode || !s.required o

/-- Every event that is neither a completed cycle nor an admitted reset.

    Checkpoints, integrity events, and terminal no-transitions all land here: they
    move the first-order machine or nothing at all, and none of them completes a
    cycle. `inert_eq` below is the whole content. -/
def inert (s : CycleState Obl) (_o : Obl) : CycleState Obl := s

/-- Non-events change nothing — whole-state equality, not merely pointwise. -/
@[simp] theorem inert_eq (s : CycleState Obl) (o : Obl) : s.inert o = s := rfl

@[simp] theorem modeAllowed_novelty (s : CycleState Obl) (o : Obl) :
    s.modeAllowed o true = true := rfl

/-- Not required means any mode may open. -/
theorem modeAllowed_of_not_required (s : CycleState Obl) (o : Obl)
    (h : s.required o = false) : s.modeAllowed o false = true := by
  simp [modeAllowed, h]

/-- **Required means novelty mode or nothing.** This is Spec 31.4's enforcement,
    stated on the state the deployment refuses from. -/
theorem not_modeAllowed_of_required (s : CycleState Obl) (o : Obl)
    (h : s.required o = true) : s.modeAllowed o false = false := by
  simp [modeAllowed, h]

/-! ## Key updates

From here an event lands at one obligation and must leave every other one alone,
which is what needs `DecidableEq`. -/

variable [DecidableEq Obl]

/-- One completed stall cycle at this obligation (Spec 31.1).

    An increment, and only that: see the module header on why the *condition* for
    calling it lives in the deployment. -/
def completeCycle (s : CycleState Obl) (o : Obl) : CycleState Obl :=
  { s with cycles := fun x => if x = o then s.cycles o + 1 else s.cycles x }

/-- Certified movement clears the second order too (Spec 31.4), the same rule
    Spec 22 applies to the no-transition count. -/
def admittedReset (s : CycleState Obl) (o : Obl) : CycleState Obl :=
  { s with cycles := fun x => if x = o then 0 else s.cycles x }

@[simp] theorem completeCycle_cycles (s : CycleState Obl) (o : Obl) :
    (s.completeCycle o).cycles o = s.cycles o + 1 := by
  simp [completeCycle]

@[simp] theorem admittedReset_cycles (s : CycleState Obl) (o : Obl) :
    (s.admittedReset o).cycles o = 0 := by
  simp [admittedReset]

@[simp] theorem completeCycle_threshold (s : CycleState Obl) (o : Obl) :
    (s.completeCycle o).threshold = s.threshold := rfl

@[simp] theorem admittedReset_threshold (s : CycleState Obl) (o : Obl) :
    (s.admittedReset o).threshold = s.threshold := rfl

/-- An admitted transition leaves the obligation not required, whatever it was. -/
@[simp] theorem not_required_after_admittedReset (s : CycleState Obl) (o : Obl)
    (h : 0 < s.threshold) : (s.admittedReset o).required o = false := by
  simp [required, admittedReset, Nat.not_le.mpr h]

/-! ### The Spec 31.1 walk at the default threshold of 3

Generic in the obligation type, concrete in the threshold, because three is the
number the rule names. -/

/-- Two completed cycles are not yet `NOVELTY_REQUIRED`. -/
theorem two_cycles_not_required (o : Obl) :
    (((initial Obl 3).completeCycle o).completeCycle o).required o = false := by
  simp [required]

/-- The third completed cycle is. -/
theorem three_cycles_required (o : Obl) :
    ((((initial Obl 3).completeCycle o).completeCycle o).completeCycle o).required o
      = true := by
  simp [required]

/-- ...and at that point a normal-mode open is not allowed, while a novelty-mode
    one is. -/
theorem three_cycles_normal_refused (o : Obl) :
    ((((initial Obl 3).completeCycle o).completeCycle o).completeCycle o).modeAllowed
      o false = false :=
  not_modeAllowed_of_required _ _ (three_cycles_required o)

theorem three_cycles_novelty_allowed (o : Obl) :
    ((((initial Obl 3).completeCycle o).completeCycle o).completeCycle o).modeAllowed
      o true = true := rfl

/-! ### Isolation

Every event is local to its key. Without this, one obligation's history could push
another into `NOVELTY_REQUIRED` — the failure a non-canonical key would produce by
aliasing two distinct obligations. -/

@[simp] theorem completeCycle_cycles_of_ne (s : CycleState Obl) (o₁ o₂ : Obl)
    (h : o₂ ≠ o₁) : (s.completeCycle o₁).cycles o₂ = s.cycles o₂ := by
  simp [completeCycle, h]

@[simp] theorem admittedReset_cycles_of_ne (s : CycleState Obl) (o₁ o₂ : Obl)
    (h : o₂ ≠ o₁) : (s.admittedReset o₁).cycles o₂ = s.cycles o₂ := by
  simp [admittedReset, h]

/-- ...so neither event can change another obligation's mode. -/
theorem required_of_ne (s : CycleState Obl) (o₁ o₂ : Obl) (h : o₂ ≠ o₁) :
    (s.completeCycle o₁).required o₂ = s.required o₂ := by
  simp [required, h]

end CycleState

end CRRG
