import CRRG.Outcome

/-!
# CRRG.Stall

Spec 22's stall detector, as a generic state machine.

**What this is.** An *orchestration* fact: "this obligation has produced N
terminal no-transitions, so change research behaviour before launching again."
That is all. The detector asserts nothing about whether the obligation is true,
whether it is hard, whether some other leaf would be easier, or whether the
reduction sits at the right depth — those stay separate judgements under Spec 10,
and a `RIGHT-DEPTH` obligation can be operationally stalled without contradiction.
The count is orchestration state and never feeds a score, a reward, or a rendered
aggregate (Spec 1).

**What the obligation key is.** Abstract. `Obl` is any type with decidable
equality. Spec 21's canonical obligation identity — derived deterministically
from the semantic seal, never from a display name, generation number, or
free-text description — is Phase D work, and nothing here derives, hashes, or
otherwise invents a key. What this module does encode is the *consequence* of
that discipline: two frontier positions that map to the same key share one
counter, which is exactly why the key must be canonical.

**State representation.** Total functions, not finite maps: every key has a count
and a flag at all times, so there is no "absent key" case to get wrong and no
insertion order to depend on. The cost is that equality of two `StallState`s is
extensional, so the laws below are stated pointwise at a key. That keeps every
statement decidable on a concrete key type and keeps the module free of `funext`.

**One rule made explicit.** Only `respond` and an `admitted` outcome clear a
block. A further `noTransition` on an already-blocked key raises the count but
cannot clear the flag (`noTransition_not_unblocks`) — an obligation must never be
able to un-stall itself by producing more no-transitions, which is precisely the
circling failure Spec 22 exists to interrupt.
-/

namespace CRRG

universe u

/-- Spec 22's deployment default: every 5 terminal no-transitions on one
    canonical obligation trigger `STALLED`. -/
def defaultThreshold : Nat := 5

/-- Per-obligation stall state.

    `threshold` travels with the state rather than being a module constant so a
    deployment can carry its own rule without a second copy of the machine. -/
structure StallState (Obl : Type u) where
  threshold : Nat
  count : Obl → Nat
  blocked : Obl → Bool

/-- A mandatory stall response (Spec 22). Recorded, not interpreted: the machine
    treats all five alike, and which one is appropriate is a research decision. -/
inductive StallResponse
  | reselect
  | backtrack
  | newMechanism
  | proposeRefinement
  | ownerOverride
  deriving DecidableEq

namespace StallState

variable {Obl : Type u}

/-! ## Key-agnostic part

Nothing in this section compares two obligations, so none of it needs decidable
equality — only the point updates further down do. -/

/-- Nothing recorded yet: every obligation at count 0, none blocked. -/
def initial (Obl : Type u) (threshold : Nat := defaultThreshold) : StallState Obl where
  threshold := threshold
  count _ := 0
  blocked _ := false

@[simp] theorem initial_count (t : Nat) (o : Obl) : (initial Obl t).count o = 0 := rfl

@[simp] theorem initial_blocked (t : Nat) (o : Obl) : (initial Obl t).blocked o = false := rfl

@[simp] theorem initial_threshold (t : Nat) : (initial Obl t).threshold = t := rfl

/-- A checkpoint (Spec 23) is append-only research evidence. It does not mutate
    the certified graph and does not increment the detector, so it returns the
    state unchanged — `checkpoint_eq` below is the whole content. -/
def checkpoint (s : StallState Obl) (_o : Obl) : StallState Obl := s

/-- Spec 22/23: checkpoints do not increment the detector. This is equality of
    whole states, not merely of the count at one key. -/
@[simp] theorem checkpoint_eq (s : StallState Obl) (o : Obl) : s.checkpoint o = s := rfl

/-- May a research episode launch on this obligation? -/
def mayLaunch (s : StallState Obl) (o : Obl) (override : Bool) : Bool :=
  override || !s.blocked o

@[simp] theorem mayLaunch_override (s : StallState Obl) (o : Obl) :
    s.mayLaunch o true = true := rfl

/-- Blocked means blocked: no launch without an override. -/
theorem not_mayLaunch_of_blocked (s : StallState Obl) (o : Obl)
    (h : s.blocked o = true) : s.mayLaunch o false = false := by
  simp [mayLaunch, h]

theorem mayLaunch_of_not_blocked (s : StallState Obl) (o : Obl)
    (h : s.blocked o = false) : s.mayLaunch o false = true := by
  simp [mayLaunch, h]

/-! ## Key updates

From here on an event lands at one obligation and must leave every other one
alone, which is what needs `DecidableEq`. -/

variable [DecidableEq Obl]

/-- Record a terminal outcome against one obligation (Spec 22).

    * `admitted` resets the key — certified movement materially changed, closed,
      or retired the obligation, so the history of no-transitions is spent;
    * `noTransition` increments, and blocks when the new count reaches a positive
      multiple of `threshold`;
    * `rejected` / `toolingFailure` change nothing: they are integrity events,
      not evidence about this obligation's research trajectory.

    A `threshold` of `0` never blocks, since `n % 0 = n ≠ 0` for the `n ≥ 1`
    reachable here. -/
def recordOutcome (s : StallState Obl) (o : Obl) : TerminalOutcome → StallState Obl
  | .admitted _ =>
      { s with
        count := fun x => if x = o then 0 else s.count x,
        blocked := fun x => if x = o then false else s.blocked x }
  | .noTransition =>
      { s with
        count := fun x => if x = o then s.count o + 1 else s.count x,
        blocked := fun x =>
          if x = o then s.blocked o || (s.count o + 1) % s.threshold == 0
          else s.blocked x }
  | .rejected => s
  | .toolingFailure => s

/-- Discharge a stall on one obligation. Clears the block; never touches the
    count, so the obligation's history is not erased by responding to it. -/
def respond (s : StallState Obl) (o : Obl) (_r : StallResponse) : StallState Obl :=
  { s with blocked := fun x => if x = o then false else s.blocked x }

/-! ### Integrity events change nothing

Spec 22: a rejection or a tooling failure says nothing about this obligation's
research trajectory, so it must not move the counter. Definitional, like
`checkpoint_eq`. -/

@[simp] theorem recordOutcome_rejected (s : StallState Obl) (o : Obl) :
    s.recordOutcome o .rejected = s := rfl

@[simp] theorem recordOutcome_toolingFailure (s : StallState Obl) (o : Obl) :
    s.recordOutcome o .toolingFailure = s := rfl

/-- The rule itself is invariant: no event rewrites the threshold. -/
@[simp] theorem recordOutcome_threshold (s : StallState Obl) (o : Obl)
    (out : TerminalOutcome) : (s.recordOutcome o out).threshold = s.threshold := by
  cases out <;> rfl

/-! ### Certified movement resets the obligation -/

@[simp] theorem recordOutcome_admitted_count (s : StallState Obl) (o : Obl)
    (k : TransitionKind) : (s.recordOutcome o (.admitted k)).count o = 0 := by
  simp [recordOutcome]

@[simp] theorem recordOutcome_admitted_blocked (s : StallState Obl) (o : Obl)
    (k : TransitionKind) : (s.recordOutcome o (.admitted k)).blocked o = false := by
  simp [recordOutcome]

/-! ### No-transition increments, and blocks at a multiple of the threshold -/

@[simp] theorem recordOutcome_noTransition_count (s : StallState Obl) (o : Obl) :
    (s.recordOutcome o .noTransition).count o = s.count o + 1 := by
  simp [recordOutcome]

/-- Reaching a positive multiple of the threshold blocks the obligation. -/
theorem blocked_of_multiple (s : StallState Obl) (o : Obl)
    (h : (s.count o + 1) % s.threshold = 0) :
    (s.recordOutcome o .noTransition).blocked o = true := by
  simp [recordOutcome, h]

/-- Below a multiple, an unblocked obligation stays unblocked. -/
theorem not_blocked_of_not_multiple (s : StallState Obl) (o : Obl)
    (hb : s.blocked o = false) (h : (s.count o + 1) % s.threshold ≠ 0) :
    (s.recordOutcome o .noTransition).blocked o = false := by
  simp [recordOutcome, hb, h]

/-- **An obligation cannot un-stall itself.** More no-transitions never clear a
    block, whatever the count does. -/
theorem noTransition_not_unblocks (s : StallState Obl) (o : Obl)
    (h : s.blocked o = true) :
    (s.recordOutcome o .noTransition).blocked o = true := by
  simp [recordOutcome, h]

/-! ### Responses -/

@[simp] theorem respond_blocked (s : StallState Obl) (o : Obl) (r : StallResponse) :
    (s.respond o r).blocked o = false := by
  simp [respond]

@[simp] theorem respond_count (s : StallState Obl) (o x : Obl) (r : StallResponse) :
    (s.respond o r).count x = s.count x := rfl

@[simp] theorem respond_threshold (s : StallState Obl) (o : Obl) (r : StallResponse) :
    (s.respond o r).threshold = s.threshold := rfl

/-- A response on an obligation that was not blocked is a no-op. -/
theorem respond_of_not_blocked (s : StallState Obl) (o : Obl) (r : StallResponse)
    (h : s.blocked o = false) (x : Obl) :
    (s.respond o r).blocked x = s.blocked x := by
  by_cases hx : x = o <;> simp [respond, hx, h]

/-! ### Isolation

Every event is local to its key. Without this, one obligation's history could
block or silently reset another's — the failure a non-canonical key would produce
by aliasing two distinct obligations. -/

@[simp] theorem recordOutcome_count_of_ne (s : StallState Obl) (o₁ o₂ : Obl)
    (out : TerminalOutcome) (h : o₂ ≠ o₁) :
    (s.recordOutcome o₁ out).count o₂ = s.count o₂ := by
  cases out <;> simp [recordOutcome, h]

@[simp] theorem recordOutcome_blocked_of_ne (s : StallState Obl) (o₁ o₂ : Obl)
    (out : TerminalOutcome) (h : o₂ ≠ o₁) :
    (s.recordOutcome o₁ out).blocked o₂ = s.blocked o₂ := by
  cases out <;> simp [recordOutcome, h]

@[simp] theorem respond_blocked_of_ne (s : StallState Obl) (o₁ o₂ : Obl)
    (r : StallResponse) (h : o₂ ≠ o₁) :
    (s.respond o₁ r).blocked o₂ = s.blocked o₂ := by
  simp [respond, h]

end StallState

end CRRG
