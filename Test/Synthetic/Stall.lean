import CRRG

/-!
# Synthetic test: stall detector

Covers Spec 22 on a two-element obligation key at the default threshold of 5.
Everything here is `rfl` or `decide` on concrete data — seconds, not a gate
invocation (Spec 18.2).

No `#expect_failure`: every rule in the state machine is a positive equation
about the resulting state, and the one property that *sounds* negative — an
obligation cannot un-stall itself — is pinned positively below, as the block
still standing after a sixth no-transition.
-/

open CRRG

private inductive Key | a | b
  deriving DecidableEq

private def S0 : StallState Key := StallState.initial Key

/-- Record `n` terminal no-transitions at one key. -/
private def bump (s : StallState Key) (o : Key) : Nat → StallState Key
  | 0 => s
  | n + 1 => (bump s o n).recordOutcome o .noTransition

/-! ## The Spec 22 walk at threshold 5. -/

example : S0.threshold = 5 := rfl
example : S0.count .a = 0 := rfl
example : S0.blocked .a = false := rfl

-- Four no-transitions are counted and do not block.
example : (bump S0 .a 4).count .a = 4 := by decide
example : (bump S0 .a 4).blocked .a = false := by decide

-- The fifth blocks.
example : (bump S0 .a 5).count .a = 5 := by decide
example : (bump S0 .a 5).blocked .a = true := by decide

/-- A stall response clears the block. -/
private def afterRespond : StallState Key := (bump S0 .a 5).respond .a .newMechanism

example : afterRespond.blocked .a = false := by decide
-- The history is not erased by responding to it: the count survives.
example : afterRespond.count .a = 5 := by decide

-- Five more stall the same obligation again, at ten...
example : (bump afterRespond .a 5).count .a = 10 := by decide
example : (bump afterRespond .a 5).blocked .a = true := by decide
-- ...and the four in between do not.
example : (bump afterRespond .a 4).count .a = 9 := by decide
example : (bump afterRespond .a 4).blocked .a = false := by decide

/-! ## An obligation cannot un-stall itself.

A sixth no-transition is not a multiple of 5. Were `blocked` *assigned* the
multiple test rather than accumulated, this would silently clear the block — and
an obligation would escape its own stall by producing exactly the no-movement
that Spec 22 exists to interrupt. -/

example : ((bump S0 .a 5).recordOutcome .a .noTransition).count .a = 6 := by decide
example : ((bump S0 .a 5).recordOutcome .a .noTransition).blocked .a = true := by decide

/-! ## Launch admission. -/

example : (bump S0 .a 5).mayLaunch .a false = false := by decide
example : (bump S0 .a 5).mayLaunch .a true = true := by decide
example : (bump S0 .a 4).mayLaunch .a false = true := by decide
example : afterRespond.mayLaunch .a false = true := by decide

/-! ## Events that change nothing.

Whole-state equalities, definitionally — a checkpoint and an integrity event do
not touch the machine at all, rather than touching it and putting it back. -/

example : (bump S0 .a 4).checkpoint .a = bump S0 .a 4 := rfl
example : (bump S0 .a 4).recordOutcome .a .rejected = bump S0 .a 4 := rfl
example : (bump S0 .a 4).recordOutcome .a .toolingFailure = bump S0 .a 4 := rfl

-- Even at the blocking boundary: a rejection on the fourth strike does not
-- become the fifth.
example : ((bump S0 .a 4).recordOutcome .a .rejected).blocked .a = false := by decide
example : ((bump S0 .a 4).checkpoint .a).count .a = 4 := by decide

-- A response on an obligation that was not blocked is a no-op at every key.
example (x : Key) :
    ((bump S0 .a 3).respond .a .reselect).blocked x = (bump S0 .a 3).blocked x :=
  StallState.respond_of_not_blocked _ _ _ (by decide) x

/-! ## Certified movement resets the obligation. -/

example : ((bump S0 .a 5).recordOutcome .a (.admitted .refined)).count .a = 0 := by decide
example : ((bump S0 .a 5).recordOutcome .a (.admitted .refined)).blocked .a = false := by decide

-- From any state and for any kind, via the generic law.
example (k : TransitionKind) :
    ((bump S0 .a 7).recordOutcome .a (.admitted k)).count .a = 0 :=
  StallState.recordOutcome_admitted_count _ _ _

example (k : TransitionKind) :
    ((bump S0 .a 7).recordOutcome .a (.admitted k)).blocked .a = false :=
  StallState.recordOutcome_admitted_blocked _ _ _

/-! ## Isolation: one obligation's history never touches another's. -/

/-- `b` has three strikes; `a` is then driven to a block. -/
private def mixed : StallState Key := bump (bump S0 .b 3) .a 5

example : mixed.count .a = 5 := by decide
example : mixed.blocked .a = true := by decide
example : mixed.count .b = 3 := by decide
example : mixed.blocked .b = false := by decide

-- `b` remains launchable while `a` is stalled.
example : mixed.mayLaunch .b false = true := by decide
example : mixed.mayLaunch .a false = false := by decide

-- Resetting `a` with certified movement leaves `b` alone.
example : (mixed.recordOutcome .a (.admitted .closed)).count .b = 3 := by decide
-- ...and responding on `a` leaves `b`'s flag alone.
example : (mixed.respond .a .backtrack).blocked .b = false := by decide

/-! ## Spec 21 at the level of keying discipline.

Two frontier positions carrying the same sealed proposition are one research
obligation, so they must share one counter. The canonical derivation of the key
is Phase D; what is testable now is that the detector follows the key and not the
position. -/

private inductive Position | leftLeaf | rightLeaf | otherLeaf
  deriving DecidableEq

private def obligationOf : Position → Key
  | .leftLeaf => .a
  | .rightLeaf => .a
  | .otherLeaf => .b

example : obligationOf .leftLeaf = obligationOf .rightLeaf := rfl
example : obligationOf .leftLeaf ≠ obligationOf .otherLeaf := by decide

/-- One no-transition at each aliased position: two strikes against one
    obligation, not one strike against each of two. -/
private def afterTwoPositions : StallState Key :=
  (S0.recordOutcome (obligationOf .leftLeaf) .noTransition).recordOutcome
    (obligationOf .rightLeaf) .noTransition

example : afterTwoPositions.count .a = 2 := by decide
example : afterTwoPositions.count .b = 0 := by decide

/-- Five no-transitions spread three-and-two across the two aliased positions
    stall the shared obligation, exactly as five at one position would. This is
    the duplicate-effort failure Spec 21 exists to prevent, seen from the
    detector's side. -/
private def spread : StallState Key :=
  bump (bump S0 (obligationOf .leftLeaf) 3) (obligationOf .rightLeaf) 2

example : spread.count .a = 5 := by decide
example : spread.blocked .a = true := by decide
example : spread.mayLaunch (obligationOf .leftLeaf) false = false := by decide
-- The alias is blocked too — it is the same obligation, not a sibling of it.
example : spread.mayLaunch (obligationOf .rightLeaf) false = false := by decide
-- The unrelated position is unaffected.
example : spread.mayLaunch (obligationOf .otherLeaf) false = true := by decide
