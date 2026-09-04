import CRRG

/-!
# Synthetic test: two-axis outcome semantics

Covers Spec 19: the integrity axis, the certified-transition axis, and the four
mechanically distinguishable terminal states.

No `#expect_failure`. The illegal axis combinations this module is built to
exclude are excluded by the *shape* of `TerminalOutcome` — there is no term to
reject, only constructors that do not exist — so a negative test here would pin
Lean's type checker rather than a CRRG property.
-/

open CRRG

/-! ## Spec 19.2's exit codes. -/

example : (TerminalOutcome.admitted .refined).exitCode = 0 := rfl
example : TerminalOutcome.noTransition.exitCode = 10 := rfl
example : TerminalOutcome.rejected.exitCode = 20 := rfl
example : TerminalOutcome.toolingFailure.exitCode = 30 := rfl

-- Every kind of admitted transition shares exit code 0. The kind is recorded on
-- the outcome, but it is not a fifth, sixth, ... terminal state.
example (k : TransitionKind) : (TerminalOutcome.admitted k).exitCode = 0 := rfl

-- The four codes are pairwise distinct, so no downstream reader can conflate two
-- terminal states.
example : TerminalOutcome.noTransition.exitCode ≠ TerminalOutcome.rejected.exitCode := by decide
example : TerminalOutcome.noTransition.exitCode ≠ (TerminalOutcome.admitted .closed).exitCode := by
  decide
example : TerminalOutcome.rejected.exitCode ≠ TerminalOutcome.toolingFailure.exitCode := by decide

/-! ## The characterisations run backwards.

Each `iff` recovers the terminal state *from* its exit code, which is what makes
the codes a contract rather than a convention. -/

example (o : TerminalOutcome) (h : o.exitCode = 10) : o = .noTransition :=
  (TerminalOutcome.exitCode_eq_ten_iff o).mp h

example (o : TerminalOutcome) (h : o.exitCode = 20) : o = .rejected :=
  (TerminalOutcome.exitCode_eq_twenty_iff o).mp h

example (o : TerminalOutcome) (h : o.exitCode = 30) : o = .toolingFailure :=
  (TerminalOutcome.exitCode_eq_thirty_iff o).mp h

-- Exit code 0 identifies an admitted transition, whatever kind it recorded.
example (o : TerminalOutcome) (h : o.exitCode = 0) : o.isAdmitted = true :=
  (TerminalOutcome.isAdmitted_iff o).mpr ((TerminalOutcome.exitCode_eq_zero_iff o).mp h)

/-! ## The integrity axis. -/

example : (TerminalOutcome.admitted .retired).integrity = .valid := rfl
example : TerminalOutcome.noTransition.integrity = .valid := rfl
example : TerminalOutcome.rejected.integrity = .rejected := rfl
example : TerminalOutcome.toolingFailure.integrity = .toolingFailure := rfl

example (k : TransitionKind) : (TerminalOutcome.admitted k).integrity = .valid := rfl

/-! ## Spec 19.2: `NO_TRANSITION` is valid, and is not progress.

Both halves are load-bearing in opposite directions. Dropping the first turns a
research no-op into a reported failure; dropping the second turns it into a green
pass that reads as movement. -/

example : TerminalOutcome.noTransition.integrity = .valid
        ∧ TerminalOutcome.noTransition.isAdmitted = false :=
  TerminalOutcome.noTransition_valid_not_admitted

-- On the integrity axis alone, a no-op is indistinguishable from an admitted
-- transition — which is exactly why the transition axis has to exist separately.
example : TerminalOutcome.noTransition.integrity
        = (TerminalOutcome.admitted .split).integrity := rfl

-- ...and on the transition axis it is indistinguishable from a rejection, which
-- is why integrity cannot be read off the transition axis either.
example : TerminalOutcome.noTransition.isAdmitted
        = TerminalOutcome.rejected.isAdmitted := rfl

-- The two axes never disagree in the one direction that would be unsound:
-- admitted always implies valid.
example (o : TerminalOutcome) (h : o.isAdmitted = true) : o.integrity = .valid :=
  TerminalOutcome.integrity_of_isAdmitted o h

/-! ## Decidable equality on all three enumerations. -/

example : TerminalOutcome.admitted .refined ≠ TerminalOutcome.admitted .split := by decide
example : TerminalOutcome.noTransition ≠ TerminalOutcome.rejected := by decide
example : TransitionKind.superseded ≠ TransitionKind.quantitative := by decide
example : IntegrityStatus.rejected ≠ IntegrityStatus.toolingFailure := by decide
example : TerminalOutcome.admitted .closed = TerminalOutcome.admitted .closed := by decide
