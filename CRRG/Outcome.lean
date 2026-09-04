/-!
# CRRG.Outcome

Spec 19's two-axis outcome model. The pre-v0.9 vocabulary conflated two
questions — "is this state/outcome valid?" and "did the certified research state
move?" — and the cost of that conflation was operational: a valid no-op could be
rendered as a green pass and read as progress.

The two axes are `IntegrityStatus` (valid / rejected / tooling failure) and
certified transition status (admitted / no transition). They are *not* stored as
an independent pair. `TerminalOutcome` is the product already quotiented by
legality, so the illegal combinations are unrepresentable by construction rather
than rejected by a validator:

* an admitted transition that was rejected, or that failed tooling, cannot be
  written down — `admitted` is one constructor and carries no integrity field;
* an admitted transition with no semantic kind cannot be written down — the kind
  is a constructor argument, not an optional field;
* a rejection or tooling failure that also claims certified movement cannot be
  written down, for the same reason.

`integrity` is therefore a total function out of `TerminalOutcome`, never a
consistency check that could fail.

Spec 19.2 is the load-bearing asymmetry: `noTransition` is `valid` but not
admitted. It is a research no-op, not a security failure — so it must not be
rendered as success, and must not be rendered as an error either. That is what
`exitCode`'s four distinguishable values exist for.
-/

namespace CRRG

/-- The semantic kind of an admitted certified transition (Spec 19.1).
    `quantitative` is 19.1's "exact monotone quantitative movement, where a
    proved family supports it". -/
inductive TransitionKind
  | closed
  | refined
  | split
  | refuted
  | retired
  | superseded
  | quantitative
  deriving DecidableEq

/-- Integrity / adjudication status (Spec 19.1): is this state mutation valid? -/
inductive IntegrityStatus
  | valid
  | rejected
  | toolingFailure
  deriving DecidableEq

/-- The terminal outcome of a research episode (Spec 19.1, 23).

    One constructor per legal axis combination, so an outcome cannot claim
    certified movement and a rejection at the same time. -/
inductive TerminalOutcome
  | admitted (kind : TransitionKind)
  | noTransition
  | rejected
  | toolingFailure
  deriving DecidableEq

namespace TerminalOutcome

/-- The integrity axis, read off the outcome. Total by construction. -/
def integrity : TerminalOutcome → IntegrityStatus
  | .admitted _ => .valid
  | .noTransition => .valid
  | .rejected => .rejected
  | .toolingFailure => .toolingFailure

/-- The certified-transition axis.

    `Bool` rather than `Prop`: this is decidable orchestration data that a
    scheduler branches on, it composes with `Stall.mayLaunch`'s `Bool`, and it
    lets the regressions discharge by `decide`. -/
def isAdmitted : TerminalOutcome → Bool
  | .admitted _ => true
  | _ => false

/-- Spec 19.2's exit codes. The exact numbers are a CLI contract; what is
    normative is that the four states stay mechanically distinguishable, which
    is what the four theorems below prove. -/
def exitCode : TerminalOutcome → Nat
  | .admitted _ => 0
  | .noTransition => 10
  | .rejected => 20
  | .toolingFailure => 30

/-! ### The four states are mechanically distinguishable

Each exit code characterises its outcome exactly — `iff`, not merely one
direction, so no other outcome can be mistaken for it downstream. -/

theorem exitCode_eq_zero_iff (o : TerminalOutcome) :
    o.exitCode = 0 ↔ ∃ k, o = .admitted k := by
  cases o <;> simp [exitCode]

theorem exitCode_eq_ten_iff (o : TerminalOutcome) :
    o.exitCode = 10 ↔ o = .noTransition := by
  cases o <;> simp [exitCode]

theorem exitCode_eq_twenty_iff (o : TerminalOutcome) :
    o.exitCode = 20 ↔ o = .rejected := by
  cases o <;> simp [exitCode]

theorem exitCode_eq_thirty_iff (o : TerminalOutcome) :
    o.exitCode = 30 ↔ o = .toolingFailure := by
  cases o <;> simp [exitCode]

/-! ### Spec 19.2: a valid no-op is neither success nor failure -/

/-- `NO_TRANSITION` is `VALID` **and** not admitted. Both halves matter: the
    first forbids rendering it as an error, the second forbids rendering it as
    progress. -/
theorem noTransition_valid_not_admitted :
    noTransition.integrity = .valid ∧ noTransition.isAdmitted = false :=
  ⟨rfl, rfl⟩

/-- Only an admitted outcome is admitted, whatever its kind. -/
theorem isAdmitted_iff (o : TerminalOutcome) :
    o.isAdmitted = true ↔ ∃ k, o = .admitted k := by
  cases o <;> simp [isAdmitted]

/-- An admitted transition is always valid: the integrity axis cannot disagree
    with the transition axis, because there is no state in which it could. -/
theorem integrity_of_isAdmitted (o : TerminalOutcome) (h : o.isAdmitted = true) :
    o.integrity = .valid := by
  cases o <;> simp_all [isAdmitted, integrity]

end TerminalOutcome

end CRRG
