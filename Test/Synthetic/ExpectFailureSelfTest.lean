import CRRGTest.ExpectFailure

/-!
# Self-test for the `#expect_failure` harness

Every negative test in this suite is only as trustworthy as the harness that
asserts it. This module pins the harness's behaviour in **both** directions, for
all three declaration kinds.

The motivating bug: Lean 4.30 elaborates `theorem` bodies asynchronously, so the
first version of the harness observed an empty message log and reported a *false
pass* for every `theorem` with a broken proof. `def` and `example` were
unaffected, which is exactly why it was easy to miss. If `Elab.async` handling
ever regresses, the `theorem` case below starts failing.
-/

/-! ## Invalid declarations must be rejected — one per declaration kind. -/

#expect_failure
theorem selfTestBadTheorem : False := True.intro

#expect_failure
example : False := True.intro

#expect_failure
def selfTestBadDef : False := True.intro

#expect_failure
private theorem selfTestBadPrivateTheorem : False := True.intro

-- Ill-typed rather than ill-proved.
#expect_failure
def selfTestIllTyped : Nat := "not a nat"

/-! ## Valid declarations must be reported as wrongly accepted.

`#expect_failure` is itself a command, so it nests: the outer one asserts that
the inner one errors. This is the direction that catches a harness which passes
unconditionally. -/

#expect_failure
#expect_failure
theorem selfTestGoodTheorem : True := trivial

#expect_failure
#expect_failure
example : True := trivial

#expect_failure
#expect_failure
def selfTestGoodDef : Nat := 0

/-! ## A rejected declaration must not survive in the environment. -/

#expect_failure
def selfTestLeak : Nat := "not a nat"

-- If the rejected `def` above had been added (e.g. as `sorry`), this reference
-- would succeed and the outer assertion would fail.
#expect_failure
example : Nat := selfTestLeak
