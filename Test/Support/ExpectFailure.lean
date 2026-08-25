import Lean

/-!
# `#expect_failure`

A negative-test harness. `#expect_failure <command>` succeeds exactly when the
wrapped command is **rejected** by the elaborator, and fails loudly when the
command is accepted.

This is what makes CRRG's negative tests real tests rather than comments:
Spec acceptance criterion 8 requires that a deliberately weakened child
statement or a missing branch is *rejected*, and that rejection must itself be
checked by the build.

The environment and message log are restored afterwards, so a rejected command
leaves no trace.

## Why `Elab.async` is forced off

Lean 4.30 elaborates `theorem` bodies **asynchronously**: `elabCommand` returns
before the proof has been checked, so the command's message log is still empty
at that point. Without disabling this, `#expect_failure` reports a *false pass*
for every `theorem` whose proof is wrong — the exact case a negative test most
needs to catch. (`def` and `example` are elaborated synchronously and were
unaffected, which is what made the gap easy to miss.)

`elabCommand` therefore runs with `Elab.async := false`, and
`Test/Synthetic/ExpectFailureSelfTest.lean` pins the behaviour for all three
declaration kinds so this cannot regress silently.
-/

open Lean Elab Command

/-- `#expect_failure cmd` fails the build unless `cmd` is rejected.

    Forces synchronous elaboration so that errors inside `theorem` bodies are
    observed; see the module doc-comment. -/
elab "#expect_failure" cmd:command : command => do
  let saved ← get
  modify fun st => { st with messages := {} }
  let ok ←
    try
      withScope (fun sc => { sc with opts := sc.opts.setBool `Elab.async false }) do
        elabCommand cmd
      pure (← get).messages.hasErrors
    catch _ =>
      pure true
  set saved
  unless ok do
    throwError
      "#expect_failure: the command was ACCEPTED but should have been rejected"
