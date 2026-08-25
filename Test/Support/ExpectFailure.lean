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
-/

open Lean Elab Command

/-- `#expect_failure cmd` fails the build unless `cmd` is rejected. -/
elab "#expect_failure" cmd:command : command => do
  let saved ← get
  modify fun st => { st with messages := {} }
  let ok ←
    try
      elabCommand cmd
      pure (← get).messages.hasErrors
    catch _ =>
      pure true
  set saved
  unless ok do
    throwError
      "#expect_failure: the command was ACCEPTED but should have been rejected"
