import CRRGCore
import Lean

/-!
# Whole-library axiom audit of the certified core (v0.12.0)

`Axioms.lean` prints the axioms of the headline declarations. This audit checks every constant instead:
every constant whose defining module has root `CRRGCore` (the `#crrg_check_lineage` criterion, so a module
missing from a hand-written list cannot escape), including private and compiler-generated ones, must depend
only on `propext` and `Quot.sound`. In particular, nothing in the certified library may use
`Classical.choice`. If any constant fails, the build fails. The summary line is captured in `BUILD.log`.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut perModule : Std.HashMap Name Nat := {}
  let mut total := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (name, _) in env.constants.toList do
    match env.getModuleIdxFor? name with
    | none => pure ()
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      if mod.getRoot == `CRRGCore then
        total := total + 1
        perModule := perModule.insert mod (perModule.getD mod 0 + 1)
        let axs ← liftCoreM <| collectAxioms name
        let extra := axs.filter fun a => a != ``propext && a != ``Quot.sound
        unless extra.isEmpty do bad := bad.push (name, extra)
  unless bad.isEmpty do
    throwError m!"core axiom audit FAILED: {bad.size} constants of CRRGCore leave [propext, Quot.sound]; the first is {bad[0]!.1}, which uses {bad[0]!.2}"
  logInfo m!"CORE AXIOM AUDIT: {total} constants in {perModule.size} modules with root CRRGCore; every one depends only on propext and Quot.sound (none on Classical.choice)"
