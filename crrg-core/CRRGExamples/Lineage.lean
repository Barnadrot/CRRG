import CRRGCore
import CRRGTools
import Lean

/-!
# G1 lineage: a metaprogrammed forgery is caught by the lineage audit (review item 2)

The kernel does not enforce `private`. A file that imports `Lean` can build a `State` through the
private constructor at the `Expr` level and add it with `addDecl` (the review's Probe2). Two
defences, both run by the gate:

1. **Runner obligation**: submitted files may not `import Lean` or use `elab`, `macro`, `run_cmd`,
   `initialize` or `#eval` (README). The certified core does not import `Lean` at all
   (`CRRGExamples/NoMeta.lean`).
2. **Lineage audit**: `#crrg_check_lineage` rejects any constant outside `CRRGCore` whose type or
   value mentions a private core name. Below, the forgery is built and the audit fails on it.

This module is not imported by any other example module, so the forged constant never reaches them.
-/

open Lean Meta Elab Command

/-- Probe2, adapted to the current `State` fields: a copy of any state with
`easierCount := 1000000`, built through the private constructor. -/
def forgeState (declName : Name) : CommandElabM Unit := do
  let mkN := Name.mkNum `_private.CRRGCore.State 0 ++ `CRRGCore.State.mk
  unless (← getEnv).contains mkN do throwError "constructor not in the environment"
  let (val, ty) ← liftTermElabM do
    let stConst ← mkConstWithFreshMVarLevels ``CRRGCore.State
    let goalTy := (← inferType stConst).bindingDomain!
    withLocalDeclD `root goalTy fun root => do
      withLocalDeclD `S (mkApp stConst root) fun S => do
        let p (f : Name) := mkAppM (``CRRGCore.State ++ f) #[S]
        let args := #[← p `fams, ← p `reg, ← p `leaves, ← p `conflicts, ← p `history,
                      mkNatLit 1000000, ← p `commitCount, ← p `record, ← p `root_key,
                      ← p `leaves_valid, ← p `conflicts_valid, ← p `conflicts_sound,
                      ← p `closeRoot, ← p `history_ok]
        let v ← mkAppM mkN args
        let v ← instantiateMVars (← mkLambdaFVars #[root, S] v)
        let t ← instantiateMVars (← inferType v)
        return (v, t)
  liftCoreM <| addDecl (.defnDecl (mkDefinitionValEx declName [] ty val .abbrev .safe [declName]))

elab "#forge_state" : command => forgeState `forgedBump

/-- Probe4: the same forgery under a name that imitates a private core name. The audit
exempts by declaring module only, so this is caught too. -/
elab "#forge_hidden_state" : command =>
  forgeState (Name.mkNum `_private.CRRGCore.State 0 ++ `hiddenBump)

#forge_state
#forge_hidden_state

/-- The forgery exists and type-checks in the kernel… -/
example : (forgedBump _ (CRRGCore.State.initial ⟨True⟩ [])).easierCount = 1000000 := rfl

-- …and the lineage audit rejects both, including the one hidden under a private-looking name.
/-- error: crrg: lineage violation, private core names used outside CRRGCore: forgedBump uses _private.CRRGCore.State.0.CRRGCore.State.mk; _private.CRRGCore.State.0.hiddenBump uses _private.CRRGCore.State.0.CRRGCore.State.mk -/
#guard_msgs in
#crrg_check_lineage
