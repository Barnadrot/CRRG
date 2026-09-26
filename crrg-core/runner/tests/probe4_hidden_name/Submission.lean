import Lean
import CRRGExamples.Negatives
open Lean Meta Elab Command
open CRRGCore CRRGExamples

def forgeState (declName : Name) : CommandElabM Unit := do
  let mkN := Name.mkNum `_private.CRRGCore.State 0 ++ `CRRGCore.State.mk
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

elab "#forge_hidden" : command =>
  forgeState (Name.mkNum `_private.CRRGCore.State 0 ++ `hiddenBump)
#forge_hidden

namespace Sub
def move : Move (E1 8) :=
  Move.closeByComputation (E1 8) ⟨0, Nat.zero_lt_one⟩ (evenCert 8) rfl
end Sub
