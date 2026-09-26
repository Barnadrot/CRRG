import CRRGTools.Seal

/-!
# CRRGTools.Runner — checks used by the gate runner (`runner/crrg_runner.py`)

* `#crrg_check_defs_using c [N₁, …] [l₁, …]` — R1 on definitions, with the agreement lemmas named
  explicitly. A submitted file is meta-free, so it cannot use the `@[crrg_agree]` attribute (registering
  an attribute needs `import Lean`). The submission's manifest lists its agreement lemmas instead, and
  the same typed, directed rule applies (`isAgreementFor`).
* `#crrg_check_axioms M` — every constant declared in module `M` depends only on `propext`,
  `Quot.sound` and `Classical.choice`, and `M` declares no axiom. This rejects `sorry` (`sorryAx`),
  `native_decide` (`Lean.ofReduceBool`) and any new `axiom`.
-/

namespace CRRGTools

open Lean Elab Command Meta

/-- `#crrg_check_defs_using c [N₁, …] [l₁, …]`: R1 on definitions against named agreement lemmas. -/
elab "#crrg_check_defs_using " id:ident " [" ns:ident,* "]" " [" ls:ident,* "]" : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let lemmas ← ls.getElems.mapM fun l => liftCoreM <| realizeGlobalConstNoOverloadWithInfo l
  let env ← getEnv
  let sealedNs : Array Name := ns.getElems.map (·.getId)
  let inSealed (c : Name) : Bool := sealedNs.any (fun s => s.isPrefixOf c)
  let mut missing : Array Name := #[]
  for c in closure env n do
    if c == n then continue
    match env.find? c with
    | some (.defnInfo _) | some (.opaqueInfo _) =>
      unless inSealed c do
        let mut ok := false
        for lem in lemmas do
          if ← liftTermElabM (isAgreementFor lem c inSealed) then ok := true
        unless ok do missing := missing.push c
    | _ => pure ()
  unless missing.isEmpty do
    throwError "crrg: definitions without a sealed namespace or a typed agreement lemma: {missing}"
  logInfo m!"crrg definitions agree (R1): {n}"

/-- `#crrg_check_move_defs M S m [N₁, …] [l₁, …]`: R1 derived from the move itself. Every definition
declared in module `M` (the submission) that occurs in the closure of a fresh child claim of `m` must
(except a claim's own name, when the claim is exactly a named statement)
lie in a sealed namespace or have a typed agreement lemma among `l₁, …`. Definitions from earlier
modules were admitted before; the core and the toolchain are pinned. -/
elab "#crrg_check_move_defs " mod:ident s:term:max m:term:max " [" ns:ident,* "]" " [" ls:ident,* "]" :
    command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? mod.getId
    | throwError "crrg: module {mod.getId} is not imported"
  let lemmas ← ls.getElems.mapM fun l => liftCoreM <| realizeGlobalConstNoOverloadWithInfo l
  let sealedNs : Array Name := ns.getElems.map (·.getId)
  let inSealed (c : Name) : Bool := sealedNs.any (fun s => s.isPrefixOf c)
  let missing ← liftTermElabM do
    let fresh ← Term.elabTerm (← `(CRRGCore.Move.freshClaims (S := $s) $m)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let fresh ← (← listElems (← instantiateMVars fresh)).mapM fun e => withReducible (whnf e)
    let mut used : NameSet := {}
    let mut stmts : NameSet := {}
    for f in fresh do
      -- a claim that is exactly a named statement (`Leaf : Prop`) is the leaf itself, not a use
      if let some c := f.constName? then stmts := stmts.insert c
      for c in f.getUsedConstants do
        for d in closure env c do used := used.insert d
    let mut missing : Array Name := #[]
    for c in used.toArray.qsort Name.lt do
      unless env.getModuleIdxFor? c == some idx do continue
      if stmts.contains c then continue
      match env.find? c with
      | some (.defnInfo _) | some (.opaqueInfo _) =>
        unless inSealed c do
          let mut ok := false
          for lem in lemmas do
            if ← isAgreementFor lem c inSealed then ok := true
          unless ok do missing := missing.push c
      | _ => pure ()
    return missing
  unless missing.isEmpty do
    throwError "crrg: new definitions in the move's claims without a sealed namespace or a typed agreement lemma: {missing}"
  logInfo m!"crrg definitions agree (R1) for the move's fresh claims"

/-- The axioms a submission may depend on. -/
def allowedAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- `#crrg_check_axioms M`: no constant of module `M` uses an axiom outside `allowedAxioms`. -/
elab "#crrg_check_axioms " m:ident : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? m.getId
    | throwError "crrg: module {m.getId} is not imported"
  let decls := env.constants.fold (init := #[]) fun acc n _ =>
    if env.getModuleIdxFor? n == some idx then acc.push n else acc
  let decls := decls.qsort Name.lt
  let mut bad : Array String := #[]
  for d in decls do
    if let some (.axiomInfo _) := env.find? d then
      bad := bad.push s!"{d} is an axiom"
      continue
    let axs ← liftCoreM <| collectAxioms d
    let extra := axs.filter (fun a => !allowedAxioms.contains a)
    unless extra.isEmpty do bad := bad.push s!"{d} uses {extra.toList}"
  unless bad.isEmpty do
    throwError "crrg: disallowed axioms in {m.getId}: {String.intercalate "; " bad.toList}"
  logInfo m!"crrg axioms ok: {decls.size} declarations of {m.getId}"

end CRRGTools

namespace CRRGTools

/-- The kernel commit outcome as one line, for the runner. -/
def commitSummary {root : CRRGCore.Goal} (S : CRRGCore.State root) (m : CRRGCore.Move S) : String :=
  match CRRGCore.State.commit S m with
  | .ok (_, t) => s!"CRRG-COMMIT ok {reprStr t}"
  | .error r => s!"CRRG-COMMIT reject {reprStr r}"

end CRRGTools
