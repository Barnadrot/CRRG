import Lean
import CRRGCore

/-!
# CRRGTools.Seal — meta tools for the gate runner

This library imports `Lean` and the certified core. The certified core never imports it, and files
submitted by seats must not import it (README, "Runner obligations"). None of these tools adds
trust to a kernel theorem. Each is a check the runner performs over kernel terms.

* `#crrg_seal c` — **declaration fingerprint** (review item 7, fixed). It hashes complete
  declarations over the non-core dependency closure:
  - kind, universe parameters and type;
  - the value, for definitions and opaques;
  - for inductives, the block, parameter and index counts, the constructor list and each
    constructor's declaration; for constructors, their inductive.

  **Name policy: the seal is name-sensitive by design.** It fingerprints declarations; it does not
  test meaning. Renaming an auxiliary changes it. Meaning equality is `#crrg_same_meaning` (D1) or a
  supplied implication (`State.learn`). The hash is Lean's 64-bit structural hash. The runner
  should compute sha256 over a canonical export (`lean4export`) of the same closure.
* `#crrg_check_lineage` — **G1 lineage audit.** Rejects every constant defined outside the
  `CRRGCore` modules whose type or value mentions a private `CRRGCore` name: the `State`
  constructor, `applyMove`, `withConflict`. Exemption is by declaring module only, never by name. The kernel does not enforce `private`, so this check
  closes the metaprogramming route (the review's Probe2).
* `#crrg_admit S m` — **D1 at admission** (review item 6). Rejects a move whose fresh child claim
  is definitionally equal to a learned conflict. It reports a fresh claim that is definitionally
  equal to a live registered key, so that key is reused instead.
* `#crrg_check_defs c [N₁, …]` with `@[crrg_agree]` — **R1 on definitions** (review item 8,
  fixed). Every non-core definition in `c`'s closure must lie in a sealed namespace or have a
  *typed, directed* agreement lemma: after its binders, `D … ↔ S …`, `S … ↔ D …` or `D … → S …`,
  with `D` the new definition's head and `S` a sealed head. Co-occurrence is not enough.
* `#crrg_check_mech c` — informational rung-2 audit. Settlement happens in the kernel
  (`Move.closeByComputation` with `h : c.decide () = true`, typically `rfl`); this only reports
  whether the certificate's own definition is computable and choice-free.
-/

namespace CRRGTools

open Lean Elab Command Meta

/-- Agreement lemmas between a definition and the sealed definitions (R1 on definitions). -/
initialize crrgAgreeAttr : TagAttribute ←
  registerTagAttribute `crrg_agree
    "agreement lemma: a typed, directed relation between a definition and a sealed definition"

/-- Constants from Lean's own core are not followed (the toolchain pins them). -/
def isCoreConst (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let root := env.header.moduleNames[idx.toNat]!.getRoot
    root == `Init || root == `Lean || root == `Std || root == `Lake
  | none => false

/-- The constants a declaration's meaning depends on. -/
def meaningRefs : ConstantInfo → Array Name
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => v.type.getUsedConstants.push v.induct
  | ci => ci.type.getUsedConstants

/-- The transitive closure of non-core constants that `n` depends on. -/
partial def closure (env : Environment) (n : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[n]
  let mut out : Array Name := #[]
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if isCoreConst env c && c != n then continue
    match env.find? c with
    | none => continue
    | some ci =>
      out := out.push c
      for r in meaningRefs ci do
        unless seen.contains r do stack := stack.push r
  return out.qsort Name.lt

/-- The fingerprint of one complete declaration. -/
def declHash (ci : ConstantInfo) : UInt64 :=
  let base := mixHash (hash ci.name) (mixHash (hash ci.levelParams) ci.type.hash)
  match ci with
  | .defnInfo v => mixHash base (mixHash 1 v.value.hash)
  | .opaqueInfo v => mixHash base (mixHash 2 v.value.hash)
  | .thmInfo _ => mixHash base 3
  | .axiomInfo _ => mixHash base 4
  | .inductInfo v => mixHash base (mixHash 5 (hash (v.numParams, v.numIndices, v.all, v.ctors, v.isRec)))
  | .ctorInfo v => mixHash base (mixHash 6 (hash (v.induct, v.cidx, v.numParams, v.numFields)))
  | .recInfo v => mixHash base (mixHash 7 (hash (v.numParams, v.numIndices, v.numMotives, v.numMinors)))
  | .quotInfo _ => mixHash base 8

/-- The seal: the fingerprints of the closure, in sorted name order. -/
def sealHash (env : Environment) (n : Name) : UInt64 := Id.run do
  let mut h : UInt64 := 7
  for c in closure env n do
    if let some ci := env.find? c then h := mixHash h (declHash ci)
  return h

/-- `#crrg_seal c` prints the declaration fingerprint of `c` and the size of its closure. -/
elab "#crrg_seal " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  logInfo m!"crrg seal {n}: {(sealHash env n).toNat} (closure of {(closure env n).size} declarations)"

/-- Definitional equality of two `Prop` constants at default transparency (D1). -/
def sameMeaning (a b : Name) : TermElabM Bool := do
  let ea ← mkConstWithLevelParams a
  let eb ← mkConstWithLevelParams b
  withTransparency .default <| isDefEq ea eb

elab "#crrg_same_meaning " a:ident b:ident : command => do
  let na ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo a
  let nb ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
  let same ← liftTermElabM <| sameMeaning na nb
  logInfo m!"crrg same meaning {na} {nb}: {same}"

elab "#crrg_assert_restatement " a:ident b:ident : command => do
  let na ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo a
  let nb ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
  unless (← liftTermElabM <| sameMeaning na nb) do
    throwError "crrg: {na} and {nb} are not definitionally equal"
  logInfo m!"crrg restatement detected (D1): {na} ≡ {nb}"

/-! ## Lineage (G1) -/

/-- Is `n` a private name of the certified core? -/
def isCorePrivate (n : Name) : Bool :=
  (n.toString (escape := false)).startsWith "_private.CRRGCore."

/-- Is `n` declared in a module of the certified core? -/
def inCoreModule (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!.getRoot == `CRRGCore
  | none => false

/-- The constants outside the core modules that reference a private core name. Exemption is by
**module only**: a constant declared outside `CRRGCore` is checked even if its own name imitates a
private core name. The result is sorted, so reports are deterministic. -/
def lineageOffenders (env : Environment) : Array (Name × Name) :=
  let bad := env.constants.fold (init := #[]) fun acc n ci =>
    if inCoreModule env n then acc else
      let refs := ci.type.getUsedConstants ++
        (match ci.value? (allowOpaque := true) with
         | some v => v.getUsedConstants
         | none => #[])
      match refs.find? isCorePrivate with
      | some p => acc.push (n, p)
      | none => acc
  bad.qsort (fun a b => Name.lt a.1 b.1)

/-- `#crrg_check_lineage` fails if any constant outside the core references a private core name. -/
elab "#crrg_check_lineage" : command => do
  let bad := lineageOffenders (← getEnv)
  unless bad.isEmpty do
    let pairs := bad.toList.map fun (n, p) => s!"{n} uses {p}"
    throwError "crrg: lineage violation, private core names used outside CRRGCore: {String.intercalate "; " pairs}"
  logInfo m!"crrg lineage ok: no constant outside CRRGCore references a private core name"

/-! ## Admission: D1 against learned conflicts and registered keys -/

/-- Unfold a list expression into its elements (by weak-head normalization). -/
partial def listElems (e : Expr) : MetaM (List Expr) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``List.cons, #[_, h, t]) => return h :: (← listElems t)
  | (``List.nil, _) => return []
  | _ => throwError "crrg: cannot unfold list {e}"

/-- A `(key, claim)` pair. -/
def pairElems (e : Expr) : MetaM (Nat × Expr) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``Prod.mk, #[_, _, k, p]) =>
    match ← evalNat (← whnf k) with
    | some n => return (n, p)
    | none => throwError "crrg: cannot evaluate key {k}"
  | _ => throwError "crrg: not a pair {e}"

/-- `#crrg_admit S m`: D1 at admission. Rejects a fresh claim definitionally equal to a learned
conflict, and reports fresh claims definitionally equal to live registered keys. -/
elab "#crrg_admit " s:term:max m:term:max : command => do
  liftTermElabM do
    let fresh ← Term.elabTerm (← `(CRRGCore.Move.freshClaims (S := $s) $m)) none
    let confl ← Term.elabTerm (← `(CRRGCore.State.conflictClaims $s)) none
    let regd ← Term.elabTerm (← `(CRRGCore.State.registeredClaims $s)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let fresh ← (← listElems (← instantiateMVars fresh)).mapM fun e => withReducible (whnf e)
    let confl ← (← listElems (← instantiateMVars confl)).mapM fun e => pairElems e
    let regd ← (← listElems (← instantiateMVars regd)).mapM fun e => pairElems e
    for f in fresh do
      for (k, c) in confl do
        if ← withTransparency .default <| isDefEq f c then
          throwError "crrg admission: fresh claim {f} is definitionally equal to learned conflict {k}"
    let mut reuse : Array (Nat × Expr) := #[]
    for f in fresh do
      for (k, c) in regd do
        if ← withTransparency .default <| isDefEq f c then reuse := reuse.push (k, f)
    if reuse.isEmpty then
      logInfo m!"crrg admission: D1 clean ({fresh.length} fresh claims)"
    else
      logInfo m!"crrg admission: D1 clean; reuse keys for definitionally equal fresh claims: {reuse.toList.map (·.1)}"

/-! ## R1 on definitions -/

/-- The head constant of an application, if any. -/
def headConst (e : Expr) : Option Name := e.getAppFn.constName?

/-- Is the tagged lemma `lem` a typed, directed agreement between `c` and a sealed definition?
Accepted shapes: `∀ xs, c xs ↔ s …`, `∀ xs, s … ↔ c xs`, and `∀ xs, c xs → s …`, where `c` is applied to
distinct bound variables (a general agreement, not one instance) and the lemma has no hypothesis other than the
antecedent `c xs` of the directed form.

v0.11.1: the v0.11.0 check discarded every binder before matching, so `∀ n, False → (c n ↔ s n)` and a specialized
`c 0 ↔ s 0` were accepted, and the directed form could never match because the telescope had already consumed its
arrow (independent audit, 2026-09-29, S1-04). -/
def isAgreementFor (lem c : Name) (inSealed : Name → Bool) : MetaM Bool := do
  let some ci := (← getEnv).find? lem | return false
  forallTelescope ci.type fun xs body => do
    let sealedHead (e : Expr) := match headConst e with
      | some h => inSealed h
      | none => false
    -- `c` applied to distinct bound variables only
    let general (e : Expr) : Bool :=
      headConst e == some c &&
        (let args := e.getAppArgs
         args.all Expr.isFVar &&
           (args.map Expr.fvarId!).toList.eraseDups.length == args.size)
    let mut hyps : Array Expr := #[]
    for x in xs do
      if ← Meta.isProp (← inferType x) then hyps := hyps.push x
    match body.getAppFnArgs with
    | (``Iff, #[a, b]) =>
      return hyps.isEmpty && ((general a && sealedHead b) || (general b && sealedHead a))
    | _ =>
      -- the directed form: the telescope took the antecedent `c xs` as the last binder
      if hyps.size != 1 || xs.isEmpty then return false
      let h := xs[xs.size - 1]!
      if hyps[0]! != h then return false
      if body.containsFVar h.fvarId! then return false
      return general (← inferType h) && sealedHead body

/-- Is there a tagged agreement lemma for `c`? -/
def hasAgreement (c : Name) (inSealed : Name → Bool) : MetaM Bool := do
  let env ← getEnv
  let tagged := env.constants.fold (init := #[]) fun acc n _ =>
    if crrgAgreeAttr.hasTag env n then acc.push n else acc
  for lem in tagged do
    if ← isAgreementFor lem c inSealed then return true
  return false

/-- `#crrg_check_defs c [N₁, …]`: R1 on definitions with typed, directed agreement lemmas. -/
elab "#crrg_check_defs " id:ident " [" ns:ident,* "]" : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let sealedNs : Array Name := ns.getElems.map (·.getId)
  let inSealed (c : Name) : Bool := sealedNs.any (fun s => s.isPrefixOf c)
  let mut missing : Array Name := #[]
  for c in closure env n do
    if c == n then continue
    match env.find? c with
    | some (.defnInfo _) | some (.opaqueInfo _) =>
      unless inSealed c do
        unless ← liftTermElabM (hasAgreement c inSealed) do missing := missing.push c
    | _ => pure ()
  unless missing.isEmpty do
    throwError "crrg: definitions without a sealed namespace or a typed agreement lemma: {missing}"
  logInfo m!"crrg definitions agree (R1): {n}"

/-! ## Rung 2 (informational) -/

elab "#crrg_check_mech " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  if isNoncomputable env n then
    throwError "crrg: {n} is noncomputable, so it is not a rung-2 decision procedure"
  let axs ← liftCoreM <| collectAxioms n
  if axs.contains ``Classical.choice then
    throwError "crrg: {n} depends on Classical.choice, so it is not a rung-2 decision procedure"
  logInfo m!"crrg mechanical certificate audited: {n}, axioms {axs}"

end CRRGTools
