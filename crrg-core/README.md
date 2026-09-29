# crrg-core — CRRG Phase 0: closing CRRG fully

A Lean package for the certified research-reduction core. Its rule is **propose → verify → commit or
reject**. It builds on three foundations:
- SMT-style **search narrowing**;
- Abadi–Lamport **refinement mappings**;
- **CWSS**, which is Fenzi–Moghaddas–Nguyen's, together with ArkLib's **guarded CWSS** implementation.

It keeps what already holds in CRRG v0.10 and addresses that version's gaps G1–G14 (listed gap by gap in
`STATUS.md`): G3 and G5–G11 have their content in Lean, G1 and G4 are closed by runner code and tooling rather than by
a Lean theorem, G2 and G12 are partly closed, G13 is outside the core, and G14 was dropped.

- **Toolchain.** `leanprover/lean4:v4.30.0`. There are no dependencies: Lean core only, no Mathlib, including
  for the multiset lift.
- **Build.** `./build.sh`, with `lean` and `lake` v4.30.0 and `python3` on PATH. It builds `CRRGCore`,
  `CRRGTools` and `CRRGExamples` from clean, runs the seal probes and the runner suite, and writes
  `BUILD.log`. The runner calls `lean` from a temporary directory, so with elan and a different default
  toolchain, set `ELAN_TOOLCHAIN=leanprover/lean4:v4.30.0` first.
- **Verified in `BUILD.log`.**
  - 37 headline declarations are printed with `#print axioms`, and **none depends on `Classical.choice`**.
    The axioms used are only `propext` and `Quot.sound`.
  - There is **no `sorry`** in `CRRGCore`.
  - The certified library (`CRRGCore`) does not import `Lean` (the meta framework); its only imports are
    its own modules.
  - Both seal probe pairs produce different seals.

**Review fixes.** The seven items of the design review are fixed, and the record-low credit rule is adopted.
The map from item to fix and probe is in `STATUS.md`.

## Layout

| Module | Role | Imports |
|---|---|---|
| `CRRGCore/Basic.lean` | goals, edges, finite splits, frontiers, the single replace operator, transitions, chains | none |
| `CRRGCore/Easier.lean` | "certified easier" as types: labels, the well-founded label order, the positional Dershowitz–Manna step and its well-foundedness | Basic |
| `CRRGCore/Guarded.lean` | guarded composition, escapes, no hidden composition debt, edge leaves, partition moves | Basic |
| `CRRGCore/State.lean` | the committed research state: registry, commit, conflicts, refute, learn, backtrack, easier accounting | Basic, Easier, Guarded |
| `CRRGCore/Route.lean` | the route's root is the capstone | State |
| `CRRGTools/Seal.lean` | **runner tools** over kernel terms: declaration seals, D1 (`#crrg_same_meaning`, `#crrg_admit`), the lineage audit, R1 on definitions, the informational rung-2 audit | `Lean`, CRRGCore |
| `CRRGExamples/*.lean` | the required examples and the negative controls (`#guard_msgs`), plus the axiom report | CRRGCore (and CRRGTools for Audit and Lineage) |
| `CRRGTools/Runner.lean` | runner-side checks: axioms per module, R1 from a move's fresh claims or named lemmas, the commit summary | CRRGTools.Seal |
| `runner/` | **the gate runner** (`crrg_runner.py`, one JSON verdict) and its negative-control suite (`tests/`, `run_tests.py`); see `RUNNER.md` | Python, Lean |
| `probes/seal/` | before/after file pairs whose seals must differ, run by `build.sh` | CRRGTools |
| `families/` | a **synthetic** crux family's guard in the runner's JSON form (`demo.json`), and `gen_lean.py`, which generates its Lean mirror `CRRGExamples/FamilyDemoJson.lean` (checked for staleness by `build.sh`) | Python |

`CRRGCore` imports nothing outside itself: the meta framework is in a separate library, `CRRGTools`. The
tools add no trust to any theorem. They are checks the gate runner performs, written in Lean rather than
shell.

## Runner obligations

These are the steps the gate runner must perform. They are not kernel theorems. `runner/crrg_runner.py`
implements all of them, and a negative-control suite tests them (`RUNNER.md`).

1. **Submitted files are meta-free.** A submitted file must not contain `import Lean`, `elab`, `macro`,
   `syntax`, `run_cmd`, `run_elab`, `initialize` or `#eval`. The kernel does not enforce `private`. With
   the meta framework, a file can build a `State` through the private constructor
   (`CRRGExamples/Lineage.lean`). The core itself cannot reach `addDecl` (`CRRGExamples/NoMeta.lean`).
2. **The lineage audit runs on every submitted environment.** `#crrg_check_lineage` must pass: no
   constant declared outside the `CRRGCore` modules may mention a private core name, whatever its own name.
3. **D1 runs at admission.** Before `commit`, the runner runs `#crrg_admit S m`:
   - it rejects a move whose fresh child claim is definitionally equal to a learned conflict;
   - it reports a fresh claim that is definitionally equal to a live key; the runner rejects that move
     (`D1_REUSE`), and the corrected proposal must reuse the key as `Child.old`.

   Propositional equivalents enter through `State.learn` once a detector supplies the implication.
4. **R1 on definitions.** `#crrg_check_defs leaf [sealed namespaces]` must pass for every new leaf. Since v0.11.1
   an agreement must be general and unconditional (see the table below); sealed status is still a namespace-prefix
   test, not pinned provenance.
5. **Seal policy.** The seal is a **name-sensitive declaration fingerprint**, not a meaning test.
   - Renaming an auxiliary changes it, by design.
   - Changing a constructor changes it (`probes/seal/`).
   - Planned, not built: production would compute sha256 over a `lean4export` of the same closure (STATUS G2).

## Theorems and what they close

### Foundation 1: search narrowing (SMT)

| Declaration | Statement | Closes |
|---|---|---|
| `Frontier` (Basic) | `closeRoot : (∀ g ∈ leaves, g.claim) → root.claim`; the root is a type index | kept from v0.10 |
| `Split` (Basic) | a finite list of children plus `discharge : (∀ c ∈ children, c) → parent` | kept; finite (G11) |
| `Frontier.replaceAt`, `replaceAt_transition` (Basic) | the one operator, and its invariant theorem | G1 |
| `Frontier.dead_of_refuted` (Basic) | a refuted leaf kills its decomposition, never the root | G5 |
| `rangeSplit`, `caseSplit` (Guarded) | partition moves whose coverage is a case split checked by the kernel | partition moves |
| `State.refute` (State) | `¬ P` for the exact registered `P` becomes a **learned conflict**; the state backtracks | G5 |
| `State.commit_rootRefuted` (State) | once the root is a learned conflict, **every** commit is rejected (`Reject.rootRefuted`) | a dead route admits nothing |
| `State.learn` (State) | propagates a conflict along a supplied implication, so a restatement under a new key is refuted too | G5, G12 |
| `State.commit_no_conflict` (State) | an accepted commit never admits a learned conflict | "a restatement cannot re-admit it" |

### Foundation 2: refinement mappings

| Declaration | Statement | Closes |
|---|---|---|
| `Transition`, `Transition.comp`, `Chain`, `Chain.closeRoot` (Basic) | checked chains back to the root | kept, plus chains |
| `State` with a **private constructor** (State) | in meta-free files, only `initial`, `commit`, `refute` and `learn` produce states | G1, together with the lineage audit |
| `State.commit_transition` (State) | **every accepted commit is a `Transition`** of the frontier | G1 |
| `State.commit` (State) | returns `Except Reject (State × Tag)`; `Reject` and `Tag` are typed and computed | G8 |
| `CertRoute`, `CertRoute.closes`, `CertRoute.refuted` (Route) | the root is `Capstone d` by type (Abadi–Lamport R1: the external statement is preserved) | G7: no `True`-valued links |
| `#crrg_check_defs` + `@[crrg_agree]` (CRRGTools) | R1 on definitions: every non-core definition a leaf uses is sealed, or has a **typed, directed** agreement lemma `∀ xs, D xs ↔ S …`, `∀ xs, S … ↔ D xs` or `∀ xs, D xs → S …`, with `D` applied to distinct bound variables and no other hypothesis (v0.11.1; v0.11.0 accepted agreements behind a discarded premise); co-occurrence does not count | R1 on definitions |
| `#crrg_check_lineage` (CRRGTools) | no constant outside `CRRGCore` mentions a private core name | G1 against metaprogramming |
| `WitnessMap.toEdge` (Guarded) | a counterexample map is R2 between zero-step specifications | kept |

### Foundation 3: guarded composition (CWSS, ArkLib's guarded CWSS)

| Declaration | Statement | Closes |
|---|---|---|
| `GuardedMap.toSplit`, `EscapeMap.toSplit` (Guarded) | both branches are committed as leaves | kept |
| `GuardedEdge.toSplit`, `escape_mem` (Guarded) | a guarded reduction commits the pass leaf `g → child` **and** the escape leaf `¬g → parent` | guards survive |
| `guardedComp`, `guardedComp_escapes` (Guarded) | composing `A ⇐[g₁] B` with `B ⇐[g₂] C` keeps `¬g₁ → A` **and** `g₁ ∧ ¬g₂ → B`; the composite guard is `g₁ ∧ g₂` | G6 |
| `conditionalSplit` (Guarded) | a conditional result enters only as a split whose premises are open leaves | no hidden composition debt |
| `hidden_debt_not_edge` (Guarded) | `¬ ∀ A B P, (A ∧ B → P) → Edge P B`: refining P into B has no witness | the two-pager's rejected refinement |
| `withEdgeLeaf` (Guarded) | a decomposition whose composition is unknown becomes a split with the composition as an open leaf | the two-pager's research question |

### Certified easier as types

| Declaration | Statement | Closes |
|---|---|---|
| `residual_sufficient`, `residual_equiv_of_two_way` (Easier) | a sufficient Z is at least as strong as X; equivalence needs a two-way reduction | the logical fact |
| `Label`, `Label.lt`, `Label.lt_wf` (Easier) | labels are `sized f n` or `top`; `lt` holds **only within one family, at a strictly smaller size**; well-founded, with no axioms. Nothing is below `top` | rung order (review item 1: no `top → sized` credit) |
| `Label.not_lt_top_top`, `Label.not_lt_cross`, `Label.not_lt_top` (Easier) | a restatement, a cross-family move, or an entry into a family from `top` is never a decrease | circling refused by construction |
| `Step`, `Step.acc_append`, `Step.wf` (Easier) | **replacing one element by finitely many smaller ones is well-founded** (Dershowitz–Manna, positional form, proved without Mathlib) | the production multiset lemma |
| `PermStep`, `DMLt`, `PermStep.wf`, `DMLt.wf` (Easier) | the transitive closure of permutation-then-step: the multiset DM order on label lists, well-founded | the record order |
| `MechCert`, `MechCert.settle` (Easier), `Move.closeByComputation` (State) | rung 2 **in the kernel**: a two-way decision procedure plus `h : c.decide () = true`, usually `rfl`, closes the leaf. The kernel runs the program. A classical certificate cannot be evaluated, so `rfl` fails | rung 2 (review item 5) |
| `Family`, `Family.close_of_step` (Easier) | a uniform step to strictly smaller instances closes the family | why rung 3 is right |
| `LabelOK`, `Entry` (State) | a `sized` label must be an actual instance of an **owner-pinned** family (`State.fams`, fixed at `initial`); a measured route is **born measured** (`initial … rootLabel hLabel`) | G10 |
| `State.record`, `State.creditOf`, `creditOf_sound` (State) | **record-low rule**: a move is credited only if its new frontier labels are DM-below the **record**, the labels of the last credited frontier. The tag is computed | review item 1, grow-then-shrink |
| `State.commit_credit_record` (State) | a credited commit lowers the record in `DMLt` | local → frontier, for commits |
| `State.easierSucc_wf` (State) | no infinite chain of certified-easier commits | the counted channel |
| `State.no_infinite_credits` (State) | **no run earns infinitely many credits**, whatever mix of commits, refutations and learned conflicts it makes | circling impossible in mixed runs |

### Examples (`CRRGExamples/`), each checked by `rfl`, `decide`, or `#guard_msgs`

| # | Example | Result |
|---|---|---|
| 1 | `P = A ∧ B` split into `{A, B}` | accepted; leaves `[1, 2]`; not certified easier (unmeasured) |
| 2 | refining P into B when only `A ∧ B ⊢ P` | rejected: no witness exists (`hidden_debt_not_edge`); the conditional split is accepted |
| 3 | the Weil pattern on `n % 2 = 0 ∨ n = 1` (true at 8, false at 3) | refining to `n % 2 = 0`: not credited; refining to `∃ k, n = 2k`: sound, **not credited**; settling `8 % 2 = 0` by `closeByComputation … rfl`: **credited**; `3 % 2 = 0` refuted by the same certificate |
| 4 | class-cap-style restatement (`ListBound` ⇝ `ClassCap`) | accepted, **no credit**; D1 detects it |
| 4b | the swapped conjunction `n ≤ 10 ∧ 2 ≤ n` vs `2 ≤ n ∧ n ≤ 10` | D1 misses it (not defeq); refuting `direct 11` and supplying `direct_iff_swapped` to `learn` kills the swapped leaf |
| 5 | refute `1 = 2`, then re-admit it | by key: **rejected** (`learnedConflict 1`). As `OneEqTwo` (defeq): `#crrg_admit` **rejects**. As `1 = 2 ∧ True`: accepted until `learn`, then backtracked |
| 5b | refute the root | every later commit is **rejected** (`rootRefuted`) |
| 6 | owner-pinned range family, root born measured at size 10 | `[0,9] → [0,4],[5,9]` and `[0,4] → [0,1],[2,4]` credited; restating `[0,4]` not credited; closure credited |
| 6b | growth, root restatement, grow-then-shrink | growing `[5]` to `[20]`: not credited; restating the root: not credited; shrinking `[20]` back to `[5]`: locally easier, but **not credited** (not below the record) |
| 7 | guarded move | commits the pass leaf and the escape leaf |
| 8 | rung-2 audit (informational) | `evenCert` passes; a noncomputable classical certificate and a choice-using one fail |
| 9 | D1 and seals | `ListBound ≡ ClassCap` detected; `ListBound` versus `R` refused; seals printed |
| 10 | R1 on definitions | no lemma: refused; `→ True`: refused; the review's conjunction of tautologies: **refused**; a real `↔`: passes |
| 11 | forging a `State` | by syntax: `State.mk` unknown and `{ … }` refused. By metaprogramming (`Lineage.lean`): the forgery type-checks in the kernel, and `#crrg_check_lineage` **rejects** it, including under a private-looking name (exemption is by module only). The legitimate examples pass the audit |
| 11b | admission | defeq restatement of a conflict rejected; propositional one passes D1; a defeq copy of live keys reported for reuse (`[0, 2]`) |
| 12 | capstone route | a closed route at `d = 7` yields `Capstone 7` |
| 13 | crux family (`CruxFamily`, **synthetic**): one shared guarded edge, four members | only a member that discharges the guard and needs a bill can use the edge; one admission updates every member by the same rule; four admitted results in either order give the same states |
| 14 | guard agreement (`FamilyAgreement`, **synthetic**) | `families/demo.json` and `CruxFamily.guard` have the same fields, kinds and constants, and give the same verdict on 17 samples |
| 15 | guarded lane (`Lane`, **synthetic** instance) | "`b ≤ a` gives `b * b ≤ a * a`" without its guard `0 ≤ b`: no unguarded edge at `(1, -3)`, and the join is stuck on the escape leaf |
| probes | seals (`probes/seal/`) | rename pair: different; inductive constructor `Claim 7` vs `Claim 8`: different |

## What this package does not do

See `STATUS.md` for the full list. In short:
- the seal is a 64-bit, name-sensitive declaration fingerprint, not a cryptographic hash or a meaning test;
- restatement detection is definitional (D1, at admission) plus supplied implications (`learn`);
- lineage, D1 admission and R1-on-definitions are runner checks in Lean meta, not kernel theorems;
- owner pinning happens at `initial` and is signed outside Lean;
- the gate runner that writes states is trusted, and its correctness is stated, not proved.
