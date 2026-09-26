# The CRRG gate runner (Phase 1a)

`runner/crrg_runner.py MANIFEST.json` takes one submitted Lean file and a committed state. It emits **one**
JSON verdict:

```json
{"verdict": "accept" | "reject", "reasons": ["CODE", ...], "tag": "certifiedEasier" | "notCertifiedEasier" | null,
 "checks": {"lint": ..., "compile": ..., "axioms": ..., "lineage": ..., "d1": ..., "commit": ..., "r1": ...}}
```

The verdict is `accept` exactly when `reasons` is empty. The suite is `runner/run_tests.py` over
`runner/tests/*`: 40 cases, and the forgeries are run again with the lint bypassed. It runs in `build.sh`,
and the results are in `runner/TESTS.log`.

## What the runner does

**Manifest.** The gate supplies it, not the proposer. It holds:
- the submission file;
- the modules the submission may import (the state's module);
- the state `S` and move `m` as Lean terms;
- optionally, the sealed namespaces and the agreement lemmas for R1.

| Step | Check | Reason codes |
|---|---|---|
| lint | the source, with comments and strings removed, contains none of: `elab`, `elab_rules`, `macro`, `macro_rules`, `syntax`, `declare_syntax_cat`, `run_cmd`, `run_elab`, `run_meta`, `initialize`, `builtin_initialize`, `#eval`, `#eval!`, `#exit`, `unsafe`, `implemented_by`, `extern`. `set_option` is limited to an allow-list, which excludes `debug.*`. Imports are only `CRRGCore` and the manifest's modules, and none of these reaches `Lean`, `Lake`, `Std` or `CRRGTools`, checked transitively | `META_COMMAND`, `META_IMPORT`, `IMPORT_NOT_ALLOWED`, `FORBIDDEN_OPTION` |
| — | **a submission that fails the lint is never compiled or executed** | — |
| compile | the file elaborates and is kernel-checked on its own, as module `CRRGSubmission`, with only its own imports in scope | `COMPILE_ERROR`, `TIMEOUT` |
| axioms | every constant the submission declares depends only on `propext`, `Quot.sound` and `Classical.choice`, and the submission declares no axiom (`#crrg_check_axioms`) | `AXIOM` |
| lineage | no constant declared outside the `CRRGCore` modules mentions a private core name, whatever its own name (`#crrg_check_lineage`) | `LINEAGE` |
| D1 | the move's fresh child claims, reduced, are not definitionally equal at default transparency to a learned conflict's claim, nor to a registered key's claim (`#crrg_admit`). The second case must be resubmitted with `Child.old k` | `D1_CONFLICT`, `D1_REUSE` |
| commit | `State.commit S m` is evaluated. `.error r` rejects; `.ok (_, t)` reports the tag `t` | `COMMIT_REJECT:<Reject>`, `COMMIT_ERROR` |
| guards | when the manifest has `guard_claim` (a crux-family edge the contract consumes), every guard field of that edge in `families/<family>.json` is listed. Decidable fields hold on the supplied values, data fields name evidence, and a joint field has exactly one witness (`runner/guard_fields.py`, run before the lint) | `GUARD_UNKNOWN_EDGE`, `GUARD_FIELD_MISSING`, `GUARD_FIELD_FAILS`, `GUARD_JOINT_SPLIT` |
| R1 | every definition declared by the submission and used, transitively, by a fresh child claim lies in a sealed namespace or has a typed, directed agreement lemma from the manifest: `D … ↔ S …`, `S … ↔ D …` or `D … → S …`. A claim that is exactly a named statement is the leaf itself, not a use (`#crrg_check_move_defs`) | `R1` |

After the lint, every check runs and every reason is reported. When the axiom check fails, the commit step
is skipped rather than failed, because Lean will not evaluate a term that depends on `sorry`.

## What an `accept` guarantees

These guarantees assume that the Lean 4 v4.30.0 kernel and toolchain are sound, and that the trusted code is
correct. The trusted code is `CRRGCore`, `CRRGTools` and `runner/crrg_runner.py`.

1. **Soundness of the step.**
   - The submitted move type-checks in the kernel against the committed state, using only the standard
     axioms.
   - `State.commit S m` accepts it, so `commit_transition` holds: the new frontier is a `Transition` of the
     old one.
   - When the route closes, `Chain.closeRoot` and `CertRoute.closes` give the root claim, which is
     `Capstone d` by type.
2. **Lineage.** The submission cannot have produced a `State` except through `initial`, `commit`, `refute`
   and `learn`, for two independent reasons:
   - without meta commands, the elaborator refuses the private constructor (`private_ctor_syntax`);
   - even with the lint bypassed, the lineage audit rejects the Probe2 and Probe4 forgeries
     (`probe2_forgery`, `probe4_hidden_name`, "(lint bypassed)").
3. **No hidden trust.** Nothing in the submission ran as a metaprogram:
   - there are no meta commands or meta imports;
   - there is no `native_decide` (it depends on an extra axiom and is caught as `AXIOM`);
   - there is no `sorry` and no new axiom;
   - there is no kernel-bypassing option.
4. **No re-admission by definitional restatement.** A fresh claim is never definitionally equal to a learned
   conflict. Re-admission by key is refused by `commit` (`commit_no_conflict`). A dead route admits nothing
   (`commit_rootRefuted`).
5. **Canonical keys.** A fresh claim is never definitionally equal to a registered key. Duplicates must reuse
   the key.
6. **R1 on definitions.** Every new definition the move's claims depend on is sealed, or is tied to a sealed
   definition by a typed, directed lemma. Co-occurrence and vacuous lemmas do not count.
7. **Accounting.**
   - The reported tag is `creditOf`, computed by the kernel.
   - Credit is given only below the record (`creditOf_sound`, `commit_credit_record`).
   - No run earns infinitely many credits (`no_infinite_credits`).
   - Growth, restatement and grow-then-shrink are admitted without credit (`item4_growth`,
     `item4_grow_from_top`, `grow_then_shrink`).

## What stays outside the runner

- **Propositional restatements.** D1 is definitional. A restatement that is equivalent only by proof (the
  swapped conjunction, `propositional_restatement`) is admitted, and it is killed only when a detector supplies
  the implication to `State.learn` (Negatives 4b). Such detectors (two-way kernel arrows, the Referee) are not
  part of the runner.
- **The adapter to a frozen target statement.**
  - `Capstone` here is a stand-in, and the runner imports no Mathlib.
  - Instantiating `CertRoute` with a real frozen target statement is a downstream adapter package in the
    application's Lean tree.
  - Until that exists, an accept certifies a step towards the stand-in root only.
- **sha256 sealing.**
  - `#crrg_seal` is a 64-bit, name-sensitive declaration fingerprint.
  - The production seal is sha256 over a `lean4export` of the same closure, computed and signed by the gate.
  - The runner does not compare seals.
- **State custody.**
  - The runner reads the state as a Lean term named by the manifest, and reports a verdict.
  - Storing states, applying the commit, and signing verdicts belong to the gate.
  - The owner's pinning of `fams` at `initial` is also signed outside Lean.
- **The runner's own correctness.**
  - The lint is a text check, argued complete for Lean v4.30.0's meta surface listed above. It is not
    proved.
  - Each Lean-side check runs on the kernel's terms.
  - There is no Abadi–Lamport refinement proof of the runner and gate loop.
- **Judgement.** Whether a statement means what the mathematics means, and whether a move is useful, stay
  judgement (CRRG Spec §10).
- **Resources.** Each Lean call has a 600-second timeout (`TIMEOUT`). Submitted code runs only as elaboration
  and tactics, and as the pure evaluation of `commit`.

## Suite

| Group | Cases | Expected |
|---|---|---|
| forgeries | `probe2_forgery`, `probe4_hidden_name` | `META_COMMAND`, `META_IMPORT`; with the lint bypassed, also `LINEAGE` |
| lint | `eval_command`, `macro_command`, `skip_kernel_option`, `import_tools`, `import_audit_transitive`, `import_not_allowed` | the matching lint code |
| lint false positive | `comments_mention_meta` | accept |
| G1 without meta | `private_ctor_syntax` | `COMPILE_ERROR` |
| axioms | `sorry_cover`, `axiom_cheat`, `native_decide` | `AXIOM` |
| rung 2 | `item5_classical_cert` | `COMPILE_ERROR` (a classical certificate does not evaluate) |
| restatements | `d1_conflict_defeq`; `d1_reuse_live_key`, `classcap_restatement`, `item4_restate_measured_root` | `D1_CONFLICT`; `D1_REUSE` |
| negatives in the kernel | `readmit_by_key`, `dead_root` | `COMMIT_REJECT:learnedConflict`, `COMMIT_REJECT:rootRefuted` |
| R1 | `r1_missing`, `r1_vacuous`, `r1_fake_conjunction` / `r1_agree` | `R1` / accept |
| legitimate | `split_ab`, `range_split`, `close_by_computation`, `item4_growth`, `item4_grow_from_top`, `grow_then_shrink` | accept, with the right tag |
| known limit | `propositional_restatement` | accept (documented above) |
| guard-fields rule (the **synthetic** family `families/demo.json`) | `guard_accept` / `guard_missing_field`, `guard_data_no_evidence` / `guard_window_fails`, `guard_over_budget`, `guard_wrong_mode`, `guard_divides_fails` / `guard_joint_split` / `guard_unknown_edge` | accept / `GUARD_FIELD_MISSING` / `GUARD_FIELD_FAILS` / `GUARD_JOINT_SPLIT` / `GUARD_UNKNOWN_EDGE` |

Regenerate the cases with `python3 runner/make_tests.py`. The case sources are committed, so they can be
read without running anything.
