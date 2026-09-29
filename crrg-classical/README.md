# crrg-classical — the first slice of the faithful classical CRRG

A faithful CRRG should be a classical Lean proof, with Mathlib trusted. This package re-proves the core's
"certified easier" machinery on Mathlib objects and adds the modules that need Mathlib.

**A parallel library.**
- It may import Mathlib, pinned to `c5ea00351c` (`lakefile.lean`, `lake-manifest.json`).
- It depends on `../crrg-core` by path, for the bridge and for the crux-family model. The list-based core,
  its Lean-core build and its runner suite are unchanged, and nothing in crrg-core depends on this package.

| Declaration | Statement | Label |
|---|---|---|
| `PartialOrder Label`, `WellFoundedLT Label` | the core's label order as a Mathlib well-founded partial order | proved |
| `step_cutExpand`, `Step.wf'` | a positional step is a `Relation.CutExpand`, so `Step` is well-founded by `WellFounded.cutExpand` (3 lines, against about 60 in the core) | proved |
| `permStep_iff_cutExpand` | `PermStep ↔ CutExpand` on list images (replaces `Step.perm_commute`, `PermStep.acc_of_perm`, `PermStep.wf`) | proved |
| `dmlt_iff_transGen`, `transGen_cutExpand_iff_isDM`, **`dmlt_iff_isDM`** | the **bridge in both directions**: `DMLt l' l ↔ Multiset.IsDershowitzMannaLT ↑l' ↑l` | proved |
| `DMLt.wf'` | `DMLt` well-founded from `Multiset.wellFounded_isDershowitzMannaLT` | proved |
| `Credited`, `RecordRun`, `no_infinite_credits` | the record-low rule and "no run earns infinitely many credits", on multisets over any well-founded preorder | proved |
| `core_credit_classical`, `core_commit_classical`, `core_no_infinite_credits_classical` | the two cores certify the same moves, and the core's `no_infinite_credits` follows from the classical one | proved |

**`CRRGClassical/State.lean`: the credit machinery over multisets.** The core's `State` is kept; the record
and the new frontier are read as multisets through the bridge.

| Declaration | Statement | Label |
|---|---|---|
| `Move.withCert` (`_root_.CRRGCore.Move.withCert`), `withCert_credited` | a record certificate given as an `IsDershowitzMannaLT` proof; such a move is credited | proved |
| **`runner_credit_sound`** | the computable `creditOf` returning `certifiedEasier` implies the classical credit (the theorem the runner cites) | proved |
| `creditOf_sound_classical`, `commit_credit_record_classical` | the core's credit theorems over multisets | proved |
| `easierSucc_wf_classical` | `InvImage.wf` of `wellFounded_isDershowitzMannaLT` | proved |
| `recordRun_of_advance`, `no_infinite_credits_state` | core runs are a `RecordRun`; the classical `no_infinite_credits` gives the core's | proved |
| `Region.admit`, **`Region.admit_comm`**, `Region.admit_subset` | crux-family regions as `Finset` intervals; admission order-independence **in general** (`sdiff_sdiff_comm`) | proved |

**The other modules.**

| Module | Declarations | Label |
|---|---|---|
| `Family.lean` | crux families on `Finset`s: no claim without the guard; pointwise update, with non-dischargers and exclusion nodes untouched; monotone admission; `admit_comm` and **`admitAll_perm`** (any permutation of the evidence gives the same family) | proved, in general |
| `Family.lean` | `demo_orders_agree`, `demo_any_order`, `demo_x_after_two`, `demo_x_closed`, `demo_y_after`: the order results and the region arithmetic on crrg-core's **synthetic** crux family | proved (synthetic example) |
| `Route.lean` | `CRRGClassical.CertRoute.closes`: a classical route certificate; `commit_transition`, `allClosed_iff` | proved |
| `Stall.lean` | a stall and exit rule per crux: parking means the last `k` contracts were dry (`parked_last_dry`); progress unparks (`progress_unparks`); finitely many progress steps park (`eventually_parked`); a crux that never parks must keep producing outcomes labelled `newConflict` (`unparked_needs_conflicts`), compatible with `no_infinite_credits`. That a label marks a real new conflict is an assumption on the outcome log, not part of the theorem (v0.11.1) | proved |
| `Ledger.lean` | an evidence ledger for non-move results: recording never changes the frontier or the credit (`record_frontier_credit`, `recordAll_state`); after a refutation, a re-priced proposal must cite a newer ledger entry (`no_ingredient_refused`, `admitted_cites_new`) | proved |
| `Converse.lean` | `classCap_iff_listBound`: for a linear code given by a surjective syndrome map, a per-syndrome class cap and a list bound of the same size are equivalent (`card_listAt_eq`, via `c ↦ y − c`) | proved |

Axioms: every declaration printed in `CRRGClassical/Axioms.lean` uses at most `[propext, Classical.choice, Quot.sound]`
(see `BUILD.log`).

**Build.** Run `./build.sh`, which does `lake exe cache get` and then `lake build`, and writes `BUILD.log`. To reuse an
existing Mathlib build at the same revisions, place (or clone) its packages under `.lake/packages`; the committed
`lake-manifest.json` pins every revision.
