# CRRG — External Review 2 packet

**Prepared for:** External Review 2, per `Spec.md` §12.
**CRRG:** `Barnadrot/CRRG`, branch `crrg-hardening`.
**Downstream:** `Barnadrot/proximity-research`, three experiment branches.
**Do not begin CRRG-directed live Soundness research before this review.**

---

## 0. Exact artifacts under review

| what | where |
|---|---|
| CRRG staging line | `crrg-hardening` |
| CRRG pinned by Stage B/C adapters | `003b7fa7263a88246192532c30f17f859de84991` |
| CRRG pinned by the Stage D adapter | `af267674f22392e5778491fc30f9bfdbad2067fa` |
| Stage B — known-proof calibration at 6399 | `crrg-stage-b-yukon` @ `951ef126` |
| Stage C — source-visible reconstruction calibration | `crrg-stage-c-yukon` @ `339a705e` |
| Stage D — frozen iter165 research backtest | `crrg-stage-d-yukon` @ `2dc5912f` |
| Stage D research checkout base | `f758c1b18a301fe76675cb628027360268bb15cb` (Yukon iteration 165) |

`main` is untouched and still at the last reviewed state. Nothing has been merged
into it (§3.1).

---

# THE FOUR FINDINGS

These are the results of the programme. Everything after §5 is supporting
evidence.

---

## Finding 1 — a blind agent rediscovered a post-cutoff obstruction, and applied it where the historical lane did not

**This is the strongest evidence in the packet, and it needs to be stated
precisely, because the precise version is stronger than the loose one.**

### What the Stage D agent did

Working in a checkout frozen at iteration 165 — **no git remote and no
post-cutoff commit in its object store**, so the corpus boundary was structural
and hard; network blocking was soft (see §9) and **no network attempt was
observed** — an agent was given the sealed obligation

```lean
StageD.T2Obligation :=
  ∀ v, v ∉ IRSProfile.baseCode →
    Code.Lambda (baseCode ⊔ span {v}) δ₇₄₈₇ ≤ mcaCap
```

It delivered `StageD.Attempts.T2 : ¬ StageD.T2Obligation`.

The witness is a **weight-one word** `spike`. It is not a codeword, because a
nonzero codeword has weight at least `d_min = 131073`. But `baseCode ⊔ span{spike}`
contains the entire scalar line `{a·spike : a ∈ Field}`, and every point of that
line is at Hamming distance `1` from `0` — far inside the radius. So

```text
Λ(baseCode ⊔ span{spike}, δ₇₄₈₇)  ≥  |Field| = p⁶ ≈ 9.36 × 10⁵⁵
```

against `mcaCap ≈ 2.75 × 10¹⁷`. A companion theorem, `T2FalseForEveryBudget`,
shows the same construction kills the obligation's *shape* at every budget below
`p⁶`, so no admissible `Bmca` rescues it.

### What the historical lane did, 11 iterations later

Iteration **176** — post-cutoff, invisible to the agent — recorded
`YukonLineRouteRefuted.lean`:

> Take `U₀ = 0` and `U₁ = ε` with `wt(ε) = 1` … for EVERY `z`, the line point
> `z·ε` agrees with the codeword `0` on `≥ n − 1 = 262143` coordinates … So
> `lineAgreeSet baseCode δ U = univ`, of size `|F| = p⁶ ≈ 9.36 × 10⁵⁵`, while
> every admissible `Bm` is at most `274980728110795087 ≈ 2.7 × 10¹⁷`.

**Same witness, same mechanism, same `p⁶` obstruction, comparable budget scale.**

The budgets are *not* the same integer, and it would be wrong to say they were.
Both derive from `⌊p⁶/2¹²⁸⌋ = 274980728111395087` minus that route's own
list-side charge, and the charges differ:

| | admissible budget | charge deducted |
|---|---|---|
| iter176, line-count route | `274980728110795087` | `600000` |
| Stage D, extension-list route | `274980727046041871` | `2 · 532676608` |

Both are ≈ `2.75 × 10¹⁷`, and both are short of `p⁶ ≈ 9.36 × 10⁵⁵` by nearly
forty orders of magnitude. That gap, not the exact integer, is what makes the
obstruction fatal on either route.

### The part that is not merely a rediscovery

Iteration 176 applied the obstruction to the **line-count** interface
(`yukonMCACountAt_of_line_counts`). The Stage D agent applied it to the
**extension-list** interface (`yukonMCACountAt_of_extension_lists`, consumed by
`protocolClaim7487_of_base_list`). These are two parallel T2-side interfaces that
both existed at the cutoff, and the same weight-one word kills both for the same
reason.

**The historical lane never propagated it to the second one.** Iteration **181**
re-examined exactly this question — which routes survived 176 — and concluded:

> Plus `YukonT1Composition.protocolClaim{7487,9433}_of_base_list`, a variant
> taking a base list bound. **None of these goes through `lineAgreeSet`.** … So
> 176 killed the chains that ADDITIONALLY reduced the MCA count via the vacuous
> line-count step; **it did not kill the targets.**

And the commentary inside `YukonT1Composition.lean` itself — **byte-identical at
the cutoff and at iteration 194** — still calls the extension-list hypothesis

> an equally open list bound, on a LARGER code

It is not open. It is false, and now provably so.

### How this was checked rather than asserted

The claim "`T2Obligation` is the seam's own argument" is the load-bearing one: if
it were a mis-transcription, the finding would be about the CRRG harness rather
than about the mathematics, and the correct outcome would have been `MALFORMED`.
It was verified by the kernel, not by reading:

```lean
example (h1 : T1Obligation) (h2 : T2Obligation) : ProtocolClaim 7487 349526 1048576 :=
  protocolClaim7487_of_base_list mcaCap mcaCap_pos h1 h2 budget_at_cap
```

compiles. That is a kernel proof that the sealed leaf **is** the seam's fourth
argument at `Bmca := mcaCap`. So the unsatisfiable hypothesis is the
development's, not the harness's.

### What it is fair to conclude

An eleven-iteration lookahead was reproduced in one session by an agent that
could not reach it — and then carried one step further than the record ever took
it. That is a real result about CRRG's value, and it should still be read with
its limits: **n = 1**, the obstruction is elementary once seen, and CRRG's
contribution was to make the obligation *exact and refutable*, not to find the
witness.

---

## Finding 2 — a route died and the target did not move

`ProtocolClaim 7487 349526 1048576` is neither proved nor refuted. It is
byte-identical to what it was before the experiment.

What died is one *decomposition* of it. `StageD.root_of_T1_T2` is still a true
theorem; it is now known to be vacuous, because one of its hypotheses is false.
Both facts are simultaneously in the graph, which is the point.

The frozen root survived because nothing in the calculus can move it:

| mechanism | why the root cannot drift |
|---|---|
| `Frontier root` | the root is a **type parameter**; a refinement that moved it would be a value of a different type |
| `refineLeaf` / `splitLeaf` | both return `Frontier yukonRoot`, and no operator produces anything else |
| type-link | `yukonRoot.claim = ProtocolClaim 7487 349526 1048576 := rfl`, with three neighbouring claims asserted to fail |
| substitution detection | a different `ProtocolClaim` in an attempt is reported and rejected absent a certified edge |

Neither agent proposed a substitution. Under §9.3.3 the agents were **not** told
that a later executor had regressed to an easier target; the control was left
unprompted, and there was nothing to reject.

This is the sentence worth carrying out of Stage D: the experiment changed
exactly the part of the research state that the theorem justified, and nothing
else.

---

## Finding 3 — an honest null: substantial certified work, `UNCHANGED` graph state

T1 was not closed, refuted, or found malformed. The graph state is `UNCHANGED`.

That null is not empty. The agent delivered kernel-checked proofs that **every
upper-bound certifier in the checkout is silent at this radius**:

- the radius-parametric second-moment interface is unsatisfiable **for every**
  list size `M` — it does not give a weak bound, it gives no bound;
- the third-moment overlap constraint is satisfied outright;
- Guruswami–Sudan certifies nothing at this agreement for **every** multiplicity
  and weighted-degree bound, with the gap hypothesis discharged rather than left
  vacuous;
- the shortfall to the Johnson integer wall is `10601` coordinates.

Refutation was unavailable too: the only lower-bound construction in the checkout
maxes at `715` in band, a factor of `745000` under the cap.

**A system that only rewards closure would have recorded this iteration as
nothing.** CRRG records it as nothing *on the frontier* — correctly, since the
obligation is exactly as open as before — while the diagnostics survive in the
tree as ordinary theorems. The distinction between "the researcher did nothing"
and "the certified graph did not move" is one CRRG can express and a prose log
usually cannot.

---

## Finding 4 — logical validity is not strategic value, and the kernel cannot tell them apart

**The T1 agent found a legal move that would have scored, and declined it.**

`t1_of_family_bound`, in its attempt file, is a compiled rootward implication
into T1. Wrapped as `EdgeRefinement .t1` it would have typechecked, and the gate
would have recorded **`REFINED`** — a graph mutation, correctly certified, on the
board.

Every mechanical check would have passed. The edge is real. The direction is
rootward. Siblings survive. The root does not move.

The agent did not submit it, and said why: the child implies the leaf *and the
leaf implies the child*, so the frontier would be no easier afterwards, and the
lift is already committed elsewhere in the checkout. It left the arrow in the
file, named and documented, unclaimed.

### Why this is a limit and not a triumph

CRRG guarantees **sufficiency**. It does not, and cannot, prove that a child is
easier than its parent — §10 says so directly. A strength-preserving reshape and
a genuine reduction are indistinguishable to the kernel, because the difference
is not a property of the implication.

So the frontier would have *looked* like it moved while the mathematics stood
still, and no check in this repository would have objected. **Here the discipline
came from the agent, not from the gate.**

The consequence for deployment is concrete: **admission of a refinement to the
active frontier is scheduler and audit policy, not a kernel property.** A
`REFINED` outcome should be read as "this move is *permitted*", never as "this
move is *progress*". Any future scheduler that counts refinements will be
optimising something CRRG does not certify.

This is one observation and must not be read as a property of agents in general.
It is the datum a reviewer should look at hardest.

---

## 5. The artifact-recovery caveat

Preserved verbatim, as required:

> **The current T2 result is mathematically reverified, but byte identity with
> the first delivered file cannot be established.**

What happened: the Stage D gate self-test must write `StageD/Attempts/<id>.*`,
because those are the paths the gate reads. Its cleanup trap removed them on
exit — including files it had not written. Both agents' delivered files were
destroyed minutes after the gate had verified them, while still untracked, so
nothing warned and git could not restore them.

Both agents were resumed and asked to reproduce their files verbatim from
context, explicitly as evidence recovery rather than improvement. Both rebuild
clean and both re-verify through the gate to the same observations — T1
`UNCHANGED`, T2 `REFUTED` with seal intact and kernel-3 axioms. The T1 agent
reports no detectable difference. The T2 agent reports that byte-identity cannot
be independently confirmed, since no copy survived to compare against.

**The verdicts are re-derived by the kernel and the gate. The files are faithful
reconstructions, not originals.** A reviewer should treat the T2 refutation's
*mathematics* as verified and its *provenance* as reconstructed.

The defect is fixed: pre-existing attempts are stashed and restored on every exit
path including `INT`/`TERM`, verified with decoy files. A measurement harness
that can delete the results it exists to measure will eventually delete the one
that mattered and leave a plausible record behind; that is why this is in the
findings section and not in an implementation log.

---

## 6. Stage results

### Stage B — known-proof calibration at 6399 (`951ef126`)

The certified **root lineage** contains the decomposition, which is what §9.1
requires and what an earlier iteration failed:

```text
ProtocolClaim 6399 307083 1048576
  ├── admissible                                    leaf
  ├── score                                         leaf
  └── reduction  --refineLeaf-->  analytic conclusion
                 --splitLeaf-->   ├── MCA term --refineLeaf--> alignment premise   leaf
                                  ├── Johnson/list term                            leaf
                                  └── field-capacity budget                        leaf
```

Five leaves; `closeRoot` consumes a total function over the task index, so none
can be skipped. `scripts/squeeze/yukon_verify.sh` passes **unchanged**, exit 0.
Nine asserted rejections in the adapter.

**Finding carried forward:** a test had to be deleted *because it passed*. In a
completed development every leaf is inhabited, so `Edge child ⟨True⟩` is
genuinely provable for every leaf — edge *existence* is evidence of nothing in a
retrospective calibration. Only the exact type-link is.

### Stage C — source-visible reconstruction calibration (`339a705e`)

Seven sealed candidates, fresh agent context each, reference proofs mechanically
forbidden. **Six `CERTIFIED`, one `REFUTED`** with a real `¬P`. Zero forbidden
routes, seal violations, weakening attempts or substitutions.

Three limits are recorded in `state/crrg-stage-c/ledger.md` and matter more than
the numbers:

1. **It measures reconstruction, not discovery.** Every agent read the forbidden
   lemma's proof and re-derived it. `crrg-forbid` stops a proof from *invoking* a
   declaration, not a reader from opening the file.
2. **C7 was not blind.** The candidate file's docstrings carried the design
   rationale, including "a deliberately FALSE target". Found by reading C7's own
   report, fixed before C2/C3/C4 — the three that carry the real mathematics — so
   those are clean. C7's cost figure is excluded.
3. **`MALFORMED` had expected count zero by construction**, so observing zero is
   not evidence.

### Stage D — frozen iter165 research backtest (`2dc5912f`)

| id | claimed | **observed** | builds | tooling | substitution considered |
|---|---|---|--:|--:|---|
| T1 | UNCHANGED | **UNCHANGED** | 1 | 0 | NO |
| T2 | REFUTED | **REFUTED** | 4 | 2 | NO |

Claim and observation agreed in both cases. There is no expected-outcome column
and there could not be — nobody knew whether either obligation was provable.

Isolation held throughout, verified before and after: base commit exactly
`f758c1b1`, no git remote, no post-cutoff commit in the object store, no ref
beyond the frozen branch, no network attempt, no mention of any later rung.

Both tooling failures were the same cause — Lean's `constructorNameAsVariable`
**style** linter aborting with max-recursion on the refutation. One linter
disabled for one file; no soundness option touched, no banned construct, axioms
independently confirmed kernel-3.

---

## 7. Trust surface

| gate | positive control | negative control |
|---|---|---|
| axiom audit | 481 declarations clean | `sorry`-backed refinement rejected; `DISALLOWED AXIOM: sorryAx` |
| banned constructs | clean file with the list quoted in a comment | `sorry`, `native_decide`, aggregate magnitude |
| `crrg-forbid` | genuine non-dependency passes | dependency through a theorem **proof**, with the path printed |
| seal | weakened target hashes differently; stable under a wider import set | retargeted declaration → `SEAL BROKEN` |
| type-link | leaf is the intended proposition | leaf is not `True`; adjacent leaves are distinct |
| refinement | rootward `Edge` and covering `Split` both accepted | easier child, unrelated child, reversed direction, non-covering split |
| root immutability | root is the exact endpoint | three neighbouring `ProtocolClaim`s rejected |
| isolation | build succeeds with network blocked | `git ls-remote` → `transport 'https' not allowed` |

Counts: CRRG **49** asserted rejections and **22** gate self-tests; Stage B **9**;
Stage D **18** asserted rejections and **27** gate self-tests.

**Every rejection test checks the reason, not the exit status.** That rule earned
its keep repeatedly — see §8.

---

## 8. Defects found by the programme's own controls

Listed because the pattern is the point: in four separate cases the code written
to prevent a failure mode exhibited that failure mode, and only a reason-checking
control caught it.

| defect | why it mattered |
|---|---|
| `crrg-seal` hashed `#check @decl`. A target's normative shape is `def T : Prop := …`, whose type is `Prop` — so the hash was **a function of the name alone**. | Renaming changed it; editing the proposition did not. Exactly inverted from §5.3's purpose. Found by the first test that required two targets to hash differently. |
| `crrg-forbid` read statements, never proofs: `ConstantInfo.value?` returns `none` for every `theorem` unless asked for opaque values. | It would have certified that a proof routed straight through the withheld lemma had not used it. |
| Stage C gate reported a missing import as `seal broken; the target moved under its own name`. | A tooling failure wearing a security finding's costume. Would have recorded a seal violation against the first agent to submit anything. |
| Stage D's `UNCHANGED`/`TOOLING_FAILURE` discriminator matched the word `toolchain` inside Lake's own `trace:` line. | Classified **every** build failure as a tooling failure — the exact misclassification it was written to prevent. |

Two more worth naming: `OPEN-01` was diagnosed as a Mathlib problem when the
linters are **core Lean** ones added between v4.30.0 and v4.32.2 — the true count
was 23, not 7, and the real defect was that CRRG's gate had only ever built under
one of the two toolchains its consumers use. And the gate could not run from a
fresh clone at all, because two scripts had lost their executable bit under a
git configuration that does not track file mode.

---

## 9. What this programme does **not** establish

- **Not that CRRG improves research.** Stage D is one experiment, two
  obligations, one session each.
- **Not that agents resist reward hacking.** Zero substitutions and zero
  weakenings were *observed*; no agent attempted one. That is a null result about
  agent behaviour, not a positive result about CRRG's defences. The defences were
  demonstrated against attempts the orchestrator constructed.
- **Not that promotion cost is known.** Stage C measured source-visible
  reconstruction. Nothing here measures discovery cost.
- **Not that a refinement is progress.** See Finding 4.
- **Not that network isolation is hard.** It is soft on this host: user
  namespaces are disabled, `unshare -rn` fails with `EPERM`, and no sandbox
  binary is installed. The *structural* layer — no remote, no post-cutoff object,
  no extra ref — is what actually guarantees the corpus boundary.

---

## 10. Review checklist (§12)

| # | item | where |
|---|---|---|
| 1 | exact CRRG and downstream SHAs | §0 |
| 2 | final Stage B graph, MCA/list/budget in root lineage | §6 |
| 3 | Stage C limitations and results | §6, `state/crrg-stage-c/ledger.md` |
| 4 | Stage D isolation and the 7487 root | §6, Finding 2 |
| 5 | attempted target substitutions and their handling | Finding 2 — none proposed; controls in `StageD/Controls.lean` |
| 6 | seal scope and registry behaviour | §7; `CRRG_SEAL_SCOPE` multi-namespace, gate-verified |
| 7 | downstream promotion wrapper | `CrrgGraph/scripts/crrg-promote`, in the consumer's Lake context |
| 8 | negative tests and axiom closure | §7, §8 |
| 9 | application mathematics kept out of CRRG core | core is Lean-core-only; `Test/Synthetic/Replay.lean` carries anonymous patterns only |
| 10 | agent DX | Stage C: promotion tooling not a bottleneck. Stage D: two tooling failures in two sessions, both one style linter |

---

## 11. The finding was fed back into the research lane

Owner-directed, after the review corrections. `yukon-lower-bound` @ **`22ba8969`**,
`iter 195: hold yukon_delta=307083/1048576 target=extension-list-refuted`.

**`crrg-stage-d-yukon` was not merged.** Only the theorem was ported, restated in
the lane's own vocabulary, so the experiment branch stays an experiment.

What landed:

- `YukonExtensionListRefuted.lean` in `ReferenceResults`, mirrored byte-identically
  into `LowerEnv/SubmissionLower` as the lane's gate requires. Nine theorems.
  `extensionList_false_of_small_budget` is stated **radius-generically**, so it
  covers 6586, 7487 and 9433 at once and shows the failure is not a matter of
  choosing `Bmca` better.
- The `YukonT1Composition` prose that called the hypothesis "an equally open list
  bound" is corrected in both copies, with the superseded text retained.
- A correction box at the head of `state/yukon-soundness/FRONTIER.md`.

What deliberately did **not** change: the metric is unmoved at
`ProtocolClaim 6399 307083 1048576`; the rungs are not refuted, only one
decomposition of them; and 182's result stands — `YukonMCACountAt` itself resists
this witness, because `IsMCA`'s failing-row clause is exactly what the
extension-list over-approximation drops.

`scripts/squeeze/yukon_verify.sh` passes, exit 0, 63.99 bits, axioms ⊆ kernel-3,
mirror diff clean.

**The lane's own audit caught a defect in my correction**, which is worth
recording because it is the same class of error the audit was built for. Its
header check requires a refuted claim to be flagged in prose, and my flag read
`**is\nDEAD**` — split by line wrapping, so the literal `is DEAD` was absent and
the check fired. Iteration 190 added that check precisely because iteration 188
"lost one to line wrapping and only noticed by hand". Fixed; the audit now
reports no problems.

---

## 12. Recommended posture

Matching the owner's standing verdict:

```text
CRRG core semantics             GREEN
Trust / sealing / gates         GREEN
Known-proof integration         GREEN
Blind-ish reconstruction        GREEN with caveats
Historical research backtest    GREEN

Ready for External Review 2     YES
Ready for Soundness shadow      pending External Review 2
Ready to schedule Soundness     NO
```

The single item a reviewer should press hardest is **Finding 4**. Everything else
in this packet is a property of the kernel or of a gate, and can be re-derived by
running it. Finding 4 is a property of an agent's judgement, was observed once,
and is precisely where the kernel offers no guarantee.
