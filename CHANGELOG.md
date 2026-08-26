# CRRG Changelog

Audit trail for the Certified Research Reduction Graph implementation.

This file is the **plan of record** for spec conformance. Section 1 is the
conformance matrix: every normative requirement in [`Spec.md`](Spec.md), its
implementation status, and the change that last touched it. Section 2 is the
chronological change log. Section 3 records deliberate deviations from the spec
and the reason for each. Section 4 records known work that is **not** done.

Conventions:

- **Spec references** use the section numbers as they appear in `Spec.md` after
  the `SPEC-01` heading repair. Where the pre-repair spec used a
  conflicting subsection number, both are given, as `§14 (12.x)`.
- **Status** is one of `DONE`, `PARTIAL`, `MISSING`, `DEFERRED` (out of scope
  for the current stage, with the gating stage named), or `DOWNSTREAM` (belongs
  to a consuming project's adapter, not to standalone CRRG).
- A requirement is only `DONE` when it is exercised by the test suite or a gate
  script, not merely when code exists.

---

## 0. Provenance

- `be47e28` Initial commit
- `a2ac02b` spec.md
- `8b521ed` Implement CRRG spec as standalone Lean 4 library — **the
  as-delivered implementation. It does not compile.** No `lake build` had been
  run against it. Six of eight core modules and all six test modules were
  rejected by the elaborator. Everything from `CHG-01` onward builds on this
  baseline.

The out-of-repo copy `../CERTIFIED_RESEARCH_REDUCTION_GRAPH_SPEC.md` is spec
**v0.1** and is deliberately left untouched as an independent validation
reference. It is *not* a mirror of `Spec.md` (v0.5, becoming v0.6): it predates
the standalone-repository architecture (§2), the typed candidate graph (§8), and
the staged implementation plan (§15). Do not reconcile the two.

---

## 1. Spec conformance matrix

### §2 Repository architecture

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 2.1 | CRRG imports no project-specific vocabulary | DONE | |
| 2.2 | Standalone repository layout | DONE | `SPEC-04` |
| 2.2 | Core is dependency-light (Lean core only) | DONE | `DEV-01` |
| 2.2 | Generic replay patterns in `Test/Synthetic/Replay.lean` | DONE | `CHG-23` — a Yukon fixture inside CRRG would violate §2.1 |
| 2.2 | Toolchain portability is checked, not asserted | DONE | `CHG-22` |
| 6.6 | Projection-reducibility usage rule | DONE | `SPEC-09` |
| 2.3 | Downstream adapter shape | DONE | `CHG-08` |
| 2.4 | Sibling-checkout development builds | DONE | `CHG-08` |
| 2.4 | Pinned-SHA integration builds | DEFERRED | needs a published CRRG SHA |

### §5 Trust model

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 5.1 | Frozen root | DOWNSTREAM | the root is a downstream declaration |
| 5.2 | Every edge is a Lean theorem | DONE | prose arrows are not representable |
| 5.3 | Every split proves coverage | DONE | `Split.discharge` |
| 5.4 | Guards produce sibling branches | DONE | `GuardedMap` |
| 5.5 | Exceptions are never deleted | DONE | `EscapeMap` |
| 5.6 | No synthetic global percentage | DONE | `CHG-16` — structural, `render_length` |

### §6 Lean API

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 6.1 | `Goal`, `Goal.Proved`, `Edge`, `Edge.id/trans` | DONE | |
| 6.1 | `Edge` universe explicit, not inferred | DONE | `CHG-12` |
| 6.2 | `Split` with coverage proof | DONE | |
| 6.3 | `BadNode`, `BadNode.Closed` | DONE | `DEV-01` |
| 6.3 | `WitnessMap`, `WitnessSplit`, `closed_parent` | DONE | `CHG-10` |
| 6.3 | Witness / branch / task types universe-polymorphic | DONE | `CHG-12` |
| 6.4 | `EscapeMap` | DONE | |
| 6.5 | `GuardedMap` consuming both truth values | DONE | |

### §7 Root package and live frontier

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 7.1–7.2 | Exact root goal and root seam | DOWNSTREAM | |
| 7.3 | `Frontier` package | DONE | |
| 7.4 | Replace one leaf by a child via `Edge`, siblings preserved | DONE | `CHG-09` |
| 7.4 | Replace one leaf by children via `Split`, siblings preserved | DONE | `CHG-09` |

### §8 Typed candidate graph and promotion queue

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 8.1 | No prose edges; every candidate has an exact Lean proposition | DONE | |
| 8.2 | Candidate edges expose all composition debt (Shape A / Shape B) | DONE | `CHG-17` — `CompositionDebt`, `shapeA_iff_shapeB` |
| 8.3 | Record carries `sourceIds`, `targetId`, `expectedTheoremName` | DONE | `CHG-14` — `SealRecord` |
| 8.4 | Lifecycle `DRAFT → SEALED_UNVERIFIED → CERTIFIED` | DONE | `CHG-14` — one type per state |
| 8.4 | Terminal states reachable and final | DONE | `CHG-14` — `status_not_promotable` |
| 8.5 | Sealed target immutable for the attempt | DONE | `CHG-14` — target is a type parameter |
| 8.6 | Promotion is not prize progress | DONE | no aggregate is emitted |
| 8.7 | Certified frontier rendered separately from the promotion queue | DONE | `CHG-16` — `QueueReport` |
| 8.8 | History: seal hash, commit, timestamp, status, reason | DONE | `CHG-08`, `CHG-14` |

### §9 LDB counterexample vocabulary

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 9 | `ListViolation` and LDB-specific vocabulary | DOWNSTREAM | `SPEC-03` — relocated in spec |

### §10 Quantitative partial progress

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 10.1 | Structural progress via certified splits | DONE | |
| 10.2 | Monotone parameterized families with an explicit monotonicity theorem | DONE | `CHG-15` |
| 10.2 | Numerical reward only for a strictly stronger parameter under identical node semantics | DONE | `CHG-15` — `Progress` |
| 10.3 | Certified root-bound evaluator | DEFERRED | spec says do not implement yet |

### §11 Agent task contract

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 11.1–11.6 | Task contract documented | DONE | `AGENTS.md` |
| 11 | Binary `OPEN → CLOSED` reward | DONE | `CHG-16` — `TaskStatus`, `FrontierReport` |
| 11 | Monotone-leaf reward variant | DONE | `CHG-15` — `Progress` |

### §12 Graph-change protocol

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 12.1 | Refinement requires a compiled coverage theorem | DONE | `CHG-09` |
| 12.2 | Invalid refinements rejected | DONE | 49 asserted rejections across the suite |
| 12.3 | Retirement removes from the live frontier | DONE | `CHG-09` |

### §14 Verification integration

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 14.2.1 | Build the live graph and every registered closed-task module | DONE | `crrg-check` |
| 14.2.2 | Reject banned constructs | DONE | `CHG-16` — `crrg-banned` |
| 14.2.3 | Transitive `collectAxioms` over the live graph | DONE | `CHG-07` |
| 14.2.4 | Type-link the root exactly | DONE | `Frontier.rootIs` |
| 14.2.5 | Type-link each task theorem exactly | DONE | `Frontier.leafIs` |
| 14.2.6 | Print only `OPEN` / `CLOSED` / `INVALID` per task | DONE | `CHG-16` |
| 14.2.7 | Print no aggregate count or percentage | DONE | `CHG-16` — `render_length` theorem |
| 14.3 | Lean is authority over rendered state | DONE | |

### §15 Stage A — synthetic unit tests

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| A.1 | Direct `Edge` composition | DONE | |
| A.2 | Exhaustive `Split` | DONE | |
| A.3 | Witness-level `WitnessSplit` | DONE | `CHG-10` |
| A.4 | Guarded refinement, failed guard explicit | DONE | |
| A.5 | Escape refinement, exception explicit | DONE | |
| A.6 | Route retirement without deleting lineage | DONE | `CHG-10` |
| A.7 | DAG reuse: one theorem discharges multiple parents | DONE | `CHG-10` |
| A.8 | Negative tests for missing branches and weakened children | DONE | `CHG-06` |

Stages B–G are out of scope for the current work and remain `DEFERRED`.

### §18 Acceptance criteria (v0.3)

| # | Criterion | Status |
|---|-----------|--------|
| 0 | Builds standalone, imports nothing project-specific | DONE |
| 0a | Downstream consumes CRRG as a dependency, no second copy | DONE |
| 0b | Sibling-checkout and pinned-SHA integration both build | PARTIAL — sibling verified, SHA pending |
| 1–4 | Exact root, closeRoot link, two landed leaves, `k0` metadata | DOWNSTREAM |
| 5 | A leaf refines into two children only with a compiled coverage theorem | DONE |
| 6 | A guarded refinement visibly retains the guard-failure branch | DONE |
| 7 | An escape refinement visibly retains the exceptional branch | DONE |
| 8 | The gate rejects a weakened child / missing branch in a negative test | DONE |
| 9–11 | Prize gate unchanged, no percentage, Disprove side unchanged | DOWNSTREAM |
| 12 | Every candidate has an exact compilable proposition | DONE |
| 13 | A sealed target cannot be weakened in place | DONE |
| 14 | Promotion requires the exact proposition plus the axiom/type-link gate | DONE |
| 15 | Yukon damaged-proof cost measured before directing live Soundness | DEFERRED — Stage C |
| 16 | An agent gets a correct binary reward from one exact leaf | DONE |

---

## 2. Change log

### Unreleased

Entries are added as `CHG-nn` (implementation) and `SPEC-nn` (specification) as
work lands.

#### `CHG-25` / `SPEC-14` — feat: `crrg-forbid`, and self-tests for the gate's own tools

**`crrg-forbid` — "prove this without using that."** Spec §11 item 4 requires an
agent's task contract to supply "only previously proved theorem constants". The
complement — which constants the agent may *not* route through — had no
mechanical enforcement at all, and Stage C cannot run without one.

The reason is specific rather than general. A damaged-proof experiment withholds
a lemma, but the withheld lemma **cannot be deleted from disk**: the downstream
Yukon gate byte-compares its vendored submission against a reference copy, so
removing the theorem would break the very gate the integration is required to
leave untouched (§2.7). The reference proof therefore stays present and
importable, and "the agent did not use it" has to be *checked*.

The audit walks the transitive constant closure of a submitted declaration and
reports the shortest path to each forbidden hit. It completes the trio:

| tool | catches |
|------|---------|
| `crrg-audit` | holes that reach the kernel — `sorry`, native decide |
| `crrg-banned` | escape hatches that do not reach the kernel — source-level |
| `crrg-forbid` | a *specific named* dependency — closure-level |

Three decisions worth recording:

- **It walks types as well as proof terms.** Restating a goal in terms of the
  forbidden definition is the obvious way around a value-only audit.
- **A prohibition naming a declaration that does not exist is an error, not a
  pass.** A misspelled prohibition forbids nothing and would otherwise report a
  clean audit — the most misleading outcome the tool could produce. A root that
  does not exist is rejected for the same reason.
- **No `partial`.** The walk is a fuelled loop bounded by the constant count.
  `crrg-banned` rejects `partial` in CRRG's sources, and the gate should not
  hold itself to a lower standard than it holds the library.

**The bug this nearly shipped with.** The first working version passed every
audit it was pointed at — including one where the forbidden lemma was used
directly. `ConstantInfo.value?` returns `none` for **every `theorem`** unless
asked for opaque values, so the audit was reading statements and never proofs.
It would have certified that a proof routed straight through the withheld lemma
had not used it: the single failure this tool must not have, in a tool whose
entire purpose is to be trusted. `value? (allowOpaque := true)` on the
non-exporting environment — which is what Lean's own `collectAxioms` does — is
the fix.

**`crrg-selftest`, added because of that bug.** A check that silently passes when
it should fail is worse than no check, because it is *reported* as evidence.
Every gate tool is now exercised on a case it must accept **and** a case it must
reject — eleven checks, step 7 of `crrg-check`.

And a rejection only counts if it happened *for the stated reason*. Exit status
alone is not enough: during development these very tests "passed" while every
invocation was actually dying on an unrelated stale-olean error. The `expect`
helper takes the substring the output must contain, and reports
`right status, WRONG REASON` when the status matches but the cause does not.

#### `CHG-24` / `SPEC-13` — feat: ship `#expect_failure` to downstream adapters

External Review 1, Priority 2 ("make failed tests real") and §2.3 ("the negative
tests are not yet genuinely adversarial"). The harness itself was already real —
`CHG-05` built it and `CHG-13` fixed a bug that made it silently pass on every
`theorem` — but it lived in `Test/Support/`, inside CRRG's own test suite, where
**no consumer could reach it**.

That matters more for CRRG than for an ordinary library. CRRG is an
anti-reward-hacking system: its most valuable tests are the ones asserting a
construction is *rejected*, and a downstream `ResearchGraph` adapter needs
exactly the same discipline for its own graph — that a weakened leaf, an
incomplete split or a dropped guard branch fails to compile. Shipping the
calculus without the means to test it adversarially ships half the design.

`CRRGTest` is now a third Lake library, holding `CRRGTest/ExpectFailure.lean`.
It is Lean-core-only like the core, and `import CRRG` does **not** pull it in, so
opting into the harness is explicit and the shipped semantics stay
unencumbered. CRRG's own test suite consumes it the same way a downstream
adapter will, which keeps the shipped path on the tested path.

`crrg-check`, `crrg-portability` and `crrg-status` build all three libraries.
The portability sweep now also replays `ExpectFailureSelfTest` under every
supported toolchain — worth noting because the `Elab.async := false` workaround
in `CHG-13` guards a *toolchain behaviour*, not a fixed one, and had only ever
been pinned against v4.30.0.

#### `CHG-23` / `SPEC-12` — feat: generic replay patterns; no Yukon fixture inside CRRG

`Spec.md` §2.2 reserved a `Test/YukonReplay/` directory inside CRRG for the
Stage B integration fixture. That directory is now struck from the layout: it
was a **boundary violation of §2.1**. Reconstructing the Yukon proof requires
importing the Yukon mathematics, and CRRG must never import a research project's
vocabulary. The matrix carried the row as `DEFERRED — Stage B`, which read as
"not built yet" when the correct status was "must not be built here". Stage B
correctly put the reconstruction downstream instead, so the spec was describing
a layout the implementation had already, rightly, declined to produce.

What *is* generic is the shape of the exercise. `Test/Synthetic/Replay.lean`
extracts the four patterns Stage B produced and states each against an anonymous
toy development — no constant, type or lemma corresponds to anything in a
research project:

| # | Pattern | What it catches |
|---|---------|-----------------|
| P1 | Coverage by the structure constructor | an invented or dropped obligation |
| P2 | Coverage by refactor, not by re-proof | a split needing an ingredient the real proof did not |
| P3 | The agreement set | the graph drifting away from the development |
| P4 | Sibling preservation under refinement | a refinement quietly discarding obligations |

Five asserted rejections, each verified to fail for the *intended* reason rather
than incidentally: the truncated split is rejected because the constructor still
demands the field it omitted; the two-ingredient coverage theorem because
`Nat.le_trans` has nowhere to hide the missing middle step; the drifted constant
because `decide` proves the equation **false**; and the `Frontier.compose`
example because the composed frontier does not mention the siblings at all —
which is §7.4's warning made concrete instead of left as prose.

**One honest correction to how P3 should be read.** An agreement check of the
form `(crrgClosure : P) = (landed : P) := rfl` does not compare proof *terms*:
`P` is a `Prop`, so proof irrelevance already equates any two of its
inhabitants. What the check establishes is that both sides inhabit the same
proposition — which is the property worth having, since a reconstruction that
closed a *different* endpoint is the failure mode — but it is weaker than "the
graph reproduces the proof". The file says so, so the pattern is copied with the
right expectation.

The file also demonstrates §6.6 item 2 in its natural habitat: its predicates
are plain `def`s, as a downstream adapter's would be, so `by decide` fails with
`failed to synthesize Decidable Premise` and each proof restates its goal with
`show` first. That error names the projection rather than the cause, which is
exactly the trap §6.6 exists to document.

#### `CHG-22` / `SPEC-11` — feat: the gate builds under every supported toolchain

`OPEN-01` was found by a downstream project rather than by CRRG's own gate. The
reason was not that the finding was subtle — it was that CRRG's gate had only
ever built under **one** toolchain, while CRRG is consumed by projects pinning
different ones. Nothing in the gate could have caught it.

`scripts/crrg-portability` builds the library and the full test suite under
every toolchain in `scripts/portability-toolchains.txt`, and **treats any
warning as a failure**. It is step 4 of `crrg-check`.

Warnings are failures rather than noise because a downstream consumer inherits
them and cannot tell CRRG's from its own. Steps 2 and 3 still build under the
primary toolchain first, so the common failure is reported before the slower
sweep.

**It paid for itself on first run.** The `defProp` audit in `CHG-20` covered the
core library, because the core was all that had ever been built under v4.32.2.
The portability check immediately surfaced **twelve more** in the *test suite* —
`Edge`- and `Progress`-valued fixtures in `Edge.lean`, `Refinement.lean`,
`Monotone.lean`, `ToyResearch.lean` and `NegativeTests.lean`. Those are now
`theorem`, along with their `#expect_failure` counterparts, so that a negative
test and the positive control it contrasts with are declared the same way. The
true `OPEN-01` count was therefore **23**, not 7.

A second result worth recording: the full suite, all **45** asserted rejections,
builds and passes under v4.32.2 as well. `#expect_failure` forces
`Elab.async := false` to observe errors inside `theorem` bodies (`CHG-13`), and
that behaviour was only ever pinned against v4.30.0. It holds on both.

The toolchain list is deliberately a file rather than a constant: the rule is
that every toolchain a live downstream consumer pins belongs in it, so the list
changes when a consumer moves, not when CRRG does.

The gate now runs in about eight seconds end to end, including two clean
cross-toolchain rebuilds.

#### `CHG-21` / `SPEC-10` — feat: `WitnessSplit` is indexed by its branch family

`OPEN-01` half two. The old shape carried the decomposition in fields:

```lean
structure WitnessSplit (parent : BadNode.{u}) where
  Branch : Type v
  child : Branch → BadNode.{w}
  classify : parent.Witness → Σ i, (child i).Witness
```

so `v` and `w` reached the structure's sort only inside a `max`, never on their
own — which is what `checkUnivs` reports. The new shape moves the branch family
into the indices:

```lean
structure WitnessSplit (parent : BadNode.{u}) {Branch : Type v}
    (child : Branch → BadNode.{w}) where
  classify : parent.Witness → Σ i, (child i).Witness
```

**This is not linter appeasement.** Spec §6.6 item 4 already says "where the
type is incidental rather than the point of the abstraction, make it a parameter
instead of a field", and cites `MonotoneFamily.Param` as the precedent. A
`WitnessSplit`'s index type is exactly that case: the classification is the
point. §6.6 simply never applied its own rule here. The linter and the spec
agree, and the change is recorded normatively as `SPEC-10`.

What it buys beyond the warning:

- **The type names the decomposition.** `WitnessSplit parent child` can be
  type-linked to the exact children it covers (§14.2 item 5). The old shape
  could only be linked to "some decomposition of this parent".
- **Consistency.** `Edge`, `WitnessMap`, `GuardedMap` and `EscapeMap` are all
  indexed by both endpoints; `WitnessSplit` was the lone exception.
- **§5.4 and §5.5 get stronger.** `GuardedMap.child pass fail` and
  `EscapeMap.child main escape` are now named families appearing in the *type*
  of `toWitnessSplit`. The guard-failure branch and the exceptional branch are
  part of a signature, so dropping one is a type error rather than a proof
  error.

**Alternatives considered.** Collapsing `v` and `w` into one universe also
silences the linter but is genuinely lossy — `GuardedMap`'s branch index is
`Bool : Type 0` while its pass and fail nodes sit at an arbitrary level, so
every guarded and escape split would have to be re-indexed by `ULift Bool`.
Promoting only `Branch` to a parameter and leaving `child` a field is likewise
clean and less invasive, but it gives up reason 1, which is the one that matters
for an anti-reward-hacking system.

`Split` is deliberately left alone: it is universe-clean as written, and §7.4
already records the accepted mitigation for the same projection hazard on
`Frontier.Task`.

Two negative tests were rewritten rather than merely repaired. The old
`partialClassifier` rejection would still have failed after this change, but for
the wrong reason — a mistyped signature rather than a missing case — so it now
states its incompleteness against the *same* child family as a positive
control. A new `misroutedClassifier` rejection covers a gap the suite never had:
that the `Sigma` really does tie each witness to the branch it names.

**Result: CRRG core and test suite are warning-free under both v4.30.0 and
v4.32.2.** `OPEN-01` is closed.

#### `CHG-20` — fix: `OPEN-01` half one — every `Prop`-valued `def` becomes a `theorem`

`OPEN-01` recorded that `linter.defProp` and `linter.checkUnivs` "ship with
Mathlib", so that "every downstream consumer sees them and CRRG never will".

**That diagnosis is wrong, and it mattered.** Both are **core Lean** linters,
introduced between v4.30.0 and v4.32.2. CRRG pins v4.30.0; the Yukon lane pins
v4.32.2. Building CRRG under v4.32.2 with no Mathlib anywhere in scope produces
every one of the warnings, and building it under v4.30.0 produces none. The gap
was never Mathlib — it was that CRRG's gate has only ever built under the older
of the two toolchains its own integration target uses. `CHG-21` closes that.

Two further consequences the original entry missed:

- **The count was 11, not 7.** `CRRG/Audit.lean` contributes four more:
  `Frontier.rootIs`, `Frontier.leafIs`, `SealedCandidate.targetIs` and
  `ResolvedCandidate.certifiedProof`. They return `True` or a bare `P`, so they
  are propositions just as much as the `Edge`-valued ones are.
- **Suppression is not portable.** `set_option linter.defProp false` and
  `set_option linter.checkUnivs false` are *hard errors* under v4.30.0
  (`Unknown option`), so "disable the linter" is not available to a library that
  must build under both.

All eleven are now `theorem`. The interaction `OPEN-01` flagged as worth
confirming — whether anything depends on their definitional unfolding — cannot
arise: every one of them is a proposition, so proof irrelevance already makes
any two inhabitants definitionally equal. The full suite builds unchanged, 30
jobs, including the `rfl`-shaped agreement checks in the downstream Stage B
reconstruction.

Also fixes the two `unusedVariables` warnings (`CRRG/Debt.lean` `chain_intro`,
`Test/Synthetic/Monotone.lean` `momentBound.monotone`), which are core-linter
findings present under both toolchains.

#### `CHG-19` — fix: the gate could not run from a fresh clone, on Linux

Three portability defects, all introduced by the Windows workstation used as an
intermediary during the Stage B session, and all invisible from that box.

**1. Two gate scripts were committed without the executable bit.**
`scripts/crrg-audit` and `scripts/crrg-banned` were recorded in the git index as
`100644`. `crrg-check` invokes both directly, so step 4 died with
`Permission denied` on any fresh clone. It passed on the machine that wrote them
only because the working-tree bit was set there while git's `core.filemode` was
off. `CHG-18`'s claim that the gate "passes from a clean tree" was therefore
false as committed.

Fixed with `git update-index --chmod=+x`, and `crrg-check` gains a **step 1**
that reads the *index* — not the filesystem — and fails if any `scripts/crrg-*`
entry is not `100755`. Checking the filesystem would have reproduced the
original blind spot exactly.

**2. `crrg-banned` invoked `python`.** Stock Linux ships `python3` and no
`python`; the name only resolves on Windows or inside a conda environment. The
script now probes for `python3`, then `python`, and honours `$PYTHON`.

**3. `stage-b-check` reached past `crrg-banned` into `banned_scan.py`** with the
same hard-coded `python`. It now calls `crrg-banned`, so the interpreter
decision lives in one place.

**Verified on Linux** (16 cores, 61 GiB): `scripts/crrg-check` passes all six
steps, and the step-1 guard was confirmed to fail when the bit is flipped back.

#### `CHG-18` — docs: close out the conformance matrix and refresh `README.md`

Updates section 1 to reflect the state at the end of this work, and renumbers its
row labels to the post-`SPEC-01` scheme (so a row now reads `§14.2.3`, not
`§12.2.3`).

Every requirement in CRRG's own scope is now `DONE`. What remains is:

| Item | Why it is not `DONE` |
|------|----------------------|
| §2.4 pinned-SHA integration | needs a published CRRG commit to pin against |
| §5.1, §7.1–7.2, §9 | `DOWNSTREAM` — the root and its vocabulary belong to the adapter |
| §10.3 root-bound evaluator | the spec says do not implement this yet |
| Acceptance 15 | Stage C |

`README.md` gains the new primitives, the five-step gate, the strengthened trust
model, and a statement that the core is Lean-core-only so consuming CRRG does not
constrain a downstream project's version resolution.

**Final state.** `scripts/crrg-check` passes from a clean tree: 481 declarations
audited with no banned axiom dependency, no banned constructs, 29 build targets,
and **44 asserted rejections** across the suite. The downstream integration
fixture builds against the library, and all four gates behave correctly against
it — honest promotion passes; a `sorry`-backed promotion is rejected by the
promotion check, by the namespace axiom audit, and by the banned-construct scan.

#### `CHG-17` / `SPEC-09` — feat: composition debt (§8.2), a toy end-to-end programme, and the projection-reducibility rule (§6.6)

**Composition debt (§8.2).** A syntactically exact proposition can still hide the
research gap by naming some premises and quietly relying on others — the spec's
own example is describing an edge as `H2 → FpMomentBudget` while depending on
`DimKerPsi4ResidualBound` and `LandedH2Count` too. `CRRG/Debt.lean` adds
`CompositionDebt`, whose target proposition is **computed** from its premise
list, so there is no second place to put a hypothesis. Shape A (`chain`) and
Shape B (a bundled obligation) are both provided, with
`shapeA_iff_shapeB` proving they are the same obligation — so the choice between
the spec's two permitted encodings is presentational, not semantic.

**Toy end-to-end programme.** Every other test exercises one primitive in
isolation. `Test/Synthetic/ToyResearch.lean` assembles them into the *shape* of a
real reduction programme: a rational-radius root with a frozen denominator, a
two-premise seam theorem mirroring
`achievable_971426_of_fpMomentBudget_genericTail`, exact root and leaf
type-links, a monotone family with a certified improvement, a guarded refinement
keeping the failure branch alive, an escape refinement keeping the exception
alive, a candidate carrying real composition debt sealed and promoted, a leaf
split by a certified coverage proof, a route retired by proof, and a frontier
report. Six asserted rejections cover the dishonest move at each stage.

It imports nothing from any research repository. **This is not Stage B.**

**ℚ without Mathlib.** The session began with a decision to add Mathlib as a
test-only dependency so fixtures could use `ℚ`. That premise was wrong in one
direction and right in another, and the resolution is worth recording:

- `Rat` **is** in Lean core, with working arithmetic — so no dependency is needed
  to state a rational-radius root;
- but core `Rat` division does **not** reduce in the kernel, so a rational
  *inequality* is not provable without Mathlib's order lemmas. `decide` and `rfl`
  both fail on `(1900 : Rat)/4096 ≤ 1`.

The toy therefore keeps ℚ in the *statement* layer and ℕ in the *proof* layer —
which is what the real adapter does anyway, since the live root names
`Achievable (971426/2097152 : ℚ)` while both landed leaves are ℕ-indexed. CRRG
never needs to prove a rational inequality. **No Mathlib dependency was added.**
Spec §2.2 already permits a test-only one (`SPEC-04`) should a future fixture
need `Finset`/`Fintype`; adding it later is easy, whereas removing it once
downstream pins exist is not.

**Projection reducibility (§6.6).** New normative usage section. Instance search,
`decide` and `omega` run at reducible transparency and will not unfold a plain
`def`, so projections like `myNode.Witness` or `myFamily.Stronger` become opaque
atoms and automation fails with errors naming the projection rather than the
cause. This bit the implementation **four separate times** (`BadNode` fixtures in
the guard and escape tests, `MonotoneFamily`, and the toy programme's
predicates), so it is now documented with its four remedies rather than
rediscovered: declare fixtures `abbrev`; restate goals with `show` when a plain
`def` is wanted; annotate binders at their concrete type; and make a type a
parameter rather than a field where it is incidental to the abstraction.

#### `CHG-16` / `SPEC-08` — feat: banned-construct scan and no-aggregate reporting (§14.2 items 2, 6, 7; §5.6; §8.7)

Three normative gate requirements had no implementation.

**§14.2 item 2 — reject banned constructs.** `scripts/crrg-banned` scans Lean
sources for escape hatches the axiom audit cannot see, because they keep a
declaration axiom-clean while defeating the trust model: `sorry`,
`native_decide`, `axiom`, `unsafe`, `partial`, `@[implemented_by]`, `@[extern]`.

The first version used `grep` and immediately produced four false positives on
`Report.lean`'s own doc-comments quoting the spec. Rewritten as
`scripts/banned_scan.py`, which strips Lean comments (handling nested `/- -/`)
before matching, so documentation may name a banned construct without tripping
the scan. Verified against a fixture containing all seven classes — every one is
caught — and against a fixture mentioning them only in comments, which passes.

**§14.2 items 6 and 7, §5.6 — reporting without an aggregate.** `CRRG/Report.lean`
adds `TaskStatus` (exactly three constructors, rendering to `OPEN` / `CLOSED` /
`INVALID`) and `FrontierReport`, whose `render` emits one line per task and
nothing else. The guarantee is a theorem:

```lean
theorem render_length (r : FrontierReport root) : r.render.length = r.tasks.length
```

A summary line, count, or percentage would make the output longer than the task
list, so surfacing one requires breaking this theorem — and the test suite
asserts it. `FrontierReport` also has no aggregate field to hold such a value,
which is itself an asserted rejection.

`taskCount` remains available for an orchestrator to iterate over, but is not
part of `render`: §7.3 says task count has no reward meaning.

**§8.7 — queue rendered separately.** `QueueReport` is an unrelated type to
`FrontierReport`, and a `PromotionQueue` is not a `Frontier`, so a queue entry
cannot contribute to root closure. Both facts are asserted rejections.

Gate is now five steps; `crrg-check` runs the scan as step 5/5.

#### `CHG-15` / `SPEC-07` — feat: monotone parameterized families (§10.2)

§10.2 permits a *local numerical* reward for node families with a canonical
parameter order, under two conditions: an explicit monotonicity theorem, and
progress measured only against a strictly stronger parameter under identical node
semantics. It also forbids comparing unrelated local currencies by a hand-chosen
exchange rate.

None of this had any representation. There was no way to declare a family, no
way to state a monotonicity theorem, and consequently no way for the orchestrator
to distinguish a real improvement from a restatement.

Adds `CRRG/Monotone.lean`:

- `MonotoneFamily Param` — `Stronger` (a preorder), `claim`, and **`monotone` as
  a field**, so a family cannot be declared without proving the monotonicity
  theorem;
- `StrictlyStronger` — irreflexive, transitive, asymmetric, so re-proving the
  same parameter earns nothing;
- `Progress F old new` — the only numerical reward CRRG recognises, requiring
  simultaneously the same family, a strict improvement, and a proof at the new
  parameter;
- `Progress.implies_old` — a theorem that progress never loses ground: a proof at
  a strictly stronger parameter still proves the old claim, so an agent cannot be
  rewarded for an "improvement" that abandons what was established;
- `MonotoneFamily.edge` — monotonicity viewed as a rootward CRRG edge.

**The prohibition on exchange rates is the absence of an operation.** `Progress`
is indexed by its family, and nothing combines progress across families. Two of
the eight tests assert exactly this: progress in a `momentBound` family is
rejected as progress in a `listBound` family even though both are over `ℕ` and
both improve 3 → 5, and `Progress.trans` refuses to chain across families.

**`Param` is a parameter, not a field.** A `Type`-valued field would be projected
as `F.Param` at every use site, and projections of a plain `def` do not reduce
during instance search — numerals and `omega` fail against `F.Param` even when
the family is over `ℕ`. This was hit directly while writing the tests. Where a
type field is the point of the abstraction (a `BadNode` *is* its witness type)
the cost is unavoidable; here it is incidental, so it belongs in the signature.
Spec §10.2 records the corresponding declaration idiom (`abbrev`, not `def`).

#### `CHG-14` / `SPEC-06` — feat: Lean-enforced candidate lifecycle

Rewrites the candidate layer so that illegal transitions are untypeable rather
than merely discouraged. The audit had found three concrete holes:

1. `sealedUnverified` was **unreachable** — nothing in the API constructed a
   candidate with that status, so `isPromotable` was dead code and the
   lifecycle's central state did not exist;
2. `SealedCandidate` carried no status, so `markRefuted` produced a value that
   `promote` still accepted — a refuted candidate could be certified;
3. the record was missing §8.3's `sourceIds`, `targetId` and
   `expectedTheoremName`, and all of §8.8's history fields.

The new encoding indexes the type by the sealed proposition and gives each
lifecycle state its own type:

- `SealRecord` — §8.3 identity plus §8.8 history (`sealHash`, `sourceCommit`,
  `createdAt`);
- `DraftCandidate` — target is a field, because a draft may still change;
- `SealedCandidate P` — **target is a type parameter**, so §8.5 is structural:
  weakening it is not a mutation but a type error;
- `Outcome P` — the terminal states, with `certified` carrying a proof of `P`
  and `refuted` carrying a disproof;
- `ResolvedCandidate P` — seal plus outcome, retained forever (§8.8);
- `PromotionQueue` — deliberately unrelated to `Frontier`, so a queue entry
  cannot close a root (§8.7).

`CandidateStatus` survives for rendering only; it is derived via `Outcome.status`
and nothing accepts it as evidence. Three properties are now theorems rather
than conventions: `status_isTerminal`, `status_not_promotable`, and
`certified_sound` (a certified resolution really does yield a proof of the exact
sealed proposition).

**A claimed refutation must carry a disproof.** `refute` requires `¬ P`;
"contradicted but not disproved" is `markInvalid`, which makes no claim about `P`.
Conflating them would let an agent close a task by asserting falsity.

Test coverage rewritten accordingly, with six new asserted rejections: proxy
promotion, re-typing a sealed target, refuting without a disproof, promoting a
resolved candidate, extracting a proof from a refuted one, and using a promotion
queue entry to close a root.

#### `CHG-13` — fix: `#expect_failure` silently passed on every `theorem`

Found while writing the candidate lifecycle tests. A negative test written as a
`theorem` passed **unconditionally**, whatever its proof.

Cause: Lean 4.30 elaborates `theorem` bodies asynchronously. `elabCommand`
returns before the proof is checked, so the harness observed an empty message
log and concluded the command had been accepted — reporting a false pass for
exactly the case a negative test most needs to catch. `def` and `example` are
elaborated synchronously and were unaffected, which is why the gap survived the
harness's original two-direction verification.

Fixed by elaborating the wrapped command with `Elab.async := false`.

Added `Test/Synthetic/ExpectFailureSelfTest.lean`, which pins the behaviour in
both directions for `theorem`, `private theorem`, `example` and `def`, using the
fact that `#expect_failure` nests (`#expect_failure #expect_failure <valid>`
asserts that the harness rejects a valid command). It also re-checks that a
rejected declaration does not survive in the environment.

**No previously written negative test was affected** — all thirteen were `def`
or `example` — but any future one written as a `theorem` would have been silently
vacuous.

#### `CHG-12` / `SPEC-05` — feat: universe-polymorphic index and witness types; pin `Edge : Prop`

**Universes.** `BadNode.Witness`, `Split.Branch`, `WitnessSplit.Branch` and
`Frontier.Task` were all `Type 0`. A research counterexample is not guaranteed
to live in the lowest universe — any witness that itself carries a type (a
family, a code, a category-like structure) is at least `Type 1` — so a
monomorphic calculus simply could not host it. All four are now `Type u`.

Sibling nodes of one refinement share a universe (`GuardedMap`'s pass/fail,
`EscapeMap`'s main/escape); a `WitnessMap` may cross universes, and
`Frontier.splitLeaf` lands in `max u v`.

`Test/Synthetic/Universe.lean` proves the polymorphism is real rather than
vacuous: a `BadNode` whose witness is `(α : Type) × (α → α)`, a cross-universe
`WitnessMap` from `Type 1` down to `Type 0`, a `Type 1`-indexed `Split` and
`Frontier`, and a guarded refinement at `Type 1`.

**The two `trivial` constructors are deliberately pinned to `Type 0`.** Making
them polymorphic was tried first and is a usability trap: a convenience
constructor whose universe nothing pins forces every downstream definition built
from it to become polymorphic, and the level is then unsolvable at the use site
(`Failed to infer universe levels in binder type`). Anyone needing a trivial node
at a higher universe writes the two-line structure instance directly.

Verified that ordinary `Type 0` usage needs no annotations anywhere: all 21
pre-existing test jobs and the downstream integration fixture build unchanged.

**`Edge : Prop`.** Lean inferred this from the single proof-valued field, but the
inference was fragile — adding any data field later would silently move `Edge`
into `Type` and change the universe of every downstream signature mentioning it.
Now pinned explicitly, so that mistake becomes an immediate error. Certified
edges carry no data by design; metadata belongs on the candidate record (§8.3).

Spec §6.1–§6.3 and §7.3 amended to match, with a new normative
"Universe discipline" paragraph.

#### `SPEC-04` — spec: describe the built repository layout and make refinement normative

**§2.2 layout.** Updated to the actual tree: `Edge` lives in `Basic.lean` beside
`Goal` (an edge is meaningless without a goal, and §13's pilot layout groups them
the same way), `Test/Support/` and the new synthetic modules are listed, and
`crrg-audit` / `axiom_audit_body.lean.in` / `CHANGELOG.md` are added. Also states
explicitly that the **core** library is Lean-core-only while the **test** library
may depend on Mathlib, since nothing downstream links against tests and a
test-only dependency does not constrain a consumer's version resolution. This is
what permits the toy fixtures to use `ℚ`.

**§7.4 refinement.** Was "provide generic frontier refinement later, after the
pilot ... for v0.2 this can be manual". It is now implemented (`CHG-09`), so the
section is normative and carries the three signatures. Adds two things the
original omitted:

- an explicit warning **not** to use `Frontier.compose` for leaf refinement — it
  re-roots the whole frontier and silently discards every sibling leaf, which is
  precisely the mistake the section exists to prevent;
- the rationale for decidability being an explicit argument rather than an
  instance, since the instance-implicit form provably fails on the usage pattern
  §7.3 prescribes for downstream adapters.

#### `SPEC-03` — spec: mark §9 as downstream-only, resolving a direct contradiction with §2.1

§2.1 states that CRRG **must never import** `Achievable`, Reed–Solomon-specific
mathematics, or "any project-specific theorem vocabulary", and that if the
generic package appears to need one of these, "the abstraction boundary is wrong
and the concept belongs in a downstream adapter."

§9 then specifies `ListViolation` in terms of `Word`, `KBField`, `targetCode`,
`listAt`, `radius`, `Achievable`, `securityBits` and `Fintype` — every one of
them forbidden — without saying which package it belongs to. Read literally, the
spec required an implementer to violate its own hardest boundary rule, and it
additionally requires Mathlib (`Finset`, `Fintype`) in a package §2.2 wants
dependency-light.

Retitled to "**downstream adapter only**" and prefixed with an explicit boundary
warning stating that none of the section may be implemented inside the
standalone CRRG package, that the generic machinery it builds on (`BadNode`,
`WitnessSplit`, `EscapeMap`, `GuardedMap`) *is* CRRG's, and that finding
`ListViolation` inside the CRRG package is a boundary violation to be moved out
rather than blessed.

No implementation change: CRRG correctly contains none of this today. The spec
was the thing that was wrong.

#### `SPEC-02` — spec: normalise the version and amend `BadNode.Closed` to be Mathlib-free

**Version.** The document declared `v0.5` in its header while §18 was titled
"Acceptance criteria for **v0.3**" and the body deferred items to "v0.2" and
"v0.3". Three different version numbers were in play for one document, and the
milestone references had no fixed meaning. Normalised to **v0.6** — the first
revision reconciled against an implementation that actually builds — and
rewrote the stale milestone deferrals as unconditional statements
("until the decomposition naturally provides valid fallback bounds" rather than
"in v0.2").

**`BadNode.Closed`.** Amended §6.3 from `IsEmpty N.Witness` to
`N.Witness → False`, with the rationale inline. See `DEV-01`; this is the spec
side of `CHG-02`.

#### `SPEC-01` — spec: repair subsection numbering and duplicate section numbers

Purely structural; no normative content changed. `Spec.md` had accumulated
numbering damage from inserting sections without renumbering their children, so
a citation like "§12.2" was ambiguous between two different sections — a real
hazard for a document that automated agents are meant to cite.

Every `###` subsection now matches its parent `##` section:

| Section | Subsections were | now |
|---------|------------------|-----|
| §3 Source-derived design constraints | 2.1–2.2 | 3.1–3.2 |
| §5 Trust model | 4.1–4.6 | 5.1–5.6 |
| §6 Lean API | 5.1–5.5 | 6.1–6.5 |
| §7 Root package and live frontier | 6.1–6.4 | 7.1–7.4 |
| §8 Typed candidate graph | 7.1–7.8 | 8.1–8.8 |
| §10 Quantitative partial progress | 8.1–8.3 | 10.1–10.3 |
| §12 Graph-change protocol | 10.1–10.3 | 12.1–12.3 |
| §14 Verification integration | 12.1–12.3 | 14.1–14.3 |

Two sections were both numbered `## 18` ("Acceptance criteria" and "Design
summary"). "Design summary" becomes §19 and "Source map" becomes §20.

Result: sections run 1–20 with no duplicates, and every subsection number
matches its parent.

**Also noted, not yet fixed:** the document header declares `v0.5`, while §18 is
titled "Acceptance criteria for v0.3" and the body defers items to "v0.2" and
"v0.3". Version normalisation is handled in `SPEC-02` together with the
semantic amendments.

#### `CHG-11` — docs: bring `README.md`, `AGENTS.md` and `crrg-status` in line

`README.md` documented `crrg-check` as performing an "axiom audit" that did not
exist until `CHG-07`, and `AGENTS.md` promised agents an axiom audit as part of
the success condition. Both are now accurate. Adds the new refinement API to the
primitives table, documents the downstream-targeting environment variables, and
notes that a bare `lake build` builds only the `CRRG` library — CI must call
`scripts/crrg-check` or `lake build Test` explicitly, or the tests never run.

`crrg-status` now lists the new test modules, reports the axiom-audit result,
counts asserted rejections, and no longer leaks `lake` build output into its
summary.

Also reconciles the `CHG-nn` references in the section 1 matrix with the numbers
actually used in section 2.

**Phase 1 complete.** The as-delivered baseline is now a repository that builds,
tests itself, and enforces the trust model it claims. `scripts/crrg-check`
passes from a clean tree.

#### `CHG-10` — test: cover the three unimplemented Stage A items

Spec §15 Stage A lists eight primitives to validate in isolation. Three had no
test at all:

- **A.3 witness-level `WitnessSplit`** — and more seriously, `WitnessMap` was
  *entirely untested*: neither `id`, `trans`, `closed_parent` nor `toEdge` was
  exercised anywhere in the suite.
- **A.7 DAG reuse** — one theorem discharging multiple parents, which is the
  structural claim that makes the graph a DAG rather than a tree.
- **A.6 route retirement without deleting historical lineage.**

Adds `Test/Synthetic/Witness.lean` (A.3, A.7): witness maps as rootward edges,
`trans` composition, identity, one `sharedClosed` theorem discharging two
distinct parents both at witness level and via `toEdge`, and an exhaustive
sign-classifier `WitnessSplit`.

Adds `Test/Synthetic/Refinement.lean` (A.6, plus acceptance criteria 5): an
`Edge` refinement that demonstrably leaves the sibling leaf untouched, a
two-child `splitLeaf`, retirement leaving the historical edge still
type-checking, and two further asserted rejections — a split without a coverage
proof, and retirement of an unproved leaf.

The refinement fixtures use ordinary `def` rather than `abbrev` deliberately, to
exercise the explicit-decidability API from `CHG-09` under the same conditions a
downstream adapter will.

Stage A is complete at this commit: 8 of 8 items covered, 13 asserted
rejections in total.

#### `CHG-09` — feat: leaf-preserving frontier refinement and retirement

`Frontier.compose` carried this doc-comment:

> if the root of `inner` matches a leaf of `outer`, the combined frontier
> replaces that leaf with `inner`'s leaves.

It does not. Its result's task set is exactly `inner.Task`; every other leaf of
the outer frontier is discarded. The operation is *sound* — it still demands an
`Edge root mid` and `inner.closeRoot` — but it is whole-root re-rooting, not
leaf-wise refinement, so §7 (6.4)'s "preserve all other leaves" had no
implementation and acceptance criterion 5 could not be demonstrated.

Corrected the doc-comment and added three sibling-preserving operations:

- `Frontier.refineLeaf` — replace one leaf by a sufficient child via an `Edge`
  (§7 6.4);
- `Frontier.splitLeaf` — replace one leaf by a `Split`'s branches; the new task
  set is `{t // t ≠ t₀} ⊕ s.Branch`, so siblings survive and the split's
  coverage proof is structurally required (§7 6.4, §12 10.1);
- `Frontier.retireLeaf` — drop a leaf from the live frontier, requiring an
  actual proof of it. Retirement is therefore never a bookkeeping deletion
  (§12 10.3).

**Design note.** These take `DecidableEq F.Task` as an *explicit* argument
rather than an instance. Instance search runs at `instances` transparency and
will not unfold a frontier declared with a plain `def`, which is exactly how
downstream adapters will declare theirs (`def current971426 : Frontier ...`).
The instance-implicit version failed with `failed to synthesize DecidableEq
base.Task` on precisely the intended usage; the explicit argument unifies at
default transparency and works. Callers pass
`inferInstanceAs (DecidableEq MyTask)`.

#### `CHG-08` — feat: let the gate scripts target downstream projects; add axiom check to promotion

Two defects.

**1. The scripts could not reach the code they exist to check.**
`crrg-seal`, `crrg-lineage` and `crrg-promote-check` hardcoded `import CRRG` and
`cd "$CRRG_ROOT"`, while their own usage text advertised downstream targets:

```text
Example: crrg-promote-check MyProject.E17 MyProject.Candidates.E17Target
```

Since CRRG "must never import" project vocabulary (§2.1), a downstream
declaration is by construction not in scope after `import CRRG`, so the one job
these scripts exist for was impossible. Added `CRRG_IMPORTS`, `CRRG_WORKDIR` and
`CRRG_AUDIT_NAMESPACES` so each script can run inside a downstream Lake project
against its own modules.

**2. `crrg-promote-check` had no axiom step.** It verified only that the
theorem inhabits the target type, so a `sorry`-backed proof passed (see
`CHG-07`). Added step 4/4: `#print axioms` on the promoting theorem, failing on
`sorryAx` / `ofReduceBool` / `ofReduceNat` with an explicit
`It must NOT be promoted to CERTIFIED.`

`crrg-seal` additionally now prints a **seal hash** (sha256 of the exact printed
type), which §8 (7.8) requires candidate history to record.

Verified end to end against a throwaway downstream Lake project consuming CRRG:
honest theorem → `PASSED`, `sorry`-backed theorem → `FAILED`, and the namespace
audit catches the hole.

#### `CHG-07` — feat: transitive axiom audit — **the gate previously certified `sorry`**

The most serious defect found in the audit. Spec §14 item 12.2.3 requires
transitive `collectAxioms` over the live graph; `AGENTS.md` states the success
condition as "kernel compilation + axiom audit + exact type-link"; `README.md`
described `crrg-check` as "build + test + axiom audit".

**No axiom audit existed.** `lake build` only *warns* on `sorry`, and neither
gate script inspected axioms. This was demonstrated by planting
`theorem demoPromotion : DemoTarget := sorry` in the library:

```text
crrg-check           -> PASSED
crrg-promote-check   -> PASSED
                        "Proceed with candidate promotion to CERTIFIED status."
```

An agent could therefore have earned a promotion reward for a hole, which
defeats the premise of the entire system.

Adds `scripts/crrg-audit` plus the elaborator body
`scripts/axiom_audit_body.lean.in`. It enumerates every non-internal declaration
in the audited namespaces and runs `Lean.collectAxioms` on each:

- **banned:** `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat` — audit fails;
- **allowed:** `propext`, `Classical.choice`, `Quot.sound` — classical logic is
  fine, holes and native `decide` are not;
- anything else is reported as a warning rather than silently accepted.

Wired in as `crrg-check` step 4/4. Verified to fail on the planted `sorry` and
to pass on the clean tree: 229 CRRG declarations, zero banned dependencies.

#### `CHG-06` — test: replace the negative-test commentary with 11 asserted rejections

`Test/Synthetic/NegativeTests.lean` previously contained **no negative tests**.
It held positive tests plus comments asserting that bad constructions "would
fail type-checking" — for example:

```text
-- The above compiles. A version with only onPass and no onFail
-- would fail type-checking (cannot construct GuardedMap without onFail).
```

Nothing checked that claim. If CRRG had ever become lax enough to accept one of
these, the suite would still have been green.

Rewritten using `#expect_failure` (`CHG-05`) so each bad construction is an
asserted rejection. Covers:

| # | Rejected construction | Spec |
|---|----------------------|------|
| 1 | `Split` missing the odd branch | §5 4.3 |
| 2 | `Split.discharge` supplied only some branches | §5 4.3 |
| 3 | Weakened child discharging a stronger parent | §18 crit. 8 |
| 4 | `Edge` used in the leafward direction | §6 5.1 |
| 5 | `GuardedMap` without `onFail` | §5 4.4 |
| 6 | `GuardedMap.onPass` applied outside the guard | §5 4.4 |
| 7 | Escape branch dropped when closing the parent | §5 4.5 |
| 8 | `WitnessSplit` classifier not total | §6 5.3 |
| 9 | `Frontier` claiming a stronger root than its leaves support | §7 6.3 |
| 10 | Promotion by a proof of a different proposition | §8 7.5 |
| 11 | Sealing a candidate that is not in `DRAFT` | §8 7.4 |

Each was then unwrapped and elaborated raw to confirm it fails for a genuine,
on-point type error rather than vacuously — a syntax error would also satisfy
`#expect_failure`. All eleven produce the expected error (missing cases, field
missing, type mismatch on the exact proposition, and so on).

Also corrects a stale comment in `Test/Synthetic/Split.lean` that referred to
`Split.ofSplit`; the declaration is `Frontier.ofSplit`.

#### `CHG-05` — test: add the `#expect_failure` negative-test harness

Spec acceptance criterion 8 requires the gate to **reject** a deliberately
weakened child statement or a missing branch. Lean has no built-in way to assert
that a command fails without matching its exact error text, which is brittle
across toolchain versions.

`Test/Support/ExpectFailure.lean` adds a `#expect_failure <command>` elaborator
that succeeds exactly when the wrapped command is rejected, and raises
`"the command was ACCEPTED but should have been rejected"` when it is not. It
restores the environment and message log afterwards, so a rejected declaration
leaves no trace.

Verified in both directions before use: it passes on an ill-typed command, fails
on a well-typed one, and a rejected `def` is genuinely absent from the
environment afterwards (not silently added as `sorry`).

This introduces `import Lean` into the **test** library only. The `CRRG` core
library remains Lean-core-only.

#### `CHG-04` — fix: make `BadNode` test fixtures reducible — **build is green from here**

`Test/Synthetic/{Guarded,Escape}.lean` declared their fixtures as
`private def parentNode : BadNode := ⟨Nat⟩`. A plain `def` is semi-reducible, so
`parentNode.Witness` never reduced to `Nat`, and:

- instance search could not find `LT`/`LE`/`OfNat` for the witness type, so
  `decide (n < 10)` and `z ≥ 0` failed to elaborate;
- `omega` refused the `Escape` obligation, because a hypothesis whose subject
  has type `parentNode.Witness` rather than syntactically `Int` is not
  recognised as an integer-linear atom.

Changed the fixtures to `private abbrev`, and annotated the `EscapeMap.classify`
binder as `fun (z : Int) => ...` so `omega` sees a concrete `Int`.

This is the last of the four build-breaking defects. `lake build CRRG` and
`lake build Test` both succeed from this commit onward.

**Note on the general problem.** This is not only a test artefact: any
`Frontier`/`BadNode` declared with a plain `def` will resist instance search on
its projected type fields. `CHG-09` avoids inflicting this on downstream users
by taking decidability as an explicit argument rather than an instance.

#### `CHG-03` — fix: `trivial` resolved to `CRRG.Frontier.trivial` in the type-link helpers

All three type-link helpers in `CRRG/Audit.lean` were defined as
`... : True := trivial`. When Lean elaborates a declaration named
`Frontier.rootIs`, it opens the `Frontier` namespace for the body — so `trivial`
bound to `CRRG.Frontier.trivial : (root : Goal) → Frontier root`, not to
`_root_.trivial : True`. Lean reported a type mismatch rather than an ambiguity,
so the failure was not obvious from the source.

This broke `Frontier.rootIs`, `Frontier.leafIs`, and
`SealedCandidate.targetIs` — i.e. every mechanism the spec provides for
type-linking a graph node to an exact project proposition (§14 items 12.2.4 and
12.2.5). Replaced with the unambiguous `True.intro`.

Third of four commits required to make the baseline build; still red.

#### `CHG-02` — fix: make `BadNode.Closed` Mathlib-free; add missing `Split` import

Two independent defects in `CRRG/Witness.lean`:

1. `BadNode.Closed` was defined as `IsEmpty N.Witness`, and the proofs used the
   `IsEmpty` API (`.false`, anonymous-constructor introduction). `IsEmpty` lives
   in Mathlib, which this package deliberately does not depend on (§2.2: "prefer
   Lean core types and logic where sufficient; avoid creating an unnecessary
   independent Mathlib-version constraint"). The declaration did not elaborate.
   Replaced by the Lean-core-only `N.Witness → False`, which is definitionally
   the same proposition. See `DEV-01`.
2. `WitnessSplit.toSplit` returns a `Split`, but the module imported only
   `CRRG.Basic`. Added `import CRRG.Split`.

Second of four commits required to make the baseline build; still red.

#### `CHG-01` — fix: move `import` above module doc-comments

Lean 4 requires every `import` to precede all other content, module
doc-comments included. Twelve files placed `/-! ... -/` first, so the
elaborator rejected each with `invalid 'import' command, it must be used in the
beginning of the file`: six of eight core modules (`Split`, `Witness`,
`Guarded`, `Escape`, `Frontier`, `Audit`) and all six test modules. Only
`Basic` and `Candidate`, which have no imports, compiled.

This is the first of four commits needed to make the baseline build; the build
is still red after this one (see `CHG-02`..`CHG-04`).

Also gitignores the generated `lake-manifest.json` (CRRG has no dependencies to
pin).

---

## 3. Deliberate deviations from spec

Recorded here so a reviewer can distinguish an intentional amendment from an
implementation error. Each has a corresponding `Spec.md` edit.

#### `DEV-01` — `BadNode.Closed` uses `Witness → False`, not `IsEmpty`

**Spec §6 (5.3)** writes `abbrev BadNode.Closed (N : BadNode) : Prop := IsEmpty N.Witness`.

`IsEmpty` is a Mathlib class. Spec §2.2 requires the CRRG core to be
dependency-light and to avoid an independent Mathlib-version constraint. The two
requirements are in direct conflict, and §2.2 is the load-bearing one: a Mathlib
pin in the core would propagate to every downstream consumer.

`Closed` is therefore `N.Witness → False`. This is the same proposition
(`IsEmpty α` is a one-field structure wrapping exactly this arrow), so every
theorem in the spec still holds verbatim; only the introduction and elimination
syntax differs. CRRG never needs `Closed` to be found by instance search — it is
always passed explicitly as a hypothesis — so nothing is lost by dropping the
class.

`Spec.md` amended accordingly (`SPEC-02`).

---

## 4. Open items

Known work that is **not** done. Distinct from section 3, which records
deviations that were decided deliberately and are closed.

*(Nothing is currently open. `OPEN-01` is recorded below as closed, with its
original diagnosis corrected, because the wrong diagnosis is the instructive
part.)*

### `OPEN-01` — CRRG trips two linters — **CLOSED by `CHG-20` / `CHG-21`**

**The original entry's diagnosis was wrong.** It is retained verbatim below,
because how it was wrong is worth keeping.

It recorded both linters as shipping **with Mathlib**, and concluded that they
"fire only once a downstream project pulls CRRG in alongside Mathlib, which
means every downstream consumer sees them and CRRG never will". That asymmetry
was the stated reason for recording the item here rather than fixing it.

In fact both are **core Lean** linters, introduced between v4.30.0 and v4.32.2.
Building CRRG under v4.32.2 with no Mathlib anywhere in scope reproduces every
warning; building it under v4.30.0 reproduces none. Mathlib was never involved.
The finding surfaced during a Mathlib-using downstream build only because that
build is the one that happened to use the newer toolchain.

Three things follow, and the first two were missed entirely:

- **The `defProp` count was 11, not 7.** `CRRG/Audit.lean` contributes
  `Frontier.rootIs`, `Frontier.leafIs`, `SealedCandidate.targetIs` and
  `ResolvedCandidate.certifiedProof`.
- **"Disable the linter" was never available.** `set_option linter.defProp
  false` and `set_option linter.checkUnivs false` are hard `Unknown option`
  errors under v4.30.0, so a library that must build under both toolchains
  cannot suppress either.
- **The real defect was in the gate, not the source.** CRRG's own check had only
  ever built under the older of the two toolchains its integration target uses,
  so an entire class of finding was invisible to it. `CHG-22` closes that gap;
  without it, the next such divergence would again be found by a downstream
  consumer rather than by CRRG.

The `defProp` findings were mechanical (`CHG-20`). The `checkUnivs` finding was
not: it was a genuine over-parameterisation that §6.6 item 4 already prescribed
a fix for, and clearing it strengthened the type-linking of every witness split
(`CHG-21` / `SPEC-10`).

<details>
<summary>Original entry, as written</summary>

#### `OPEN-01` — CRRG trips two Mathlib linters

Found during the Stage B Yukon integration (`proximity-research`, branch
`crrg-stage-b-yukon`), *not* by CRRG's own gate — and it cannot be, because both
linters ship with Mathlib and CRRG's core is deliberately Mathlib-free. They fire
only once a downstream project pulls CRRG in alongside Mathlib, which means
**every downstream consumer sees them and CRRG never will**. That asymmetry is
the reason this is recorded here rather than left to be rediscovered.

**`linter.defProp`** — "Definition `X` is a proposition; use `theorem` instead of
`def`". Fires on every `def` whose result type is the `Prop`-valued `Edge`:

| Declaration | File |
|-------------|------|
| `CRRG.Edge.id` | `CRRG/Basic.lean` |
| `CRRG.Edge.trans` | `CRRG/Basic.lean` |
| `CRRG.Edge.comp` | `CRRG/Basic.lean` |
| `CRRG.Split.toEdge` | `CRRG/Split.lean` |
| `CRRG.WitnessMap.toEdge` | `CRRG/Witness.lean` |
| `CRRG.MonotoneFamily.edge` | `CRRG/Monotone.lean` |
| `CRRG.Progress.trans` | `CRRG/Monotone.lean` |

This is a direct consequence of pinning `Edge : Prop` in `CHG-12`, and the fix is
mechanical — `def` → `theorem` on each. Note the interaction before doing it:
`Edge` is proof-irrelevant, so these carry no data and nothing can depend on
their definitional unfolding. Worth confirming that claim against the test suite
rather than assuming it.

**`linter.checkUnivs`** — "`WitnessSplit`: universes `v`, `w` only occur together.
This usually means there is a `max` expression in the type where none of these
universes appear on their own." `CRRG/Witness.lean`. The universe polymorphism
added in `CHG-12` gave `WitnessSplit` separate universes for its branch index and
its child nodes, but they only ever appear together in a `max`, so one of them is
redundant. Collapsing them is a signature change: check `WitnessSplit.toSplit`
and the `GuardedMap`/`EscapeMap` conversions, which instantiate them at different
levels.

Neither is a soundness issue and neither blocks a downstream adapter — the Stage
B reconstruction builds and its axiom audit is clean with both present. They are
noise that every consumer inherits, so they are worth clearing before more
adapters exist.

**To reproduce:** build any project that requires both CRRG and Mathlib; the
warnings appear when CRRG's modules are replayed. There is no way to see them
from CRRG alone.

</details>

**Correct reproduction:** `elan toolchain install leanprover/lean4:v4.32.2`,
point `lean-toolchain` at it, `lake build CRRG Test`. No Mathlib required.
`scripts/crrg-portability` does this automatically (`CHG-22`).
