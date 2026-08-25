# CRRG Changelog

Audit trail for the Certified Research Reduction Graph implementation.

This file is the **plan of record** for spec conformance. Section 1 is the
conformance matrix: every normative requirement in [`Spec.md`](Spec.md), its
implementation status, and the change that last touched it. Section 2 is the
chronological change log. Section 3 records deliberate deviations from the spec
and the reason for each.

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
| 2.2 | `Test/YukonReplay/` fixture | DEFERRED | Stage B |
| 2.3 | Downstream adapter shape | DONE | `CHG-08` |
| 2.4 | Sibling-checkout development builds | DONE | `CHG-08` |
| 2.4 | Pinned-SHA integration builds | DEFERRED | needs a published CRRG SHA |

### §5 (4.x) Trust model

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 4.1 | Frozen root | DOWNSTREAM | the root is a downstream declaration |
| 4.2 | Every edge is a Lean theorem | DONE | prose arrows are not representable |
| 4.3 | Every split proves coverage | DONE | `Split.discharge` |
| 4.4 | Guards produce sibling branches | DONE | `GuardedMap` |
| 4.5 | Exceptions are never deleted | DONE | `EscapeMap` |
| 4.6 | No synthetic global percentage | MISSING | no gate forbids emitting one |

### §6 (5.x) Lean API

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 5.1 | `Goal`, `Goal.Proved`, `Edge`, `Edge.id/trans` | DONE | |
| 5.1 | `Edge` universe explicit, not inferred | MISSING | inferred `Prop`; a later data field silently changes it |
| 5.2 | `Split` with coverage proof | DONE | |
| 5.3 | `BadNode`, `BadNode.Closed` | DONE | `DEV-01` |
| 5.3 | `WitnessMap`, `WitnessSplit`, `closed_parent` | DONE | `CHG-10` |
| 5.3 | Witness / branch / task types universe-polymorphic | MISSING | pinned to `Type 0` |
| 5.4 | `EscapeMap` | DONE | |
| 5.5 | `GuardedMap` consuming both truth values | DONE | |

### §7 (6.x) Root package and live frontier

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 6.1–6.2 | Exact root goal and root seam | DOWNSTREAM | |
| 6.3 | `Frontier` package | DONE | |
| 6.4 | Replace one leaf by a child via `Edge`, siblings preserved | DONE | `CHG-09` |
| 6.4 | Replace one leaf by children via `Split`, siblings preserved | DONE | `CHG-09` |

### §8 (7.x) Typed candidate graph and promotion queue

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 7.1 | No prose edges; every candidate has an exact Lean proposition | DONE | |
| 7.2 | Candidate edges expose all composition debt (Shape A / Shape B) | MISSING | |
| 7.3 | Record carries `sourceIds`, `targetId`, `expectedTheoremName` | MISSING | only `id`, `targetProp`, `status` exist |
| 7.4 | Lifecycle `DRAFT → SEALED_UNVERIFIED → CERTIFIED` | PARTIAL | `sealedUnverified` is unreachable |
| 7.4 | Terminal states reachable and final | MISSING | a refuted candidate can still be promoted |
| 7.5 | Sealed target immutable for the attempt | PARTIAL | convention, not enforced |
| 7.6 | Promotion is not prize progress | DONE | no aggregate is emitted |
| 7.7 | Certified frontier rendered separately from the promotion queue | MISSING | no renderer |
| 7.8 | History: seal hash, commit, timestamp, status, reason | PARTIAL | seal hash only, `CHG-08` |

### §9 LDB counterexample vocabulary

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 9 | `ListViolation` and LDB-specific vocabulary | DOWNSTREAM | `SPEC-03` — contradicts §2.1 |

### §10 (8.x) Quantitative partial progress

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 8.1 | Structural progress via certified splits | DONE | |
| 8.2 | Monotone parameterized families with an explicit monotonicity theorem | MISSING | no representation at all |
| 8.2 | Numerical reward only for a strictly stronger parameter under identical node semantics | MISSING | depends on the above |
| 8.3 | Certified root-bound evaluator | DEFERRED | spec says do not implement yet |

### §11 Agent task contract

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 11.1–11.6 | Task contract documented | DONE | `AGENTS.md` |
| 11 | Binary `OPEN → CLOSED` reward | PARTIAL | documented, not machine-emitted |
| 11 | Monotone-leaf reward variant | MISSING | depends on §8.2 |

### §12 (10.x) Graph-change protocol

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 10.1 | Refinement requires a compiled coverage theorem | DONE | `CHG-09` |
| 10.2 | Invalid refinements rejected | PARTIAL | list not exhausted |
| 10.3 | Retirement removes from the live frontier | DONE | `CHG-09` |

### §14 (12.x) Verification integration

| Req | Requirement | Status | Ref |
|-----|-------------|--------|-----|
| 12.2.1 | Build the live graph and every registered closed-task module | DONE | `crrg-check` |
| 12.2.2 | Reject banned constructs | MISSING | no banned-construct scan |
| 12.2.3 | Transitive `collectAxioms` over the live graph | DONE | `CHG-07` |
| 12.2.4 | Type-link the root exactly | DONE | `Frontier.rootIs` |
| 12.2.5 | Type-link each task theorem exactly | DONE | `Frontier.leafIs` |
| 12.2.6 | Print only `OPEN` / `CLOSED` / `INVALID` per task | MISSING | no task-status renderer |
| 12.2.7 | Print no aggregate count or percentage | MISSING | not asserted by any gate |
| 12.3 | Lean is authority over rendered state | DONE | |

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
| 13 | A sealed target cannot be weakened in place | PARTIAL |
| 14 | Promotion requires the exact proposition plus the axiom/type-link gate | DONE |
| 15 | Yukon damaged-proof cost measured before directing live Soundness | DEFERRED — Stage C |
| 16 | An agent gets a correct binary reward from one exact leaf | PARTIAL |

---

## 2. Change log

### Unreleased

Entries are added as `CHG-nn` (implementation) and `SPEC-nn` (specification) as
work lands.

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
