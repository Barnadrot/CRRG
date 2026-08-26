import CRRG
import Test.Support.ExpectFailure

/-!
# Synthetic test: retrospective reconstruction patterns

Spec §15 Stage B validates CRRG by rebuilding an **already solved** proof as a
certified reduction graph. That exercise is necessarily downstream — the proof
being reconstructed is a research project's mathematics, and §2.1 forbids CRRG
from importing any of it.

What is *not* downstream is the shape of the exercise. Stage B produced four
reusable patterns, and each one is a claim about CRRG rather than about the
proof it was applied to. This file states all four against a toy "already
solved" development, so that the patterns are regression-tested inside CRRG and
a future adapter has something to copy.

The mathematics below is deliberately trivial and deliberately anonymous. No
constant, type or lemma here corresponds to anything in a research project; if a
reader recognises a research quantity in this file, it is a boundary violation
and should be removed (§2.1).

## The four patterns

| # | Pattern | What it catches |
|---|---------|-----------------|
| P1 | Coverage by the structure constructor | an invented or dropped obligation |
| P2 | Coverage by refactor, not by re-proof | a split that needs an ingredient the real proof did not |
| P3 | The agreement set | the graph drifting away from the development |
| P4 | Sibling preservation under refinement | a refinement quietly discarding obligations |
-/

open CRRG

namespace Replay

/-! ## The "landed development"

Stand-in for a completed proof: a structured endpoint, an analytic step with
three ingredients, and one isolated premise that the conditional part hangs on.
Written the way a real development is written — as ordinary theorems, with no
CRRG in sight — because that is the situation a retrospective reconstruction
starts from. -/

/-- The isolated premise. Everything conditional is downstream of it. -/
def Premise : Prop := ∀ n : Nat, n < 3 → n * n < 9

/-- The three ingredients of the analytic step. -/
def TermA : Prop := 10 ≤ 12
def TermB : Prop := 12 ≤ 20
def TermC : Prop := 20 ≤ 32

/-- What the analytic step concludes. -/
def AnalyticConclusion : Prop := 10 ≤ 32

/-! Each of these restates its goal in unfolded form before deciding it. That is
Spec §6.6 item 2, and it is not stylistic: `Premise` and `TermA` are plain
`def`s, `decide` runs at reducible transparency, and so it will not unfold them.
A downstream adapter normally *does* declare its predicates with `def`, so this
is the idiom an adapter will need. Writing `by decide` directly fails with
`failed to synthesize Decidable Premise`, an error that names the projection
rather than the cause. -/

theorem premise_holds : Premise := by
  show ∀ n : Nat, n < 3 → n * n < 9
  decide

/-- The first ingredient is the one the premise buys. -/
theorem termA_of_premise (_h : Premise) : TermA := by
  show 10 ≤ 12
  decide

theorem termB_landed : TermB := by show 12 ≤ 20; decide
theorem termC_landed : TermC := by show 20 ≤ 32; decide

/-- The landed analytic theorem. Its body consumes exactly three facts. -/
theorem analytic_of_premise (h : Premise) : AnalyticConclusion :=
  Nat.le_trans (termA_of_premise h) (Nat.le_trans termB_landed termC_landed)

/-- The public endpoint: a three-field structure in `Prop`. -/
structure Endpoint (lo hi : Nat) : Prop where
  admissible : 0 < lo
  reduction : 10 ≤ hi
  score : lo ≤ hi

/-- The landed conditional endpoint. -/
theorem endpoint_of_premise (h : Premise) : Endpoint 3 32 where
  admissible := by decide
  reduction := analytic_of_premise h
  score := by decide

/-- The landed unconditional endpoint. -/
theorem endpoint_landed : Endpoint 3 32 := endpoint_of_premise premise_holds

/-! ## P1 — coverage by the structure constructor

When the root obligation is a `Prop` structure, its fields **are** the
obligations, and the split's coverage proof is the structure's own constructor.
This is the strongest available form of §5.3: the coverage proof cannot be
wrong, because it is the same term Lean uses to build the structure at all. A
split written this way cannot have invented an obligation or dropped one. -/

def root : Goal := ⟨Endpoint 3 32⟩

/-- Type-link the root to the exact endpoint (§14.2 item 4). -/
example : True := (Frontier.trivial root).rootIs (P := Endpoint 3 32) rfl

inductive Obligation
  | admissible
  | reduction
  | score
  deriving DecidableEq

def rootSplit : Split root where
  Branch := Obligation
  child
    | .admissible => ⟨0 < 3⟩
    | .reduction => ⟨10 ≤ 32⟩
    | .score => ⟨3 ≤ 32⟩
  discharge h := ⟨h .admissible, h .reduction, h .score⟩

def frontier : Frontier root := Frontier.ofSplit rootSplit

def frontierDec : DecidableEq frontier.Task := inferInstanceAs (DecidableEq Obligation)

/-- Each leaf is type-linked to the exact field it stands for (§14.2 item 5). -/
example : True := frontier.leafIs (P := 0 < 3) .admissible rfl
example : True := frontier.leafIs (P := 10 ≤ 32) .reduction rfl
example : True := frontier.leafIs (P := 3 ≤ 32) .score rfl

/- Negative: a split that omits an obligation cannot be built, because the
constructor still demands the field it left out. This is the *point* of P1 —
"forgot a case" becomes a type error rather than a review finding. -/
#expect_failure
def truncatedSplit : Split root where
  Branch := Bool
  child
    | true => ⟨0 < 3⟩
    | false => ⟨10 ≤ 32⟩
  discharge h := ⟨h true, h false⟩

/-! ## P2 — coverage by refactor, not by re-proof

A coverage theorem for an existing proof step should be that proof with its
ingredient *calls* replaced by *hypotheses* — same steps, same order. Then the
resulting `Split` is evidence about the landed development rather than about
CRRG: if the real proof needed a fourth ingredient, the refactored version does
not typecheck.

Re-proving the step by some other route would also produce a valid `Split`, and
would prove nothing about whether the graph matches the development. -/

theorem analytic_of_parts (ha : TermA) (hb : TermB) (hc : TermC) :
    AnalyticConclusion :=
  Nat.le_trans ha (Nat.le_trans hb hc)

def analyticGoal : Goal := ⟨AnalyticConclusion⟩

inductive Part
  | a
  | b
  | c
  deriving DecidableEq

def analyticSplit : Split analyticGoal where
  Branch := Part
  child
    | .a => ⟨TermA⟩
    | .b => ⟨TermB⟩
    | .c => ⟨TermC⟩
  discharge h := analytic_of_parts (h .a) (h .b) (h .c)

/-- The analytic step closed through CRRG rather than by calling the landed
theorem. -/
theorem analytic_closed (h : Premise) : AnalyticConclusion :=
  analyticSplit.discharge fun
    | .a => termA_of_premise h
    | .b => termB_landed
    | .c => termC_landed

/- Negative: a coverage theorem that quietly drops an ingredient. The refactor
discipline is what makes this fail — `Nat.le_trans` still needs the middle
step, so there is nowhere to hide the omission. -/
#expect_failure
theorem analytic_of_two (ha : TermA) (hc : TermC) : AnalyticConclusion :=
  Nat.le_trans ha hc

/-! ## P3 — the agreement set

The deliverable of a retrospective reconstruction is **not** "the root closes".
That was already true before CRRG existed — the development proves it. The
deliverable is a set of statements each of which stops compiling if the graph
drifts from the development.

**What an agreement check does and does not establish.** The endpoint is a
`Prop`, so proof irrelevance makes any two of its inhabitants definitionally
equal, and an `rfl` between two proofs of it is not comparing *terms*. What it
compares is the two type ascriptions: the check passes only if CRRG's closure
and the landed theorem inhabit the same proposition. That is exactly the
property worth checking — a reconstruction that closed a *different* endpoint
would be the failure — but it should not be read as "the graph produces the same
proof term". Stating this here so the pattern is copied with the right
expectation. -/

/-- **A1.** The root is syntactically the endpoint. -/
theorem agree_root : root.claim = Endpoint 3 32 := rfl

theorem crrg_closes_root : root.Proved :=
  frontier.closeRoot fun
    | .admissible => endpoint_landed.admissible
    | .reduction => endpoint_landed.reduction
    | .score => endpoint_landed.score

/-- **A2.** CRRG's closure and the landed endpoint inhabit the same
proposition. -/
example : (crrg_closes_root : Endpoint 3 32) = (endpoint_landed : Endpoint 3 32) :=
  rfl

/-- **A3.** The level-1 branches really are the structure's fields: coverage is
the constructor. -/
example (h : ∀ i, (rootSplit.child i).claim) :
    rootSplit.discharge h =
      (⟨h .admissible, h .reduction, h .score⟩ : Endpoint 3 32) := rfl

/-- **A4.** The CRRG-assembled analytic step and the landed analytic theorem
agree. Had the split strengthened a hypothesis or weakened the conclusion, these
two would no longer have the same type. -/
example (h : Premise) :
    (analytic_closed h : AnalyticConclusion) =
      (analytic_of_premise h : AnalyticConclusion) := rfl

/-- **A5.** The quantitative side conditions are the recorded constants.
Changing any of them breaks the build. -/
example : (3 : Nat) = 3 := rfl
example : (32 : Nat) = 32 := rfl

/-! **A6.** The check that would catch a genuine reconstruction error: the same
quantity reached by two different routes must be the same number. In a real
reconstruction the root states a parameter one way and a lower layer states it
another, and a graph that reconstructed a *different* certificate could still
compile if nobody tied the two spellings together. -/

/-- The root's spelling of the bound. -/
def rootBound : Nat := 32

/-- The analytic layer's spelling of the same bound. -/
def analyticBound : Nat := 2 * 4 * 4

theorem agree_bound : rootBound = analyticBound := by decide

/- Negative: the agreement check is not vacuous. A second spelling that is *not*
the same number is rejected, which is what makes A6 load-bearing rather than
decorative. -/
def driftedBound : Nat := 2 * 4 * 5

#expect_failure
theorem agree_drifted : rootBound = driftedBound := by decide

/-! ## P4 — sibling preservation under refinement

Refining one leaf must leave every other leaf untouched. §12.2 names the failure
this guards against: a change that "adds children" while quietly losing the
obligations it did not touch. `Frontier.refineLeaf` preserves siblings by
construction, and these `rfl`s are how an adapter asserts it. -/

def premiseGoal : Goal := ⟨Premise⟩

/-- Rootward, as always: prove the premise and the reduction obligation
follows. Discharged by projecting the landed conditional endpoint, so no
analytic step is repeated. -/
theorem reductionEdge : Edge (rootSplit.child .reduction) premiseGoal :=
  ⟨fun h => (endpoint_of_premise h).reduction⟩

def refined : Frontier root :=
  frontier.refineLeaf frontierDec .reduction reductionEdge

/-- The refinement replaced the leaf it targeted... -/
example : refined.leaf .reduction = premiseGoal := rfl

/-- ...and preserved both siblings. -/
example : refined.leaf .admissible = rootSplit.child .admissible := rfl
example : refined.leaf .score = rootSplit.child .score := rfl

/-- The refined frontier still closes the exact same root. -/
theorem refined_closes_root : root.Proved :=
  refined.closeRoot fun
    | .admissible => endpoint_landed.admissible
    | .reduction => premise_holds
    | .score => endpoint_landed.score

/-! `Frontier.compose` is **not** a refinement operator, and the difference is
worth making concrete rather than leaving as a warning in §7.4. It re-roots an
entire frontier through an `Edge`, and its result's leaves are exactly the
*inner* frontier's leaves. -/

private abbrev composed : Frontier (rootSplit.child .reduction) :=
  Frontier.compose reductionEdge (Frontier.trivial premiseGoal)

example : composed.leaf () = premiseGoal := rfl

/- Negative: the composed frontier does not retain the outer frontier's other
obligations — it does not mention them at all. `refineLeaf` above kept
`admissible` and `score`; `compose` would have discarded both. -/
#expect_failure
example : composed.leaf () = rootSplit.child .admissible := rfl

/-! ## The live report

Every obligation is closed, because the development is complete — which is
exactly what makes it usable as a reconstruction fixture (§15 Stage B). -/

def report : FrontierReport root where
  frontier := refined
  tasks := [Obligation.admissible, .reduction, .score]
  taskId
    | .admissible => "R000_Admissible"
    | .reduction => "R001_Premise"
    | .score => "R002_Score"
  status
    | .admissible => .closed
    | .reduction => .closed
    | .score => .closed

example : report.render =
    ["R000_Admissible: CLOSED",
     "R001_Premise: CLOSED",
     "R002_Score: CLOSED"] := rfl

/-- No aggregate, by theorem rather than by convention (§14.2 item 7). -/
example : report.render.length = report.tasks.length := report.render_length

end Replay
