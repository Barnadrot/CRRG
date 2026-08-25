import CRRG
import Test.Support.ExpectFailure

/-!
# Synthetic test: frontier and queue reporting

Spec §5.6, §8.7, §14.2 items 6 and 7. The invariant under test is negative: the
gate's output must contain **only** per-task lines in exactly three states, and
must never contain an aggregate count or percentage.
-/

open CRRG

private inductive RTask | fpMomentBudget | genericTail | retiredRoute
  deriving DecidableEq

private def root : Goal := ⟨True ∧ True⟩

private def frontier : Frontier root where
  Task := RTask
  leaf
    | .fpMomentBudget => ⟨True⟩
    | .genericTail => ⟨True⟩
    | .retiredRoute => ⟨True⟩
  closeRoot h := ⟨h .fpMomentBudget, h .genericTail⟩

private def report : FrontierReport root where
  frontier := frontier
  tasks := [RTask.fpMomentBudget, RTask.genericTail, RTask.retiredRoute]
  taskId
    | .fpMomentBudget => "T000_FpMomentBudget"
    | .genericTail => "T001_GenericTail"
    | .retiredRoute => "T002_RetiredRoute"
  status
    | .fpMomentBudget => .closed
    | .genericTail => .«open»
    | .retiredRoute => .invalid

/-! ## Only the three permitted states are ever printed (§14.2 item 6). -/

example : TaskStatus.«open».render = "OPEN" := rfl
example : TaskStatus.closed.render = "CLOSED" := rfl
example : TaskStatus.invalid.render = "INVALID" := rfl

example (s : TaskStatus) :
    s.render = "OPEN" ∨ s.render = "CLOSED" ∨ s.render = "INVALID" := s.render_mem

/-! ## Exactly one line per task — the no-aggregate guarantee (§5.6, §14.2 item 7). -/

example : report.render.length = report.tasks.length := report.render_length
example : report.render.length = 3 := rfl

example : report.render =
    ["T000_FpMomentBudget: CLOSED",
     "T001_GenericTail: OPEN",
     "T002_RetiredRoute: INVALID"] := rfl

-- Every emitted line is a task line; there is no summary line to be found.
example : ∀ line ∈ report.render, ∃ i ∈ report.tasks,
    line = report.taskId i ++ ": " ++ (report.status i).render :=
  report.render_states

/- Negative: `FrontierReport` has no aggregate field. A percentage cannot be
attached to a report, because there is nowhere to put it. -/
#expect_failure
private def withPercentage : FrontierReport root :=
  { frontier := frontier
    tasks := []
    taskId := fun _ => ""
    status := fun _ => .«open»
    completionPercentage := 66 }

/- Negative: there is no fourth task state. A downstream adapter cannot invent
`PARTIAL` or `IN_PROGRESS`. -/
#expect_failure
private def fourthState : TaskStatus := .partial

/-! ## Task count is available to an orchestrator but is not part of the output.

Spec §7.3: "task count has no reward meaning". Looping over tasks is fine;
printing the count in the gate's output is not. -/

example : report.taskCount = 3 := rfl
-- The count does not appear in the rendered output.
example : "3" ∉ report.render := by decide

/-! ## The promotion queue renders separately from the certified frontier (§8.7). -/

private def qDraft : DraftCandidate where
  id := "E017"
  sourceIds := ["T000_FpMomentBudget"]
  targetId := "T001_GenericTail"
  expectedTheoremName := "Downstream.e017"
  targetProp := True

private def qSealed : SealedCandidate qDraft.targetProp :=
  qDraft.seal "beef…" "8b521ed" "2026-08-25T00:00:00Z"

private inductive QT | e017
  deriving DecidableEq

private def queue : PromotionQueue where
  Task := QT
  target _ := qDraft.targetProp
  entry _ := qSealed

private def queueReport : QueueReport where
  queue := queue
  entries := [QT.e017]

example : queueReport.render =
    ["[E017 SEALED_UNVERIFIED] expects Downstream.e017 for T001_GenericTail"] := rfl

example : queueReport.render.length = queueReport.entries.length :=
  queueReport.render_length

/- Negative: a queue report is not a frontier report. The certified graph and the
promotion queue are separate renderings and cannot be merged. -/
#expect_failure
private def mergedReport : FrontierReport root := queueReport
