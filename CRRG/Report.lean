import CRRG.Frontier
import CRRG.Candidate

/-!
# CRRG.Report

Rendering of the live frontier and the promotion queue (Spec §5.6, §8.7,
§14.2 items 6 and 7).

The spec is unusually specific about *output*:

> 6. print task identifiers with only `OPEN` / `CLOSED` / `INVALID` states;
> 7. print no aggregate count or percentage.

and, as a non-negotiable invariant (§5.6):

> No synthetic global percentage.

The reason is stated in §1: any synthetic magnitude becomes gameable. A "42%
solved" figure invites optimising the figure rather than the mathematics.

This module makes that structural rather than editorial. A `FrontierReport`
renders to **exactly one line per task**, and `render_length` is a theorem
proving it. There is no `count` field, no `total`, no `percentage`, and no
function in this module returns a number derived from the task set. A future
edit that tried to append a summary line would have to break `render_length`,
and the test suite asserts it.
-/

namespace CRRG

universe u

/-- The only states a task may be reported in (§14.2 item 6). -/
inductive TaskStatus
  /-- The obligation is live and unproved. -/
  | «open»
  /-- A theorem discharges the obligation, and it passed the axiom gate. -/
  | closed
  /-- The obligation is not a valid live task: its route was retired or refuted. -/
  | invalid
  deriving DecidableEq, Repr

namespace TaskStatus

/-- The exact printed form. These three strings are the whole reporting
    vocabulary; §14.2 item 6 admits no others. -/
def render : TaskStatus → String
  | .«open» => "OPEN"
  | .closed => "CLOSED"
  | .invalid => "INVALID"

/-- Rendering is injective: the three states are distinguishable in output. -/
theorem render_injective : ∀ a b : TaskStatus, a.render = b.render → a = b := by
  intro a b h
  cases a <;> cases b <;> first | rfl | simp [render] at h

/-- Only these three strings are ever produced. -/
theorem render_mem (s : TaskStatus) :
    s.render = "OPEN" ∨ s.render = "CLOSED" ∨ s.render = "INVALID" := by
  cases s <;> simp [render]

end TaskStatus

/-- A report over a live frontier (§14.2 item 6).

    `tasks` is the enumeration to render, in order. It is supplied explicitly
    rather than derived, because `Frontier.Task` need not be a finite type; the
    downstream adapter is responsible for listing the live tasks.

    Note what this structure does **not** have: no `closedCount`, no `total`, no
    `fraction`. Adding one would be a spec violation (§5.6, §14.2 item 7), and
    `render_length` below would have to be broken to surface it. -/
structure FrontierReport (root : Goal) where
  /-- The live frontier being reported on. -/
  frontier : Frontier.{u} root
  /-- The tasks to render, in order. -/
  tasks : List frontier.Task
  /-- Stable identifier for each task, used as the agent-facing task name. -/
  taskId : frontier.Task → String
  /-- The reported state of each task. -/
  status : frontier.Task → TaskStatus

namespace FrontierReport

variable {root : Goal}

/-- One line per task: `"<id>: <STATE>"`. Nothing else is emitted. -/
def render (r : FrontierReport root) : List String :=
  r.tasks.map fun t => r.taskId t ++ ": " ++ (r.status t).render

/-- **The no-aggregate guarantee (§5.6, §14.2 item 7).**

    The rendered output has exactly as many lines as there are tasks. There is
    therefore no room for a summary line, a count, a total, or a percentage: any
    such line would make the output longer than the task list, and this theorem
    would fail to compile. -/
theorem render_length (r : FrontierReport root) : r.render.length = r.tasks.length := by
  simp [render]

/-- Every emitted line ends in one of the three permitted states (§14.2 item 6). -/
theorem render_states (r : FrontierReport root) :
    ∀ line ∈ r.render, ∃ i ∈ r.tasks,
      line = r.taskId i ++ ": " ++ (r.status i).render := by
  intro line hline
  simp only [render, List.mem_map] at hline
  obtain ⟨i, hi, rfl⟩ := hline
  exact ⟨i, hi, rfl⟩

/-- Task count is available as ordinary list length for an orchestrator that
    needs to iterate, but it is deliberately **not** part of `render`.

    §7.3 of the spec: "task count has no reward meaning". Exposing it as a
    number an orchestrator may loop over is fine; printing it in the graph gate's
    output is not. -/
def taskCount (r : FrontierReport root) : Nat := r.tasks.length

end FrontierReport

/-- A rendering of the typed promotion queue (§8.7).

    Rendered separately from the certified frontier and never merged with it.
    Queue entries contribute zero trusted root closure: only a `Frontier` can
    close a root, and `PromotionQueue` is an unrelated type. -/
structure QueueReport where
  /-- The queue being reported on. -/
  queue : PromotionQueue
  /-- The entries to render, in order. -/
  entries : List queue.Task

namespace QueueReport

/-- One line per sealed candidate, carrying its identity and expected theorem.

    The status is always `SEALED_UNVERIFIED`: a `PromotionQueue` holds only
    unresolved candidates by construction, so there is no state to compute. -/
def render (r : QueueReport) : List String :=
  r.entries.map fun t =>
    let rec_ := (r.queue.entry t).record
    "[" ++ rec_.id ++ " SEALED_UNVERIFIED] expects " ++ rec_.expectedTheoremName
      ++ " for " ++ rec_.targetId

/-- One line per entry, and no aggregate — as for the frontier report. -/
theorem render_length (r : QueueReport) : r.render.length = r.entries.length := by
  simp [render]

end QueueReport

end CRRG
