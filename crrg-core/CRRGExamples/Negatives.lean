import CRRGExamples.Basic

/-!
# Examples 4–7: class-cap restatement, learned conflicts, owner-pinned measures, guarded moves
-/

namespace CRRGExamples

open CRRGCore

/-! ## 4. Class-cap-style restatement: sound, and refused credit

A toy restatement. `ListBound` stands for a list-decoding bound, and `ClassCap`
restates it through another definition (syndrome-class form). They are definitionally equal, so
detector D1 (`#crrg_assert_restatement`, `Audit.lean`) flags them. The move is accepted, since it is
sound, but it is tagged not certified easier and earns no credit. -/

/-- Stand-in for the list-decoding bound. -/
def ListBound : Prop := ∀ n : Nat, n + 0 = n

/-- Stand-in for a per-class cap: the same bound, restated through another definition. -/
def ClassCap : Prop := ∀ n : Nat, n = n + 0

def C0 : State ⟨ListBound⟩ := State.initial ⟨ListBound⟩ []

def restateMove : Move C0 :=
  Move.ofEdge C0 ⟨0, Nat.zero_lt_one⟩ ⟨ClassCap⟩ ⟨fun h n => (h n).symm⟩

example : tagOf? (State.commit C0 restateMove) = some .notCertifiedEasier := rfl

/-- No credit. -/
example : (stateOr (State.commit C0 restateMove) C0).easierCount = 0 := rfl

/-- By construction: `top` is never below `top`. -/
example : ¬ Label.lt .top .top := Label.not_lt_top_top

/-! ## 5. Refutation is a learned conflict; a refuted obligation is never re-admitted -/

/-- An open-looking root claim. -/
def R : Prop := ∀ n : Nat, n < n + 1

def F0 : State ⟨R⟩ := State.initial ⟨R⟩ []

/-- A sound but bad split of `R` into `1 = 2` and `R` itself. -/
def badSplit : Split (F0.leafGoal ⟨0, Nat.zero_lt_one⟩) where
  children := [⟨1 = 2⟩, ⟨R⟩]
  discharge h := h ⟨R⟩ (by simp)

def F1 : State ⟨R⟩ :=
  stateOr (State.commit F0 (Move.ofSplit F0 ⟨0, Nat.zero_lt_one⟩ badSplit)) F0

example : F1.leaves = [1, 2] := rfl

/-- Refute the leaf `1 = 2` (key 1) with its disproof. -/
def F2 : State ⟨R⟩ := F1.refute ⟨0, by decide⟩ (show ¬ (1 = 2) by decide)

/-- Key 1 is a learned conflict, and the state backtracked to the root frontier. -/
example : F2.conflicts = [1] := rfl
example : F2.leaves = [0] := rfl

/-- An attempt to re-admit the refuted obligation by its key. The coverage proof is valid:
`1 = 2` implies anything. -/
def readmit : Move F2 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.old 1]
  cover h := by
    have h1 : holds F2.reg 1 := h (.old 1) (List.mem_singleton.mpr rfl)
    have hv : 1 < F2.reg.length := by decide
    have h12 : 1 = 2 := (holds_iff hv).mp h1
    exact absurd h12 (by decide)

/-- **Rejected**: key 1 is a learned conflict. -/
example : rejectOf? (State.commit F2 readmit) = some (.learnedConflict 1) := rfl

/-- A restatement under a *new* key, `1 = 2 ∧ True`, is not caught by the key check. -/
def restatedFalse : Goal := ⟨1 = 2 ∧ True⟩

def readmitRestated : Move F2 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new ⟨restatedFalse, .top, trivial⟩]
  cover h := by
    have h1 : 1 = 2 ∧ True := h _ (List.mem_singleton.mpr rfl)
    exact absurd h1.1 (by decide)

def F3 : State ⟨R⟩ := stateOr (State.commit F2 readmitRestated) F2

example : F3.leaves = [3] := rfl

/-- Once a detector supplies the implication `key 3 → key 1`, `learn` propagates the conflict:
key 3 is refuted too, and the state backtracks. -/
def F4 : State ⟨R⟩ :=
  F3.learn 3 (by decide) 1 (by decide) (fun h3 => by
    have hv3 : 3 < F3.reg.length := by decide
    have hv1 : 1 < F3.reg.length := by decide
    have h : 1 = 2 ∧ True := (holds_iff hv3).mp h3
    exact (holds_iff hv1).mpr h.1)

example : F4.conflicts = [3, 1] := rfl
example : F4.leaves = [0] := rfl

/-! ## 6. Owner-pinned measure: range splits are certified easier, a same-size restatement is not -/

/-- The property of each point. -/
def Pt (x : Nat) : Prop := x * 0 = 0

/-- The owner-pinned family: ranges `[a, b]`, of size `b + 1 - a`. -/
def rangeFam : Family where
  Idx := Nat × Nat
  claim q := ∀ x, q.1 ≤ x → x ≤ q.2 → Pt x
  size q := q.2 + 1 - q.1

def fams : List Family := [rangeFam]

/-- A registry entry for the range `q`, labelled with its pinned size. -/
def rangeEntry (q : Nat × Nat) : Entry fams :=
  ⟨⟨rangeFam.claim q⟩, .sized 0 (rangeFam.size q), ⟨by decide, q, rfl, rfl⟩⟩

/-- The root is **born measured**: label `sized 0 10` with its instance proof (review item 4). -/
def G0 : State (rangeGoal Pt 0 9) :=
  State.initial (rangeGoal Pt 0 9) fams (.sized 0 10) ⟨by decide, (0, 9), rfl, rfl⟩

/-- The owner cannot be bypassed: the root and the family list are fixed at `initial`. -/
example : G0.fams.length = 1 := rfl

/-- Split `[0, 9]` into `[0, 4]` and `[5, 9]`. -/
def rangeMove1 : Move G0 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new (rangeEntry (0, 4)), .new (rangeEntry (5, 9))]
  cover h := (rangeSplit Pt 0 4 9).discharge fun c hc => by
    simp [rangeSplit] at hc
    rcases hc with rfl | rfl
    · exact h (.new (rangeEntry (0, 4))) (by simp)
    · exact h (.new (rangeEntry (5, 9))) (by simp)

/-- Size 10 to sizes 5 and 5: certified easier. -/
example : tagOf? (State.commit G0 rangeMove1) = some .certifiedEasier := rfl

def G1 : State (rangeGoal Pt 0 9) := stateOr (State.commit G0 rangeMove1) G0

/-- Split `[0, 4]` (size 5) into `[0, 1]` (size 2) and `[2, 4]` (size 3): certified easier. -/
def rangeMove2 : Move G1 where
  pos := ⟨0, by decide⟩
  children := [.new (rangeEntry (0, 1)), .new (rangeEntry (2, 4))]
  cover h := by
    have h1 : rangeFam.claim (0, 1) := h (.new (rangeEntry (0, 1))) (by simp)
    have h2 : rangeFam.claim (2, 4) := h (.new (rangeEntry (2, 4))) (by simp)
    show ∀ x, 0 ≤ x → x ≤ 4 → Pt x
    intro x h0 h4
    by_cases hx : x ≤ 1
    · exact h1 x h0 hx
    · exact h2 x (by omega) h4

example : tagOf? (State.commit G1 rangeMove2) = some .certifiedEasier := rfl

/-- Restate `[0, 4]` as a fresh entry for the same range (same pinned size): not certified
easier, since `5 < 5` fails. This is circling, and it earns nothing. -/
def rangeMoveCircle : Move G1 where
  pos := ⟨0, by decide⟩
  children := [.new (rangeEntry (0, 4))]
  cover h := h (.new (rangeEntry (0, 4))) (by simp)

example : tagOf? (State.commit G1 rangeMoveCircle) = some .notCertifiedEasier := rfl

/-- A closure (rung 1) is certified easier: it has no children. -/
def closeMove : Move G1 :=
  Move.close G1 ⟨0, by decide⟩ (show ∀ x, 0 ≤ x → x ≤ 4 → Pt x from fun x _ _ => Nat.mul_zero x)

example : tagOf? (State.commit G1 closeMove) = some .certifiedEasier := rfl

/-! ## 6b. Review item 4 and the record-low rule: growth and restatement earn nothing -/

/-- Replace the measured root `[0, 9]` (size 10) by the **stronger** `[0, 19]` (size 20). Sound,
since the larger range implies the smaller one, but not a decrease. -/
def growMove : Move G0 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new (rangeEntry (0, 19))]
  cover h := by
    have hp : rangeFam.claim (0, 19) := h _ (List.mem_singleton.mpr rfl)
    show ∀ x, 0 ≤ x → x ≤ 9 → Pt x
    exact fun x h0 h9 => hp x h0 (by omega)

example : tagOf? (State.commit G0 growMove) = some .notCertifiedEasier := rfl

/-- An exact restatement of the measured root (size 10 to size 10): not credited. -/
def restateRootMove : Move G0 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new (rangeEntry (0, 9))]
  cover h := h _ (List.mem_singleton.mpr rfl)

example : tagOf? (State.commit G0 restateRootMove) = some .notCertifiedEasier := rfl

/-- Grow, then shrink: from `G1` (`[0,4], [5,9]`, record `[5, 5]`) grow `[0, 4]` to `[0, 19]`, then
split `[0, 19]` into `[0, 4]` and `[5, 19]`. The shrink is a *local* decrease (20 to 5 and 15), but
the frontier `[5, 15, 5]` is not below the record `[5, 5]`: **no credit**. -/
def growG1 : Move G1 where
  pos := ⟨0, by decide⟩
  children := [.new (rangeEntry (0, 19))]
  cover h := by
    have hp : rangeFam.claim (0, 19) := h _ (List.mem_singleton.mpr rfl)
    show ∀ x, 0 ≤ x → x ≤ 4 → Pt x
    exact fun x h0 h4 => hp x h0 (by omega)

def G1g : State (rangeGoal Pt 0 9) := stateOr (State.commit G1 growG1) G1

example : tagOf? (State.commit G1 growG1) = some .notCertifiedEasier := rfl
example : G1g.leafLabels = [.sized 0 20, .sized 0 5] := rfl
example : G1g.record = [.sized 0 5, .sized 0 5] := rfl

def shrinkG1g : Move G1g where
  pos := ⟨0, by decide⟩
  children := [.new (rangeEntry (0, 4)), .new (rangeEntry (5, 19))]
  cover h := by
    have h1 : rangeFam.claim (0, 4) := h (.new (rangeEntry (0, 4))) (by simp)
    have h2 : rangeFam.claim (5, 19) := h (.new (rangeEntry (5, 19))) (by simp)
    show ∀ x, 0 ≤ x → x ≤ 19 → Pt x
    intro x h0 h19
    by_cases hx : x ≤ 4
    · exact h1 x h0 hx
    · exact h2 x (by omega) h19

/-- The local decrease is there, but the record forbids credit. -/
example : State.localEasier G1g shrinkG1g = true := rfl
example : tagOf? (State.commit G1g shrinkG1g) = some .notCertifiedEasier := rfl

/-! ## 4b. A genuine equivalence that D1 misses: the swapped conjunction (review item 8)

`direct n` and `swapped n` are equivalent but not definitionally equal. D1 (`#crrg_assert_restatement`)
rejects the pair (`Audit.lean`). The conflict still propagates through `learn` with the supplied
equivalence. -/

def direct (n : Nat) : Prop := n ≤ 10 ∧ 2 ≤ n
def swapped (n : Nat) : Prop := 2 ≤ n ∧ n ≤ 10

theorem direct_iff_swapped (n : Nat) : direct n ↔ swapped n :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- A root and a bad split containing `direct 11` (false). -/
def Q0 : State ⟨R⟩ := State.initial ⟨R⟩ []

def qSplit : Split (Q0.leafGoal ⟨0, Nat.zero_lt_one⟩) where
  children := [⟨direct 11⟩, ⟨R⟩]
  discharge h := h ⟨R⟩ (by simp)

def Q1 : State ⟨R⟩ := stateOr (State.commit Q0 (Move.ofSplit Q0 ⟨0, Nat.zero_lt_one⟩ qSplit)) Q0

/-- Refute `direct 11` (key 1). -/
def Q2 : State ⟨R⟩ := Q1.refute ⟨0, by decide⟩ (show ¬ direct 11 by unfold direct; decide)

/-- A fresh `swapped 11` passes the key check... -/
def qSwapMove : Move Q2 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new ⟨⟨swapped 11⟩, .top, trivial⟩]
  cover h := by
    have : swapped 11 := h _ (List.mem_singleton.mpr rfl)
    exact absurd this (by unfold swapped; decide)

def Q3 : State ⟨R⟩ := stateOr (State.commit Q2 qSwapMove) Q2

example : Q3.leaves = [3] := rfl

/-- ...and `learn`, fed the equivalence, refutes it and backtracks. -/
def Q4 : State ⟨R⟩ :=
  Q3.learn 3 (by decide) 1 (by decide) (fun h3 => by
    have hv3 : 3 < Q3.reg.length := by decide
    have hv1 : 1 < Q3.reg.length := by decide
    have h : swapped 11 := (holds_iff hv3).mp h3
    exact (holds_iff hv1).mpr ((direct_iff_swapped 11).mpr h))

example : Q4.conflicts = [3, 1] := rfl
example : Q4.leaves = [0] := rfl

/-! ## 5b. A dead route admits nothing (review item 6) -/

def deadRoot : State ⟨1 = 2⟩ := State.initial ⟨1 = 2⟩ []
def dead : State ⟨1 = 2⟩ := deadRoot.refute ⟨0, Nat.zero_lt_one⟩ (show ¬ (1 = 2) by decide)

example : dead.rootRefuted = true := rfl

def deadMove : Move dead := Move.ofEdge dead ⟨0, Nat.zero_lt_one⟩ ⟨1 = 2⟩ ⟨id⟩

example : rejectOf? (State.commit dead deadMove) = some .rootRefuted := rfl

/-! ## 7. A guarded move commits its escape leaf -/

section Guarded

def Gd : Prop := 3 ≤ 5

instance : Decidable Gd := inferInstanceAs (Decidable (3 ≤ 5))

def H0 (P : Prop) : State ⟨P⟩ := State.initial ⟨P⟩ []

/-- A guarded reduction `P ⇐[Gd] Q`: the move commits `Gd → Q` and the escape `¬Gd → P`. -/
def guardedMove (P Q : Prop) (e : GuardedEdge ⟨P⟩ ⟨Q⟩ Gd) : Move (H0 P) :=
  Move.ofSplit (H0 P) ⟨0, Nat.zero_lt_one⟩ e.toSplit

example (P Q : Prop) (e : GuardedEdge ⟨P⟩ ⟨Q⟩ Gd) :
    (stateOr (State.commit (H0 P) (guardedMove P Q e)) (H0 P)).leaves = [1, 2] := rfl

/-- The escape leaf is in the committed registry at key 2. -/
example (P Q : Prop) (e : GuardedEdge ⟨P⟩ ⟨Q⟩ Gd) :
    ((stateOr (State.commit (H0 P) (guardedMove P Q e)) (H0 P)).reg[2]?).map (·.goal) =
      some (GuardedEdge.escapeLeaf ⟨P⟩ Gd) := rfl

end Guarded

/-! ## L-01. Closure is accepted without necessarily lowering the credited record

The owner pins a constant true claim with its Nat index as size. Grow the size-1
root to two size-2 children, then close both. The final closure is credited only
when supplied with the explicit record certificate in this lagging-record example.
-/

namespace ClosureRecord

def family : Family where
  Idx := Nat
  claim _ := True
  size n := n

def families : List Family := [family]

def entry (n : Nat) : Entry families :=
  ⟨⟨True⟩, .sized 0 n, ⟨by decide, n, rfl, rfl⟩⟩

def start : State ⟨True⟩ :=
  State.initial ⟨True⟩ families (.sized 0 1) ⟨by decide, (1 : Nat), rfl, rfl⟩

def grow : Move start where
  pos := ⟨0, by decide⟩
  children := [.new (entry 2), .new (entry 2)]
  cover _ := True.intro

def grown : State ⟨True⟩ := stateOr (State.commit start grow) start

theorem initial_record : start.record = [.sized 0 1] := rfl

theorem grow_accepted :
    State.commit start grow = .ok (grown, .notCertifiedEasier) := rfl

theorem grown_frontier_record :
    grown.leafLabels = [.sized 0 2, .sized 0 2] ∧ grown.record = [.sized 0 1] :=
  ⟨rfl, rfl⟩

def closeOne : Move grown := Move.close grown ⟨0, by decide⟩ True.intro

def oneLeft : State ⟨True⟩ := stateOr (State.commit grown closeOne) grown

theorem close_one_accepted :
    State.commit grown closeOne = .ok (oneLeft, .notCertifiedEasier) := rfl

theorem close_one_frontier_record :
    oneLeft.leafLabels = [.sized 0 2] ∧ oneLeft.record = [.sized 0 1] ∧
      grown.localEasier closeOne = true ∧ oneLeft.easierCount = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

def closeLast : Move oneLeft := Move.close oneLeft ⟨0, by decide⟩ True.intro

def closedWithoutCert : State ⟨True⟩ := stateOr (State.commit oneLeft closeLast) oneLeft

theorem terminal_without_cert_accepted :
    State.commit oneLeft closeLast = .ok (closedWithoutCert, .notCertifiedEasier) := rfl

theorem terminal_without_cert_result :
    closedWithoutCert.leaves = [] ∧ closedWithoutCert.leafLabels = [] ∧
      closedWithoutCert.record = [.sized 0 1] ∧ closedWithoutCert.easierCount = 0 ∧
      closeLast.recordCert = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Deleting the recorded singleton supplies the terminal gamma certificate. -/
theorem empty_below_record : DMLt [] oneLeft.record := by
  apply DMLt.of_step
  exact ⟨0, by decide, [], by simp, rfl⟩

def closeLastWithCert : Move oneLeft :=
  { closeLast with recordCert := some ⟨empty_below_record⟩ }

def closedWithCert : State ⟨True⟩ := stateOr (State.commit oneLeft closeLastWithCert) oneLeft

theorem terminal_with_cert_accepted :
    State.commit oneLeft closeLastWithCert = .ok (closedWithCert, .certifiedEasier) := rfl

theorem terminal_with_cert_result :
    closedWithCert.leaves = [] ∧ closedWithCert.leafLabels = [] ∧
      closedWithCert.record = [] ∧ closedWithCert.easierCount = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

end ClosureRecord

end CRRGExamples
