import CRRGCore

/-!
# Examples 1–3: accepted split, rejected hidden-debt refinement, the Weil chain

Every claim here is checked by `rfl` or `decide`: `commit` is an ordinary Lean function, so its
verdicts and tags are computed by the kernel.
-/

namespace CRRGExamples

open CRRGCore

universe u

/-- `some tag` if the commit was accepted. -/
def tagOf? {α : Type u} : Except Reject (α × Tag) → Option Tag
  | .ok (_, t) => some t
  | .error _ => none

/-- The rejection, if any. -/
def rejectOf? {α : Type u} : Except Reject (α × Tag) → Option Reject
  | .ok _ => none
  | .error r => some r

/-- The accepted state, or a fallback. -/
def stateOr {root : Goal} (e : Except Reject (State root × Tag)) (d : State root) :
    State root :=
  match e with
  | .ok (S, _) => S
  | .error _ => d

/-! ## 1. P split into {A, B}: accepted -/

section SplitAB

variable (A B : Prop)

def rootAB : Goal := ⟨A ∧ B⟩

def S0 : State (rootAB A B) := State.initial (rootAB A B) []

def splitAB : Split ((S0 A B).leafGoal ⟨0, Nat.zero_lt_one⟩) where
  children := [⟨A⟩, ⟨B⟩]
  discharge h := ⟨h ⟨A⟩ (by simp), h ⟨B⟩ (by simp)⟩

def moveAB : Move (S0 A B) := Move.ofSplit (S0 A B) ⟨0, Nat.zero_lt_one⟩ (splitAB A B)

/-- Accepted. Unmeasured children of an unmeasured leaf: sound, but not certified easier. -/
example : tagOf? (State.commit (S0 A B) (moveAB A B)) = some .notCertifiedEasier := rfl

/-- After the split the frontier has two leaves, keys 1 and 2. -/
example : (stateOr (State.commit (S0 A B) (moveAB A B)) (S0 A B)).leaves = [1, 2] := rfl

end SplitAB

/-! ## 2. "Refine P into B" when only A ∧ B ⊢ P: rejected, because no witness exists

In this core, V_refine is "the witness elaborates at type `Edge P B`". From `A ∧ B → P` alone that
type is not inhabited in general (`hidden_debt_not_edge`, counterexample `A := False`,
`B := True`, `P := False`). The admissible move is the explicit split `{A, B}`: the hidden
premise becomes an open leaf. -/

example : ¬ ∀ (A B P : Prop), (A ∧ B → P) → Edge ⟨P⟩ ⟨B⟩ := hidden_debt_not_edge

section Conditional

variable (A B P : Prop) (hAB : A ∧ B → P)

def S0P : State ⟨P⟩ := State.initial ⟨P⟩ []

def condSplit : Split ((S0P P).leafGoal ⟨0, Nat.zero_lt_one⟩) :=
  conditionalSplit ⟨P⟩ [⟨A⟩, ⟨B⟩] fun h => hAB ⟨h ⟨A⟩ (by simp), h ⟨B⟩ (by simp)⟩

/-- The conditional result is accepted, as a split with `A` as an explicit open leaf. -/
example :
    tagOf? (State.commit (S0P P) (Move.ofSplit (S0P P) ⟨0, Nat.zero_lt_one⟩ (condSplit A B P hAB)))
      = some .notCertifiedEasier := rfl

end Conditional

/-! ## 3. The Weil pattern on a real parametric chain (review item 8's arithmetic chain)

Root: `n % 2 = 0 ∨ n = 1`, which is true at 8 and false at 3.
* Move 1 refines it to `n % 2 = 0`: sound, not certified easier (an unmeasured child of an
  unmeasured leaf).
* Move 2a refines `n % 2 = 0` to `∃ k, n = 2 * k`. It is sound, since the implication consumes the
  witness, but it is **not** certified easier: it replaces a decidable goal by an existential, the
  two-pager's Weil-to-unknown pattern.
* Move 2b instead **settles** `n % 2 = 0` at `n = 8` by computation (`closeByComputation`,
  `h := rfl`: the kernel runs the program). This is rung 2 settled as rung 1, and it is certified
  easier. -/

section Weil

/-- A two-way decision procedure for `n % 2 = 0`. -/
def evenCert (n : Nat) : MechCert ⟨n % 2 = 0⟩ where
  decide _ := decide (n % 2 = 0)
  sound_true := of_decide_eq_true
  sound_false := of_decide_eq_false

def evenRoot (n : Nat) : Goal := ⟨n % 2 = 0 ∨ n = 1⟩

def E0 (n : Nat) : State (evenRoot n) := State.initial (evenRoot n) []

def evenMove1 (n : Nat) : Move (E0 n) :=
  Move.ofEdge (E0 n) ⟨0, Nat.zero_lt_one⟩ ⟨n % 2 = 0⟩ ⟨Or.inl⟩

example (n : Nat) : tagOf? (State.commit (E0 n) (evenMove1 n)) = some .notCertifiedEasier := rfl

def E1 (n : Nat) : State (evenRoot n) := stateOr (State.commit (E0 n) (evenMove1 n)) (E0 n)

/-- Move 2a: `n % 2 = 0 ⇐ ∃ k, n = 2 * k`. -/
def evenMove2a (n : Nat) : Move (E1 n) :=
  Move.ofEdge (E1 n) ⟨0, Nat.zero_lt_one⟩ ⟨∃ k, n = 2 * k⟩ ⟨fun ⟨k, hk⟩ => by
    show n % 2 = 0
    rw [hk, Nat.mul_mod_right]⟩

/-- Sound, and **not** certified easier. -/
example (n : Nat) : tagOf? (State.commit (E1 n) (evenMove2a n)) = some .notCertifiedEasier := rfl

/-- Move 2b at `n = 8`: settle by computation; the kernel evaluates `decide (8 % 2 = 0)`. -/
def evenMove2b : Move (E1 8) :=
  Move.closeByComputation (E1 8) ⟨0, Nat.zero_lt_one⟩ (evenCert 8) rfl

/-- **Certified easier** (a closure). -/
example : tagOf? (State.commit (E1 8) evenMove2b) = some .certifiedEasier := rfl

/-- At `n = 3` the program returns `false`: no settlement exists, and the negative certificate
refutes the leaf instead. -/
example : (evenCert 3).decide () = false := rfl
example : ¬ (3 % 2 = 0) := (evenCert 3).refute rfl

/-- Credit after moves 1 and 2b: exactly one. -/
example : (stateOr (State.commit (E1 8) evenMove2b) (E1 8)).easierCount = 1 := rfl

end Weil

end CRRGExamples
