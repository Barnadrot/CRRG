import CRRG
import CRRGTest.ExpectFailure

/-!
# Synthetic test: Frontier refinement and route retirement

Covers Spec acceptance criterion 5 ("a sample leaf can be refined into two
children only by supplying a compiled coverage theorem") and the Stage A item
"route retirement without deleting historical lineage".

Note the deliberate use of ordinary `def` (not `abbrev`) for the frontier: the
refinement API takes decidable equality as an *explicit* argument precisely so
that it works with ordinary definitions, whose `.Task` field instance search
would not unfold.
-/

open CRRG

private inductive T2 | a | b
  deriving DecidableEq

private def rootGoal : Goal := ⟨(∀ n : Nat, n + 0 = n) ∧ True⟩

private def base : Frontier rootGoal where
  Task := T2
  leaf
    | .a => ⟨∀ n : Nat, n + 0 = n⟩
    | .b => ⟨True⟩
  closeRoot h := ⟨h .a, h .b⟩

private def baseDec : DecidableEq base.Task := inferInstanceAs (DecidableEq T2)

/-! ## Refining one leaf via an Edge preserves the sibling. -/

private def strongerChild : Goal := ⟨∀ n : Nat, n + 0 = n ∧ 0 + n = n⟩

private theorem edgeA : Edge (base.leaf T2.a) strongerChild :=
  ⟨fun h n => (h n).1⟩

private def refined : Frontier rootGoal := base.refineLeaf baseDec T2.a edgeA

-- The refined leaf now carries the stronger child obligation...
example : refined.leaf T2.a = strongerChild := rfl
-- ...and the sibling survived unchanged. Nothing was silently dropped.
example : refined.leaf T2.b = ⟨True⟩ := rfl

example : rootGoal.Proved :=
  refined.closeRoot fun
    | T2.a => fun n => ⟨Nat.add_zero n, Nat.zero_add n⟩
    | T2.b => trivial

/-! ## Refining one leaf into two children requires a coverage proof. -/

private inductive Half | small | large
  deriving DecidableEq

private def coverA : Split (base.leaf T2.a) where
  Branch := Half
  child
    | .small => ⟨∀ n : Nat, n < 5 → n + 0 = n⟩
    | .large => ⟨∀ n : Nat, ¬(n < 5) → n + 0 = n⟩
  discharge h n := if hn : n < 5 then h .small n hn else h .large n hn

private def split2 : Frontier rootGoal := base.splitLeaf baseDec T2.a coverA

-- Three live obligations now: the untouched sibling plus the two children.
example : rootGoal.Proved :=
  split2.closeRoot fun
    | .inl ⟨T2.b, _⟩ => trivial
    | .inl ⟨T2.a, h⟩ => absurd rfl h
    | .inr Half.small => fun n _ => Nat.add_zero n
    | .inr Half.large => fun n _ => Nat.add_zero n

/- Negative: a "split" that only covers the small case has no coverage proof,
so it cannot be built and therefore cannot be used to refine the leaf. -/
#expect_failure
private def bogusCover : Split (base.leaf T2.a) where
  Branch := Unit
  child _ := ⟨∀ n : Nat, n < 5 → n + 0 = n⟩
  discharge h n := h () n (by omega)

/-! ## Retirement: a route leaves the live frontier only when actually proved.

The historical declarations remain in source; what changes is the live task set. -/

private def retired : Frontier rootGoal :=
  base.retireLeaf baseDec T2.b _root_.trivial

-- Only the surviving obligation is live; `.b` is no longer assignable.
example : rootGoal.Proved :=
  retired.closeRoot fun
    | ⟨T2.a, _⟩ => fun n => Nat.add_zero n
    | ⟨T2.b, h⟩ => absurd rfl h

-- Historical lineage is undamaged: the retired route's edge still type-checks
-- and the original frontier is still a well-formed object.
example : Edge (base.leaf T2.a) strongerChild := edgeA
example : Frontier rootGoal := base

/- Negative: retirement is not a deletion. It requires a real proof of the leaf,
so an unproved leaf cannot be retired. -/
#expect_failure
private def bogusRetire : Frontier rootGoal :=
  base.retireLeaf baseDec T2.a _root_.trivial
