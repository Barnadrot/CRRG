import CRRG
import Test.Support.ExpectFailure

/-!
# Synthetic test: monotone parameterized families

Spec §10.2. Models a `ListBound`-shaped family: the claim is "every violating
list has at most `B` members", and a **smaller** `B` is the stronger statement.
The toy claim below is arithmetic rather than combinatorial, but the parameter
order and the monotonicity obligation have the same shape as the real thing.
-/

open CRRG

/-! ## A family where smaller is stronger.

Declared with `abbrev`, not `def`. `Stronger` is a structure *field*, so
`listBound.Stronger 7 9` only reduces to `7 ≤ 9` if `listBound` itself is
reducible; with a plain `def`, `omega` sees an opaque atom and fails. This is the
recommended idiom for declaring a family — see the note in Spec §10.2. -/

private abbrev listBound : MonotoneFamily Nat where
  -- `a` is at least as strong as `b` when `a ≤ b`: a smaller bound is stronger.
  Stronger a b := a ≤ b
  -- Toy stand-in for "every violating list has at most `B` members".
  claim B := ∀ n : Nat, n ≤ 3 → n ≤ B
  stronger_refl _ := Nat.le_refl _
  stronger_trans hab hbc := Nat.le_trans hab hbc
  monotone hab ha n hn := Nat.le_trans (ha n hn) hab

-- The claim is provable at 3 and at everything above it, and false below 3.
private theorem bound3 : listBound.claim 3 := fun _ hn => hn
private theorem bound7 : listBound.claim 7 := listBound.monotone (by omega) bound3
private theorem bound9 : listBound.claim 9 := listBound.monotone (by omega) bound7

-- Monotonicity as a CRRG edge, in the usual rootward direction: proving the
-- stronger parameter discharges the weaker goal.
private def tighten : Edge (listBound.goalAt 9) (listBound.goalAt 7) :=
  listBound.edge (by omega)

example : (listBound.goalAt 9).Proved := tighten.discharge bound7

/-! ## Certified quantitative progress. -/

private def improve9to7 : Progress listBound 9 7 where
  improvement := ⟨by omega, by omega⟩
  proof := bound7

-- Progress never loses ground: the old parameter's claim still holds.
example : listBound.claim 9 := improve9to7.implies_old
example : (listBound.goalAt 9).Proved := improve9to7.closes_old_goal

-- Improvements compose.
private def improve7to3 : Progress listBound 7 3 where
  improvement := ⟨by omega, by omega⟩
  proof := bound3
private def improve9to3 : Progress listBound 9 3 := improve9to7.trans improve7to3

example : listBound.claim 9 := improve9to3.implies_old

/-! ## What must be rejected. -/

/- Negative: re-proving the same parameter is not progress. `StrictlyStronger`
is irreflexive, so `Progress F p p` cannot be built. -/
#expect_failure
private def notProgress : Progress listBound 7 7 where
  improvement := ⟨Nat.le_refl 7, Nat.le_refl 7⟩
  proof := bound7

/- Negative: a *weaker* parameter is not progress. Claiming 9 after having 7
must not be rewarded. -/
#expect_failure
private def backwards : Progress listBound 7 9 where
  improvement := ⟨by omega, by omega⟩
  proof := bound9

/- Negative: progress requires a proof at the new parameter, not merely the
claim that it is stronger. -/
#expect_failure
private def unprovenImprovement : Progress listBound 9 2 where
  improvement := ⟨by omega, by omega⟩
  proof := bound7

/-! ## Currencies from different families cannot be exchanged.

Spec §10.2 forbids comparing unrelated local currencies by a hand-chosen
exchange rate. `Progress` is indexed by its family, so this is structural: there
is no operation that takes progress in one family to progress in another. -/

private abbrev momentBound : MonotoneFamily Nat where
  Stronger a b := b ≤ a          -- here LARGER is stronger: opposite direction
  claim k := ∀ n : Nat, n ≤ k → n ≤ k
  stronger_refl _ := Nat.le_refl _
  stronger_trans hab hbc := Nat.le_trans hbc hab
  monotone _ _ n hn := hn

private def momentProgress : Progress momentBound 3 5 where
  improvement := ⟨by omega, by omega⟩
  proof := fun _ hn => hn

/- Negative: progress in `momentBound` is not progress in `listBound`, even
though both have `Param := Nat` and both improve 3 → 5 numerically. -/
#expect_failure
private def exchangeRate : Progress listBound 3 5 := momentProgress

/- Negative: there is no operation combining progress across families. -/
#expect_failure
private def combined : Progress listBound 9 3 := improve9to7.trans momentProgress
