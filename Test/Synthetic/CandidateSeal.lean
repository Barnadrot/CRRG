import CRRG
import CRRGTest.ExpectFailure

/-!
# Synthetic test: candidate sealing, promotion, and lifecycle enforcement

Exercises Spec §8.3–§8.5 and §8.8. The point of these tests is not that the
happy path works, but that the **illegal** transitions are untypeable:

- a sealed target cannot be weakened in place (§8.5);
- promotion requires a proof of the *exact* sealed proposition (§8.4);
- refutation requires a disproof of it;
- a resolved candidate cannot be promoted afterwards (the gap that existed when
  status was a mutable field).
-/

open CRRG

/-! ## Draft → sealed → certified, the intended path. -/

private def draft001 : DraftCandidate where
  id := "E001"
  sourceIds := ["N010", "N011"]
  targetId := "N020"
  expectedTheoremName := "Downstream.e001"
  targetProp := ∀ n : Nat, n + 0 = n

private def sealed001 : SealedCandidate draft001.targetProp :=
  draft001.seal "9f2c…" "8b521ed" "2026-08-25T00:00:00Z"

-- Spec 8.3: the record carries source ids, target id and expected theorem name.
example : sealed001.record.id = "E001" := rfl
example : sealed001.record.sourceIds = ["N010", "N011"] := rfl
example : sealed001.record.targetId = "N020" := rfl
example : sealed001.record.expectedTheoremName = "Downstream.e001" := rfl
-- Spec 8.8: history fields are present at seal time.
example : sealed001.record.sealHash = "9f2c…" := rfl
example : sealed001.record.sourceCommit = "8b521ed" := rfl

-- A sealed, unresolved candidate is exactly the promotable state. Under the old
-- API nothing could ever reach this status, so `isPromotable` was dead code.
example : sealed001.status = .sealedUnverified := rfl
example : sealed001.status.isPromotable = true := rfl
example : sealed001.status.isTerminal = false := rfl

private def promoted001 : ResolvedCandidate draft001.targetProp :=
  sealed001.promote (fun n => Nat.add_zero n) "sha-of-theorem"

example : promoted001.status = .certified := rfl
example : promoted001.status.isTerminal = true := rfl
-- Provenance survives resolution.
example : promoted001.sealed.record.id = "E001" := rfl

-- Certification really does yield a proof of the exact sealed proposition.
example : ∀ n : Nat, n + 0 = n := promoted001.certified_sound rfl

/-! ## Promotion demands the exact proposition. -/

/- Negative: a proof of a different, weaker proposition does not promote. This is
the anti-proxy rule (§8.5) at the type level. -/
#expect_failure
private def proxyPromotion : ResolvedCandidate draft001.targetProp :=
  sealed001.promote (rfl : (0 : Nat) + 0 = 0) "sha"

/- Negative: a sealed candidate cannot be re-typed to an easier target. The
proposition is a type parameter, so this is not a mutation — it is a type
error. -/
#expect_failure
private def weakenedSeal : SealedCandidate ((0 : Nat) + 0 = 0) := sealed001

/-! ## Refutation demands a disproof. -/

private def draftFalse : DraftCandidate where
  id := "E002"
  sourceIds := []
  targetId := "N021"
  expectedTheoremName := "Downstream.e002"
  targetProp := (0 : Nat) = 1

private def sealedFalse : SealedCandidate draftFalse.targetProp :=
  draftFalse.seal "aa11…" "8b521ed" "2026-08-25T00:00:00Z"

private def refutedFalse : ResolvedCandidate draftFalse.targetProp :=
  -- NB: `by decide` cannot be used here. `draftFalse.targetProp` is a projection
  -- of a plain `def`, which instance search will not unfold, so no `Decidable`
  -- instance is found. A term proof elaborates at default transparency and works.
  sealedFalse.refute (fun h => Nat.noConfusion h) "0 = 1 is false in Nat"

example : refutedFalse.status = .refuted := rfl
example : refutedFalse.status.isTerminal = true := rfl

/- Negative: `refute` requires an actual disproof. A reason string alone is
`markInvalid`, which makes no claim about the proposition. -/
#expect_failure
private def bogusRefutation : ResolvedCandidate draft001.targetProp :=
  sealed001.refute (fun _ => trivial) "I think this is false"

/-! ## The remaining terminal states are honest non-claims. -/

private def malformed001 : ResolvedCandidate draft001.targetProp :=
  sealed001.markMalformed "omits the rank-free H1 premise"

private def invalid001 : ResolvedCandidate draft001.targetProp :=
  sealed001.markInvalid "intended route contradicted by the H2 count"

private def superseded001 : ResolvedCandidate draft001.targetProp :=
  sealed001.supersede "E023" "premise X added explicitly"

example : malformed001.status = .malformed := rfl
example : invalid001.status = .invalid := rfl
example : superseded001.status = .superseded := rfl

-- Spec 8.5: superseding preserves the old exact target. It is still visible in
-- this record's type and its provenance is intact.
example : superseded001.sealed.record.id = "E001" := rfl
example : SealedCandidate draft001.targetProp := superseded001.sealed

/-! ## No transition out of a terminal state. -/

-- Every outcome is terminal, and no resolved candidate is promotable. Under the
-- old API `markRefuted` returned a value that `promote` still accepted.
example (r : ResolvedCandidate draft001.targetProp) : r.status.isPromotable = false :=
  r.not_promotable

example (o : Outcome draft001.targetProp) : o.status.isTerminal = true :=
  o.status_isTerminal

/- Negative: a resolved candidate is not a sealed candidate, so it cannot be fed
back into `promote`. -/
#expect_failure
private def repromote : ResolvedCandidate draft001.targetProp :=
  SealedCandidate.promote refutedFalse (fun n => Nat.add_zero n) "sha"

/- Negative: `certified_sound` cannot be applied to a non-certified resolution,
so a refuted candidate yields no proof. -/
#expect_failure
private theorem refutedYieldsProof : (0 : Nat) = 1 :=
  refutedFalse.certified_sound rfl

/-! ## The promotion queue is separate from the certified graph. -/

private inductive QTask | e001 | e002
  deriving DecidableEq

private def queue : PromotionQueue where
  Task := QTask
  target
    | .e001 => draft001.targetProp
    | .e002 => draftFalse.targetProp
  entry
    | .e001 => sealed001
    | .e002 => sealedFalse

example : queue.target QTask.e001 = (∀ n : Nat, n + 0 = n) := rfl

/- Negative: a promotion queue entry cannot close a root. Only a `Frontier` can,
and the two are unrelated types. -/
#expect_failure
private def queueClosesRoot : Frontier ⟨∀ n : Nat, n + 0 = n⟩ := queue
