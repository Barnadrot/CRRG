/-!
# CRRG.Candidate

Typed candidate graph and promotion queue (Spec §8).

The certified graph is brutally literal: every certified edge is a Lean theorem.
The candidate layer exists to expose formalization debt *without pretending the
debt has been paid*. Its central discipline is that the lifecycle is enforced by
the type system rather than by convention:

- a candidate's target proposition is a **type parameter**, so it cannot be
  weakened in place (§8.5 — the anti-proxy rule);
- `certified` requires a proof of that exact proposition;
- `refuted` requires a disproof of it;
- each lifecycle state is a distinct type, and the terminal states have no
  outgoing transitions, so a refuted or superseded candidate cannot be promoted.
-/

namespace CRRG

/-- Lifecycle status of a candidate edge (Spec §8.4).

    This enumeration exists for **rendering and reporting**. It is derived from
    the candidate's type, never stored as mutable state: see `Outcome.status`.
    Nothing in CRRG accepts a `CandidateStatus` as evidence of anything. -/
inductive CandidateStatus
  /-- Free research design. May be edited. Carries no graph status and no reward. -/
  | draft
  /-- Exact proposition fixed and hash-anchored for the attempt. A real task. -/
  | sealedUnverified
  /-- A theorem inhabits the exact sealed proposition. May enter the trusted graph. -/
  | certified
  /-- The intended mathematical route is contradicted, without a formal disproof. -/
  | invalid
  /-- The proposition is false, and a disproof exists. -/
  | refuted
  /-- Type-correct, but does not represent the intended composition. -/
  | malformed
  /-- A different sealed candidate replaces it. The old target remains in history. -/
  | superseded
  deriving DecidableEq, Repr

namespace CandidateStatus

/-- A status is terminal when no further transition is possible. -/
def isTerminal : CandidateStatus → Bool
  | .draft => false
  | .sealedUnverified => false
  | .certified => true
  | .invalid => true
  | .refuted => true
  | .malformed => true
  | .superseded => true

/-- Only a sealed, unresolved candidate is a live promotion task. -/
def isPromotable : CandidateStatus → Bool
  | .sealedUnverified => true
  | _ => false

/-- Only `certified` may contribute a trusted edge to the certified graph. -/
def isCertified : CandidateStatus → Bool
  | .certified => true
  | _ => false

end CandidateStatus

/-- Provenance fixed at seal time and never mutated (Spec §8.3, §8.8).

    `sealHash` is the sha256 of the exact printed target type, produced by
    `scripts/crrg-seal`. Lean cannot compute it (it has no access to its own
    pretty-printed output as data), so the hash is the *tooling* half of the
    immutability guarantee and the type parameter on `SealedCandidate` is the
    *kernel* half. Together they catch both in-place weakening of the
    proposition and redefinition of the underlying declaration. -/
structure SealRecord where
  /-- Candidate identifier, e.g. `"E17"`. Unique and never reused. -/
  id : String
  /-- Identifiers of the graph nodes this candidate consumes. -/
  sourceIds : List String
  /-- Identifier of the graph node this candidate discharges. -/
  targetId : String
  /-- Name the promoting theorem must be given. -/
  expectedTheoremName : String
  /-- sha256 of the exact printed target type, from `scripts/crrg-seal`. -/
  sealHash : String
  /-- Repository commit the seal was taken against. -/
  sourceCommit : String
  /-- Creation timestamp, ISO-8601. Supplied by tooling. -/
  createdAt : String
  deriving Repr, DecidableEq

/-- A draft candidate (Spec §8.4, DRAFT).

    Freely editable. Carries no graph status and no reward. The target
    proposition is an ordinary field here, precisely because a draft *may* still
    change; sealing moves it into the type. -/
structure DraftCandidate where
  id : String
  sourceIds : List String
  targetId : String
  expectedTheoremName : String
  targetProp : Prop

/-- A sealed candidate (Spec §8.4, SEALED_UNVERIFIED).

    The target proposition is a **type parameter**, not a field. This is what
    makes §8.5 enforceable rather than advisory: a `SealedCandidate P` can never
    become a `SealedCandidate Q`, so "refactoring the target into an easier
    statement and reporting a promotion" is not a mutation, it is a different
    type, and the seal record's `id` and `sealHash` will not match. -/
structure SealedCandidate (targetProp : Prop) where
  record : SealRecord

/-- Seal a draft, fixing its exact proposition for the attempt.

    The proposition travels from the draft's field into the result's type index,
    which is the moment it becomes immutable. -/
def DraftCandidate.seal (d : DraftCandidate) (sealHash sourceCommit createdAt : String) :
    SealedCandidate d.targetProp :=
  { record :=
      { id := d.id
        sourceIds := d.sourceIds
        targetId := d.targetId
        expectedTheoremName := d.expectedTheoremName
        sealHash := sealHash
        sourceCommit := sourceCommit
        createdAt := createdAt } }

/-- How a sealed candidate was resolved (Spec §8.4, terminal states).

    `certified` and `refuted` are kernel-checked: they carry a proof and a
    disproof of the exact sealed proposition respectively. `invalid`,
    `malformed` and `superseded` are research judgements and carry a reason
    string instead — they are honest *non*-claims, and CRRG never treats them as
    evidence about `P`. -/
inductive Outcome (P : Prop)
  /-- A theorem inhabits the exact sealed proposition. -/
  | certified (proof : P) (theoremSha : String)
  /-- The proposition is false, with a disproof. -/
  | refuted (disproof : ¬ P) (reason : String)
  /-- The intended route is contradicted, without a formal disproof. -/
  | invalid (reason : String)
  /-- Type-correct but not the intended composition, e.g. a premise was omitted. -/
  | malformed (reason : String)
  /-- Replaced by a different sealed candidate, whose id is recorded. -/
  | superseded (bySealId : String) (reason : String)

namespace Outcome

variable {P : Prop}

/-- The status this outcome renders as. Derived, never stored. -/
def status : Outcome P → CandidateStatus
  | .certified _ _ => .certified
  | .refuted _ _ => .refuted
  | .invalid _ => .invalid
  | .malformed _ => .malformed
  | .superseded _ _ => .superseded

/-- Every outcome is terminal. There are no transitions out of a resolution;
    a changed target requires a new candidate id (§8.5). -/
theorem status_isTerminal (o : Outcome P) : o.status.isTerminal = true := by
  cases o <;> rfl

/-- A resolved candidate is never promotable. This is the property that was
    missing when status was a mutable field: previously a value could be marked
    refuted and then promoted anyway. -/
theorem status_not_promotable (o : Outcome P) : o.status.isPromotable = false := by
  cases o <;> rfl

/-- Extract the proof from a certified outcome. The only way to obtain a proof
    of the sealed proposition from an outcome, and it exists only for
    `certified`. -/
def proofOf? : (o : Outcome P) → Option (PLift P)
  | .certified h _ => some ⟨h⟩
  | _ => none

/-- A certified outcome yields a proof of the exact sealed proposition. -/
theorem certified_sound (o : Outcome P) (h : o.status = .certified) : P := by
  cases o with
  | certified proof _ => exact proof
  | _ => simp [status] at h

end Outcome

/-- A sealed candidate together with its resolution (Spec §8.8, history).

    Both halves are retained forever: the exact proposition (in the type), the
    seal provenance (in `sealed.record`), and the final status with its reason
    (in `outcome`). Nothing is deleted when a candidate fails. -/
structure ResolvedCandidate (P : Prop) where
  sealed : SealedCandidate P
  outcome : Outcome P

namespace ResolvedCandidate

variable {P : Prop}

/-- Rendered status of a resolved candidate. -/
def status (r : ResolvedCandidate P) : CandidateStatus := r.outcome.status

/-- A certified resolution really does prove the sealed proposition. -/
theorem certified_sound (r : ResolvedCandidate P) (h : r.status = .certified) : P :=
  r.outcome.certified_sound h

/-- A resolved candidate is never a live promotion task. -/
theorem not_promotable (r : ResolvedCandidate P) : r.status.isPromotable = false :=
  r.outcome.status_not_promotable

end ResolvedCandidate

namespace SealedCandidate

variable {P : Prop}

/-- Promote: resolve a sealed candidate with a proof of its **exact** target.

    There is no other way to reach `certified`. In particular there is no
    transition from any terminal outcome back into this one, so a refuted or
    superseded candidate cannot be promoted. -/
def promote (c : SealedCandidate P) (proof : P) (theoremSha : String) :
    ResolvedCandidate P :=
  ⟨c, .certified proof theoremSha⟩

/-- Refute: resolve with a disproof of the exact target.

    A claimed refutation must be backed by `¬ P`; "I believe this is false" is
    `markInvalid`, not `refute`. -/
def refute (c : SealedCandidate P) (disproof : ¬ P) (reason : String) :
    ResolvedCandidate P :=
  ⟨c, .refuted disproof reason⟩

/-- Mark the intended mathematical route contradicted, without a formal
    disproof of the proposition itself. -/
def markInvalid (c : SealedCandidate P) (reason : String) : ResolvedCandidate P :=
  ⟨c, .invalid reason⟩

/-- Mark type-correct but not the intended composition — e.g. a needed premise
    was omitted or a quantifier is wrong (§8.4). Highly informative: it proves
    the research blueprint was missing a real obligation (§8.6). -/
def markMalformed (c : SealedCandidate P) (reason : String) : ResolvedCandidate P :=
  ⟨c, .malformed reason⟩

/-- Supersede by a different sealed candidate. The old exact target survives in
    this record's type; the replacement must carry a new id (§8.5). -/
def supersede (c : SealedCandidate P) (bySealId reason : String) : ResolvedCandidate P :=
  ⟨c, .superseded bySealId reason⟩

/-- The status of a sealed but unresolved candidate. -/
def status (_c : SealedCandidate P) : CandidateStatus := .sealedUnverified

/-- A sealed, unresolved candidate is exactly the promotable state. This is the
    state that was previously unreachable: nothing in the old API constructed a
    candidate with `sealedUnverified` status, so `isPromotable` was dead code. -/
theorem status_isPromotable (c : SealedCandidate P) : c.status.isPromotable = true := rfl

/-- A sealed, unresolved candidate is not terminal. -/
theorem status_not_terminal (c : SealedCandidate P) : c.status.isTerminal = false := rfl

end SealedCandidate

/-- The promotion queue: sealed candidates that are not yet resolved (§8.7).

    Deliberately a *separate* type from anything in the certified graph. Its
    entries contribute zero trusted root closure; only a `Frontier` can close a
    root. -/
structure PromotionQueue where
  /-- Index type of the live promotion tasks. -/
  Task : Type
  /-- The exact sealed proposition of each task. -/
  target : Task → Prop
  /-- The seal provenance of each task. -/
  entry : (t : Task) → SealedCandidate (target t)

end CRRG
