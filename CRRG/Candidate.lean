/-!
# CRRG.Candidate

Typed candidate graph and promotion queue.
Candidates have exact Lean propositions; prose-only arrows are rejected.
-/

namespace CRRG

/-- Lifecycle status of a candidate edge. -/
inductive CandidateStatus
  | draft
  | sealedUnverified
  | certified
  | invalid
  | refuted
  | malformed
  | superseded
  deriving DecidableEq, Repr

namespace CandidateStatus

def isTerminal : CandidateStatus → Bool
  | .draft => false
  | .sealedUnverified => false
  | .certified => true
  | .invalid => true
  | .refuted => true
  | .malformed => true
  | .superseded => true

def isPromotable : CandidateStatus → Bool
  | .sealedUnverified => true
  | _ => false

end CandidateStatus

/-- A sealed candidate edge with an exact Lean proposition.
    The `targetProp` is the exact statement that must be inhabited
    for promotion. Once sealed, the target cannot be weakened in place. -/
structure SealedCandidate where
  id : String
  targetProp : Prop

/-- Evidence that a sealed candidate has been promoted: a proof
    inhabiting the exact sealed proposition. -/
structure Promotion (c : SealedCandidate) where
  proof : c.targetProp

/-- A candidate edge in the typed promotion queue.
    Links source goal(s) to a destination via an exact proposition. -/
structure CandidateEdge where
  id : String
  targetProp : Prop
  status : CandidateStatus

/-- Seal a draft candidate, fixing its exact proposition. -/
def CandidateEdge.seal (c : CandidateEdge) (_h : c.status = .draft) :
    SealedCandidate :=
  { id := c.id, targetProp := c.targetProp }

/-- Promote a sealed candidate by providing a proof of its exact proposition.
    Returns the original candidate updated to certified status. -/
def SealedCandidate.promote (c : SealedCandidate)
    (_proof : c.targetProp) : CandidateEdge :=
  { id := c.id
    targetProp := c.targetProp
    status := .certified }

/-- Mark a sealed candidate as superseded. The old target is preserved;
    a new candidate ID must be created for the replacement. -/
def SealedCandidate.supersede (c : SealedCandidate) : CandidateEdge :=
  { id := c.id
    targetProp := c.targetProp
    status := .superseded }

/-- Mark a sealed candidate as malformed. -/
def SealedCandidate.markMalformed (c : SealedCandidate) : CandidateEdge :=
  { id := c.id
    targetProp := c.targetProp
    status := .malformed }

/-- Mark a sealed candidate as refuted. -/
def SealedCandidate.markRefuted (c : SealedCandidate) : CandidateEdge :=
  { id := c.id
    targetProp := c.targetProp
    status := .refuted }

end CRRG
