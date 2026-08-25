/-!
# Synthetic test: Candidate sealing and promotion

Tests the candidate lifecycle: DRAFT → SEALED_UNVERIFIED → CERTIFIED.
Verifies that promotion requires inhabiting the exact sealed proposition.
-/

import CRRG

open CRRG

private def draftCandidate : CandidateEdge where
  id := "E001"
  targetProp := 2 + 2 = 4
  status := .draft

example : draftCandidate.status = .draft := rfl
example : draftCandidate.status.isTerminal = false := rfl

-- Seal the candidate
private def sealed001 : SealedCandidate :=
  draftCandidate.seal rfl

example : sealed001.id = "E001" := rfl

-- Promote with exact proof
private def promoted001 : CandidateEdge :=
  sealed001.promote rfl

example : promoted001.status = .certified := rfl
example : promoted001.status.isTerminal = true := rfl
example : promoted001.id = "E001" := rfl

-- Supersede creates a new record preserving the old target
private def superseded001 : CandidateEdge :=
  sealed001.supersede

example : superseded001.status = .superseded := rfl
example : superseded001.id = "E001" := rfl

-- Malformed
private def malformed001 : CandidateEdge :=
  sealed001.markMalformed

example : malformed001.status = .malformed := rfl

-- Refuted
private def refuted001 : CandidateEdge :=
  sealed001.markRefuted

example : refuted001.status = .refuted := rfl
