import CRRG.Frontier
import CRRG.Candidate

/-!
# CRRG.Audit

Audit utilities: type-linking helpers and frontier introspection.
-/


namespace CRRG

/-- Assert that a frontier's root claim is exactly a given proposition.
    Used for type-linking the root to the Grand Challenge target. -/
def Frontier.rootIs {root : Goal} {P : Prop} (_front : Frontier root)
    (_h : root.claim = P) : True := True.intro

/-- Assert that a specific leaf's claim is exactly a given proposition.
    Used for type-linking task assignments. -/
def Frontier.leafIs {root : Goal} {P : Prop} (front : Frontier root)
    (t : front.Task) (_h : (front.leaf t).claim = P) : True := True.intro

/-- Verify that a sealed candidate's target proposition is exactly `Q`.

    Since sealing moves the proposition into the type, `SealedCandidate P` already
    pins it; this helper exists so a downstream pin file can assert the link to a
    *named* project declaration in the same style as `rootIs` and `leafIs`. -/
def SealedCandidate.targetIs {P Q : Prop} (_c : SealedCandidate P)
    (_h : P = Q) : True := True.intro

/-- Verify that a resolved candidate really is certified, and extract the proof
    of its exact sealed proposition. A promotion that does not type-check here
    is not a promotion. -/
def ResolvedCandidate.certifiedProof {P : Prop} (r : ResolvedCandidate P)
    (h : r.status = .certified) : P := r.certified_sound h

/-- A frontier with all leaves closed yields the root. -/
theorem Frontier.root_of_allClosed {root : Goal}
    (front : Frontier root)
    (h : ∀ t, (front.leaf t).Proved) : root.Proved :=
  front.closeRoot h

end CRRG
