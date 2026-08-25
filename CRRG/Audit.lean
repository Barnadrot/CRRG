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

/-- Verify that a sealed candidate's target proposition is exactly `P`. -/
def SealedCandidate.targetIs {P : Prop} (c : SealedCandidate)
    (_h : c.targetProp = P) : True := True.intro

/-- A frontier with all leaves closed yields the root. -/
theorem Frontier.root_of_allClosed {root : Goal}
    (front : Frontier root)
    (h : ∀ t, (front.leaf t).Proved) : root.Proved :=
  front.closeRoot h

end CRRG
