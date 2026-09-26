import CRRGClassical.Family

/-!
# CRRGClassical.Route — the classical frontier and `CertRoute`

The frontier invariant has no dependence on the label order: `Frontier.closeRoot`,
`State.commit_transition` and `CertRoute` port unchanged. They are re-stated here on the
classical side. So a **classical route certificate** is `CRRGClassical.CertRoute.closes`, an ordinary
classical Lean proof of `Capstone d`, and the credit side of the same states is Mathlib's
Dershowitz–Manna order (`runner_credit_sound`, `easierSucc_wf_classical`).
-/

namespace CRRGClassical

open CRRGCore

/-- The classical route type: a state whose root is `Capstone d`. -/
abbrev CertRoute (Capstone : ℕ → Prop) (d : ℕ) := CRRGCore.CertRoute Capstone d

/-- *proved*: **a classical route certificate.** Closing the route's frontier proves the capstone at
`d`, and nothing else. -/
theorem CertRoute.closes {Capstone : ℕ → Prop} {d : ℕ} (R : CertRoute Capstone d)
    (h : R.frontier.AllClosed) : Capstone d :=
  R.frontier.closeRoot h

/-- *proved*: the frontier invariant: all leaves closed gives the root. -/
theorem closeRoot {root : Goal} (S : State root) (h : S.frontier.AllClosed) : root.claim :=
  S.frontier.closeRoot h

/-- *proved*: every accepted commit is a transition of the frontier. -/
theorem commit_transition {root : Goal} (S S' : State root) (m : Move S) (t : Tag)
    (h : State.commit S m = .ok (S', t)) : Transition S.frontier S'.frontier :=
  State.commit_transition S S' m t h

/-- *proved*: `AllClosed` read through the registry (as in the core). -/
theorem allClosed_iff {root : Goal} (S : State root) :
    S.frontier.AllClosed ↔ ∀ k ∈ S.leaves, holds S.reg k :=
  State.allClosed_iff S

end CRRGClassical
