import CRRGCore.State

/-!
# CRRGCore.Route — the route's root is the capstone (refinement foundation, closes G7)

A route is a state whose root is `Capstone d`. In an application, `Capstone d` is the frozen target
statement at parameter `d`. The root is a *type index*, not a `True`-valued link helper, so closing
the route proves exactly the capstone at `d`. This is Abadi–Lamport's R1,
"the external statement is preserved", as a type. `CertRoute` takes the caller's `Capstone`, so an
application must bind it to its frozen statement; no seal comparison is implemented yet (STATUS G2, G7).
-/

namespace CRRGCore

/-- A route aimed at the capstone at radius `d`. -/
abbrev CertRoute (Capstone : Nat → Prop) (d : Nat) := State ⟨Capstone d⟩

/-- Closing the route's frontier proves the capstone at `d`, and nothing else. -/
theorem CertRoute.closes {Capstone : Nat → Prop} {d : Nat} (R : CertRoute Capstone d)
    (h : R.frontier.AllClosed) : Capstone d :=
  R.frontier.closeRoot h

/-- A refuted route root is a certified negative about the capstone itself. -/
theorem CertRoute.refuted {Capstone : Nat → Prop} {d : Nat} (R : CertRoute Capstone d)
    (h : R.rootRefuted = true) : ¬ Capstone d :=
  R.rootRefuted_sound h

end CRRGCore
