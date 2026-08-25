import CRRG.Basic

/-!
# CRRG.Monotone

Quantitative partial progress (Spec §10.2).

CRRG's default reward is binary: a leaf is `OPEN` or `CLOSED`. Some node families
have a mathematically canonical parameter order, and for those the spec allows a
*local numerical* reward — but only under strict conditions:

> Each family should have an explicit monotonicity theorem stating which
> parameter direction is stronger. An agent assigned to such a family may
> receive local numerical reward only when it proves a strictly stronger
> parameter under the **same node semantics**.
>
> Never compare unrelated local currencies (e.g. "3 bits of moment slack" versus
> "one case eliminated") by a hand-chosen exchange rate.

Both conditions are structural here:

- the monotonicity theorem is a **field**, so a family cannot exist without it;
- `Progress` is indexed by the family, so progress in one family is not progress
  in another and there is no operation that combines them. There is deliberately
  no way to add, average, or exchange progress across families.
-/

namespace CRRG

universe u

/-- A monotone parameterized family of goals (§10.2).

    `Stronger a b` means "parameter `a` is at least as strong as `b`", so the
    claim at `a` implies the claim at `b`. `Stronger` is required to be a
    preorder: without reflexivity and transitivity, "strictly stronger" would not
    compose and chained improvements could not be certified.

    The `monotone` field is the spec's "explicit monotonicity theorem". It is a
    field rather than a side condition precisely so that declaring a family
    without proving it is impossible.

    `Param` is a **parameter**, not a field. A `Type`-valued field would have to
    be projected as `F.Param` at every use site, and projections of a plain `def`
    do not reduce during instance search — so numerals and `omega` would fail
    against `F.Param` even when the family is over `Nat`. Where a type field is
    the point of the abstraction (a `BadNode` *is* its witness type) that cost is
    unavoidable; here the parameter type is incidental, so it belongs in the
    signature. -/
structure MonotoneFamily (Param : Type u) where
  /-- `Stronger a b`: parameter `a` is at least as strong as parameter `b`. -/
  Stronger : Param → Param → Prop
  /-- The proposition asserted at each parameter. -/
  claim : Param → Prop
  /-- `Stronger` is reflexive. -/
  stronger_refl : ∀ p, Stronger p p
  /-- `Stronger` is transitive. -/
  stronger_trans : ∀ {a b c}, Stronger a b → Stronger b c → Stronger a c
  /-- **The monotonicity theorem.** A stronger parameter's claim implies a
      weaker parameter's claim. -/
  monotone : ∀ {a b}, Stronger a b → claim a → claim b

namespace MonotoneFamily

variable {Param : Type u} (F : MonotoneFamily Param)

/-- `a` is *strictly* stronger than `b`: at least as strong, and not conversely.

    Strictness is what makes a numerical reward meaningful. Re-proving an
    equally-strong parameter is not progress. -/
def StrictlyStronger (a b : Param) : Prop :=
  F.Stronger a b ∧ ¬ F.Stronger b a

/-- The goal asserted at a given parameter. -/
def goalAt (p : Param) : Goal := ⟨F.claim p⟩

/-- A stronger parameter's goal discharges a weaker parameter's goal.

    This is the family's monotonicity theorem viewed as a CRRG edge, with the
    usual rootward direction: solve the child (the stronger parameter) and the
    parent (the weaker one) is solved. -/
def edge {a b : Param} (h : F.Stronger a b) : Edge (F.goalAt b) (F.goalAt a) :=
  ⟨F.monotone h⟩

variable {F}

/-- Strict strength is irreflexive: nothing is strictly stronger than itself. -/
theorem strictlyStronger_irrefl (p : Param) : ¬ F.StrictlyStronger p p :=
  fun h => h.2 (F.stronger_refl p)

/-- Strict strength is transitive. -/
theorem strictlyStronger_trans {a b c : Param}
    (hab : F.StrictlyStronger a b) (hbc : F.StrictlyStronger b c) :
    F.StrictlyStronger a c :=
  ⟨F.stronger_trans hab.1 hbc.1, fun hca => hbc.2 (F.stronger_trans hca hab.1)⟩

/-- Strict strength is asymmetric. -/
theorem strictlyStronger_asymm {a b : Param}
    (h : F.StrictlyStronger a b) : ¬ F.StrictlyStronger b a :=
  fun h' => h.2 h'.1

end MonotoneFamily

/-- Certified quantitative progress within one family (§10.2).

    The **only** numerical reward CRRG recognises. It requires three things
    simultaneously: the same family `F` (so the node semantics are identical), a
    proof that the new parameter is *strictly* stronger, and a proof of the claim
    at the new parameter.

    Note what is absent: there is no constructor combining `Progress` in
    different families, and no numeric measure attached. That absence is the
    implementation of "never compare unrelated local currencies by a hand-chosen
    exchange rate". -/
structure Progress {Param : Type u} (F : MonotoneFamily Param) (old new : Param) where
  /-- The new parameter is strictly stronger than the old one. -/
  improvement : F.StrictlyStronger new old
  /-- The claim holds at the new parameter. -/
  proof : F.claim new

namespace Progress

variable {Param : Type u} {F : MonotoneFamily Param} {old new : Param}

/-- Progress never loses ground: a proof at a strictly stronger parameter still
    proves the old parameter's claim. This is the safety property that makes a
    numerical reward sound — an agent cannot be rewarded for an "improvement"
    that abandons what was already established. -/
theorem implies_old (p : Progress F old new) : F.claim old :=
  F.monotone p.improvement.1 p.proof

/-- Progress closes the old parameter's goal. -/
theorem closes_old_goal (p : Progress F old new) : (F.goalAt old).Proved :=
  p.implies_old

/-- Consecutive improvements compose into a single certified improvement. -/
def trans {mid : Param} (p : Progress F old mid) (q : Progress F mid new) :
    Progress F old new :=
  { improvement := MonotoneFamily.strictlyStronger_trans q.improvement p.improvement
    proof := q.proof }

/-- There is no such thing as progress from a parameter to itself. -/
theorem not_self (p : Progress F old old) : False :=
  MonotoneFamily.strictlyStronger_irrefl old p.improvement

end Progress

end CRRG
