import CRRGCore

/-!
# Several certificates under guarded composition

Each per-certificate lemma of a proof lane is modelled as a **guarded edge**: under its guard (the
lemma's stated hypotheses, instantiated), the certificate bills its piece. A join packs several
bills into an aggregate. We ask, failure by failure, whether `guardedComp` turns a recorded failure
into a *type error*: a guard that cannot be discharged.

**Caveat (kept explicit).** CWSS and ArkLib's guarded CWSS are about extraction and knowledge
soundness; a lane of counting lemmas is not. The correspondence is structural (a per-component
guarantee is only valid inside its guard, and gluing must carry every guard), not a theorem
transfer.

The generic shape comes first. The instance at the end is a **synthetic example**: squaring is
monotone only on nonnegative numbers. What the kernel checks is the *shape* of the failure: the
guard that the join needed is false on the instance, so no unguarded edge exists, and the escape
leaf is exactly the unbilled obligation.
-/

namespace CRRGExamples.Lane

open CRRGCore

/-! ## The generic shape -/

/-- A per-certificate lemma: under `guard`, the piece's `bill` holds. -/
structure Cert where
  guard : Prop
  bill : Prop
  sound : guard → bill

/-- A certificate is a guarded edge from its bill to nothing further (its proof is on paper). -/
def Cert.edge (c : Cert) : GuardedEdge ⟨c.bill⟩ ⟨True⟩ c.guard := ⟨fun h _ => c.sound h⟩

/-- Two certificates glued: both guards, both bills. -/
def Cert.and (c₁ c₂ : Cert) : Cert where
  guard := c₁.guard ∧ c₂.guard
  bill := c₁.bill ∧ c₂.bill
  sound h := ⟨c₁.sound h.1, c₂.sound h.2⟩

/-- **Type error, generic form.** On an instance where the bill is false, no *unguarded* edge
from the bill exists, whatever the certificate: the lemma cannot be used without its guard. -/
theorem no_unguarded_edge {bill : Prop} (hb : ¬ bill) : ¬ Edge ⟨bill⟩ ⟨True⟩ :=
  fun e => hb (e.discharge trivial)

/-- **The escape leaf is the unbilled obligation.** Joining an aggregate `A ⇐[gate] ⟨bill⟩` with a
certificate `⟨bill⟩ ⇐[g] True` keeps the leaf `gate ∧ ¬ g → bill`. On an instance where the gate
holds, the certificate's guard fails and the bill is false, that leaf is false: the composite split
**cannot be closed**. The join cannot silently absorb the failure. -/
theorem join_stuck {A : Goal} {gate g bill : Prop} [Decidable gate] [Decidable g]
    (e₁ : GuardedEdge A ⟨bill⟩ gate) (e₂ : GuardedEdge ⟨bill⟩ ⟨True⟩ g)
    (hgate : gate) (hg : ¬ g) (hb : ¬ bill) :
    ¬ ∀ c ∈ (guardedComp e₁ e₂).children, c.claim := by
  intro h
  have hleaf : gate ∧ ¬ g → bill := h ⟨gate ∧ ¬ g → bill⟩ (by simp [guardedComp])
  exact hb (hleaf ⟨hgate, hg⟩)

/-- Conversely, where the guard holds, the certificate discharges its bill. -/
theorem join_pass {gate g bill : Prop} (c : Cert) (hc : c.guard = g) (hbill : c.bill = bill)
    (_ : gate) (hg : g) : bill := by
  subst hc hbill; exact c.sound hg

/-- **Separate witnesses are not a joint witness.** A guard of the form `(∃ x, P x) ∧ (∃ x, Q x)`
never discharges `∃ x, P x ∧ Q x`. Here `P = (· = 0)` and `Q = (· = 1)`: both exist, and no joint
witness does. This is why a joint guard field must be discharged by one witness (the runner's
`GUARD_JOINT_SPLIT`). -/
theorem separate_witnesses_not_joint :
    ¬ (((∃ x : Nat, x = 0) ∧ (∃ x : Nat, x = 1)) → ∃ x : Nat, x = 0 ∧ x = 1) := by
  intro h
  obtain ⟨x, h0, h1⟩ := h ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩
  omega

/-! ## Synthetic example: a sign guard

"If `b ≤ a` then `b * b ≤ a * a`" holds only under the guard `0 ≤ b`. Read without the guard, it
fails at `(a, b) = (1, -3)`, where `9 ≤ 1` is false. -/

section Sign

/-- The certificate: under `0 ≤ b ∧ b ≤ a`, the bill `b * b ≤ a * a` holds. -/
def sqCert (a b : Int) : Cert where
  guard := 0 ≤ b ∧ b ≤ a
  bill := b * b ≤ a * a
  sound h := Int.mul_le_mul h.2 h.2 h.1 (Int.le_trans h.1 h.2)

instance (a b : Int) : Decidable (sqCert a b).guard :=
  inferInstanceAs (Decidable (0 ≤ b ∧ b ≤ a))

/-- *computed*: the bill is false on the instance… -/
theorem sq_bill_false : ¬ ((-3 : Int) * -3 ≤ 1 * 1) := by decide

/-- …and so is the guard. -/
theorem sq_guard_false : ¬ (0 ≤ (-3 : Int) ∧ (-3 : Int) ≤ 1) := by decide

/-- **Type error**: the unguarded edge does not exist on this instance. -/
example : ¬ Edge ⟨(-3 : Int) * -3 ≤ 1 * 1⟩ ⟨True⟩ := no_unguarded_edge sq_bill_false

/-- An aggregate whose gate (`True`) always holds and which needs exactly the certificate's bill. -/
def sqAggregate : GuardedEdge ⟨(sqCert 1 (-3)).bill⟩ ⟨(sqCert 1 (-3)).bill⟩ True :=
  ⟨fun _ h => h⟩

/-- **The join is stuck**: composing the aggregate with the certificate keeps the escape leaf
`True ∧ ¬ guard → bill`, which is false here, so the composite split cannot be closed. -/
example : ¬ ∀ c ∈ (guardedComp sqAggregate (sqCert 1 (-3)).edge).children, c.claim :=
  join_stuck sqAggregate (sqCert 1 (-3)).edge trivial sq_guard_false sq_bill_false

/-- Where the guard holds, the certificate discharges its bill. -/
example : (2 : Int) * 2 ≤ 5 * 5 := (sqCert 5 2).sound (by decide)

end Sign

end CRRGExamples.Lane
