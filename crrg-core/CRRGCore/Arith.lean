import CRRGCore.Easier

/-! M7: reflection of a closed integer-arithmetic fragment, not quantified arithmetic. -/
namespace CRRGCore.Arith

inductive Term where
  | lit (n : Int)
  | add (a b : Term)
  | mul (a b : Term)
  | emod (a : Term) (n : Int)
  deriving Repr

inductive Formula where
  | eq (a b : Term)
  | lt (a b : Term)
  | le (a b : Term)
  | and (p q : Formula)
  | or (p q : Formula)
  | not (p : Formula)
  deriving Repr

def Term.eval : Term → Int
  | .lit n => n
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval
  | .emod a n => a.eval % n

def Formula.Holds : Formula → Prop
  | .eq a b => a.eval = b.eval
  | .lt a b => a.eval < b.eval
  | .le a b => a.eval ≤ b.eval
  | .and p q => p.Holds ∧ q.Holds
  | .or p q => p.Holds ∨ q.Holds
  | .not p => ¬ p.Holds

def Formula.check : Formula → Bool
  | .eq a b => decide (a.eval = b.eval)
  | .lt a b => decide (a.eval < b.eval)
  | .le a b => decide (a.eval ≤ b.eval)
  | .and p q => p.check && q.check
  | .or p q => p.check || q.check
  | .not p => !p.check

theorem Formula.check_iff (φ : Formula) : φ.check = true ↔ φ.Holds := by
  induction φ with
  | eq a b => simp [check, Holds]
  | lt a b => simp [check, Holds]
  | le a b => simp [check, Holds]
  | and p q hp hq => simp [check, Holds, hp, hq]
  | or p q hp hq => simp [check, Holds, hp, hq]
  | not p hp => simp [check, Holds, ← hp]

def Formula.mechCert (φ : Formula) : MechCert ⟨φ.Holds⟩ where
  decide _ := φ.check
  sound_true h := (φ.check_iff).mp h
  sound_false h hφ := by rw [(φ.check_iff).mpr hφ] at h; cases h

end CRRGCore.Arith
