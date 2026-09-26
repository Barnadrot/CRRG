import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
def split : Split ((S0 (1 = 1) (2 = 2)).leafGoal ⟨0, Nat.zero_lt_one⟩) where
  children := [⟨1 = 1⟩, ⟨2 = 2⟩]
  discharge h := ⟨h ⟨1 = 1⟩ (by simp), h ⟨2 = 2⟩ (by simp)⟩
def move : Move (S0 (1 = 1) (2 = 2)) := Move.ofSplit _ ⟨0, Nat.zero_lt_one⟩ split
end Sub
