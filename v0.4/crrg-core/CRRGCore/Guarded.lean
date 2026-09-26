import CRRGCore.Basic

/-!
# CRRGCore.Guarded — guarded composition, escapes, and no hidden composition debt

Foundation: **CWSS and ArkLib's guarded CWSS**. Coordinate-wise special soundness is Fenzi,
Moghaddas and Nguyen's (J. Cryptology 2024). The guarded variant is ArkLib's Lean implementation
(`OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean`). There:
* a guarded verifier is `if check then pure out else failure`;
* packages compose only along an exact seam (`hseam : L₁.relOut = L₂.relIn := by rfl`);
* the composite check is the conjunction of the two checks.

Restated for research obligations:
* **Exact seam.** Edges and splits compose only through the *same* middle `Goal`.
* **No dropped guard.** A guarded reduction commits both a pass leaf and an **escape leaf**
  (`GuardedEdge.toSplit`).
* **Escapes survive composition** (`guardedComp`).
* **No hidden composition debt.** A conditional result is admitted only as an explicit split whose
  premises are open leaves (`conditionalSplit`). A refinement that needs a hidden premise has no
  witness (`hidden_debt_not_edge`).

Kept from CRRG v0.10 with the same meaning: `BadNode`, `WitnessMap`, `GuardedMap`, `EscapeMap`
(`CRRG/Witness.lean`, `Guarded.lean`, `Escape.lean`) and the premise-list encoding of
composition debt (`CRRG/Debt.lean`).
-/

namespace CRRGCore

/-! ## Witness-level nodes (counterexample form) -/

/-- A counterexample node: closed when its witness type is empty. -/
structure BadNode where
  Witness : Type

def BadNode.Closed (N : BadNode) : Prop := N.Witness → False

/-- The goal "this node is closed". -/
def BadNode.goal (N : BadNode) : Goal := ⟨N.Closed⟩

/-- Parent counterexamples map into child counterexamples; closing the child closes the parent.
This is Abadi–Lamport's R2 between two zero-step specifications. -/
structure WitnessMap (parent child : BadNode) where
  map : parent.Witness → child.Witness

def WitnessMap.toEdge {parent child : BadNode} (m : WitnessMap parent child) :
    Edge parent.goal child.goal :=
  ⟨fun hc w => hc (m.map w)⟩

/-- A guarded transformation: the guard partitions parent witnesses, and both branches must be
handled. -/
structure GuardedMap (parent pass fail : BadNode) where
  guard : parent.Witness → Bool
  onPass : (w : parent.Witness) → guard w = true → pass.Witness
  onFail : (w : parent.Witness) → guard w = false → fail.Witness

/-- A guarded map commits **both** branches as leaves. -/
def GuardedMap.toSplit {parent pass fail : BadNode} (g : GuardedMap parent pass fail) :
    Split parent.goal where
  children := [pass.goal, fail.goal]
  discharge h w := by
    have hp : pass.Closed := h pass.goal (by simp)
    have hf : fail.Closed := h fail.goal (by simp)
    cases hg : g.guard w with
    | true => exact hp (g.onPass w hg)
    | false => exact hf (g.onFail w hg)

/-- An escape map: every parent witness is a main-branch or an escape-branch witness. -/
structure EscapeMap (parent main escape : BadNode) where
  classify : parent.Witness → main.Witness ⊕ escape.Witness

/-- The escape branch cannot be dropped: both branches are committed as leaves. -/
def EscapeMap.toSplit {parent main escape : BadNode} (e : EscapeMap parent main escape) :
    Split parent.goal where
  children := [main.goal, escape.goal]
  discharge h w := by
    have hm : main.Closed := h main.goal (by simp)
    have he : escape.Closed := h escape.goal (by simp)
    cases hc : e.classify w with
    | inl m => exact hm m
    | inr x => exact he x

/-! ## Guarded reductions of propositions -/

/-- A reduction of `parent` to `child` valid only under the guard `g`. -/
structure GuardedEdge (parent child : Goal) (g : Prop) where
  onPass : g → child.claim → parent.claim

/-- The pass leaf and the escape leaf of a guarded edge. -/
def GuardedEdge.passLeaf (child : Goal) (g : Prop) : Goal := ⟨g → child.claim⟩
def GuardedEdge.escapeLeaf (parent : Goal) (g : Prop) : Goal := ⟨¬ g → parent.claim⟩

/-- A guarded reduction commits the pass leaf `g → child` **and** the escape leaf `¬g → parent`. -/
def GuardedEdge.toSplit {parent child : Goal} {g : Prop} [Decidable g]
    (e : GuardedEdge parent child g) : Split parent where
  children := [GuardedEdge.passLeaf child g, GuardedEdge.escapeLeaf parent g]
  discharge h := by
    have hpass : g → child.claim := h (GuardedEdge.passLeaf child g) (by simp)
    have hfail : ¬ g → parent.claim := h (GuardedEdge.escapeLeaf parent g) (by simp)
    by_cases hg : g
    · exact e.onPass hg (hpass hg)
    · exact hfail hg

theorem GuardedEdge.escape_mem {parent child : Goal} {g : Prop} [Decidable g]
    (e : GuardedEdge parent child g) :
    GuardedEdge.escapeLeaf parent g ∈ e.toSplit.children := by
  simp [GuardedEdge.toSplit]

/-- **Guarded composition.** Composing `A ⇐[g₁] B` with `B ⇐[g₂] C` keeps both escape leaves, each
in the context where it arises. The composite guard is `g₁ ∧ g₂`, mirroring ArkLib's composite
check `check₁ && check₂`. -/
def guardedComp {A B C : Goal} {g₁ g₂ : Prop} [Decidable g₁] [Decidable g₂]
    (_e₁ : GuardedEdge A B g₁) (_e₂ : GuardedEdge B C g₂) : Split A where
  children := [⟨g₁ ∧ g₂ → C.claim⟩, ⟨¬ g₁ → A.claim⟩, ⟨g₁ ∧ ¬ g₂ → B.claim⟩]
  discharge h := by
    have hC : g₁ ∧ g₂ → C.claim := h ⟨g₁ ∧ g₂ → C.claim⟩ (by simp)
    have hA : ¬ g₁ → A.claim := h ⟨¬ g₁ → A.claim⟩ (by simp)
    have hB : g₁ ∧ ¬ g₂ → B.claim := h ⟨g₁ ∧ ¬ g₂ → B.claim⟩ (by simp)
    by_cases h₁ : g₁
    · apply _e₁.onPass h₁
      by_cases h₂ : g₂
      · exact _e₂.onPass h₂ (hC ⟨h₁, h₂⟩)
      · exact hB ⟨h₁, h₂⟩
    · exact hA h₁

/-- Both escape leaves survive composition. -/
theorem guardedComp_escapes {A B C : Goal} {g₁ g₂ : Prop} [Decidable g₁] [Decidable g₂]
    (e₁ : GuardedEdge A B g₁) (e₂ : GuardedEdge B C g₂) :
    (⟨¬ g₁ → A.claim⟩ : Goal) ∈ (guardedComp e₁ e₂).children ∧
      (⟨g₁ ∧ ¬ g₂ → B.claim⟩ : Goal) ∈ (guardedComp e₁ e₂).children := by
  simp [guardedComp]

/-! ## No hidden composition debt -/

/-- A conditional result `A₁ → … → Aₙ → P` enters only as a split whose premises are all open
leaves. -/
def conditionalSplit (P : Goal) (premises : List Goal)
    (target : (∀ a ∈ premises, a.claim) → P.claim) : Split P where
  children := premises
  discharge := target

/-- **A hidden premise cannot be turned into a refinement.** There is no uniform refinement of `P`
into `B` from `A ∧ B → P` alone: here `A := False`, `B := True`, `P := False`. -/
theorem hidden_debt_not_edge :
    ¬ ∀ (A B P : Prop), (A ∧ B → P) → Edge ⟨P⟩ ⟨B⟩ := by
  intro h
  exact (h False True False (fun ⟨a, _⟩ => a)).discharge trivial

/-- A proposed decomposition whose composition is not yet proved: the composition itself becomes
an open leaf, the **edge leaf**. This answers the two-pager's research question: the relation
need not be known beforehand. -/
def withEdgeLeaf (P : Goal) (children : List Goal) : Split P where
  children := ⟨(∀ c ∈ children, c.claim) → P.claim⟩ :: children
  discharge h := (h _ (List.mem_cons_self ..)) fun c hc => h c (List.mem_cons_of_mem _ hc)

/-! ## Partition moves (SMT-style search narrowing) -/

/-- A leaf quantified over a range `[a, b]` of naturals. -/
def rangeGoal (P : Nat → Prop) (a b : Nat) : Goal := ⟨∀ x, a ≤ x → x ≤ b → P x⟩

/-- Split a range at `m`: coverage is a case split on `x ≤ m`, checked by the kernel. -/
def rangeSplit (P : Nat → Prop) (a m b : Nat) : Split (rangeGoal P a b) where
  children := [rangeGoal P a m, rangeGoal P (m + 1) b]
  discharge h x hax hxb := by
    have h1 := h (rangeGoal P a m) (by simp)
    have h2 := h (rangeGoal P (m + 1) b) (by simp)
    by_cases hxm : x ≤ m
    · exact h1 x hax hxm
    · exact h2 x (by omega) hxb

/-- A split on a decidable predicate: the two cubes `c → P` and `¬c → P`. -/
def caseSplit (P : Goal) (c : Prop) [Decidable c] : Split P where
  children := [⟨c → P.claim⟩, ⟨¬ c → P.claim⟩]
  discharge h := by
    have h1 : c → P.claim := h ⟨c → P.claim⟩ (by simp)
    have h2 : ¬ c → P.claim := h ⟨¬ c → P.claim⟩ (by simp)
    by_cases hc : c
    · exact h1 hc
    · exact h2 hc

end CRRGCore
