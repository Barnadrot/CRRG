/-!
# CRRG.Basic

Core types for the Certified Research Reduction Graph:
`Goal`, `Edge`, and their basic operations.
-/

namespace CRRG

/-- A proposition-level research obligation. -/
structure Goal where
  claim : Prop

/-- The proposition that a goal's claim is inhabited. -/
abbrev Goal.Proved (G : Goal) : Prop := G.claim

/-- `child` is sufficient to discharge `parent`.
    Direction is rootward: proving `child.claim` yields `parent.claim`.

    The `: Prop` annotation is deliberate and load-bearing. Lean would infer it
    anyway from the single proof-valued field, but that inference is fragile:
    adding any data field later (a provenance string, an identifier) would
    silently move `Edge` into `Type`, changing the universe of every downstream
    signature that mentions it. Pinning it here turns that mistake into an
    immediate error. Edges carry no data by design — metadata belongs on the
    candidate record (§8.3), not on a certified edge. -/
structure Edge (parent child : Goal) : Prop where
  discharge : child.claim → parent.claim

namespace Edge

/-- Identity edge: a goal discharges itself. -/
def id (G : Goal) : Edge G G := ⟨_root_.id⟩

/-- Transitivity: compose edges rootward.
    If `C` discharges `B` and `B` discharges `A`, then `C` discharges `A`. -/
def trans {A B C : Goal} (ab : Edge A B) (bc : Edge B C) : Edge A C :=
  ⟨fun hC => ab.discharge (bc.discharge hC)⟩

/-- Compose two edges in leaf-to-root order. -/
def comp {A B C : Goal} (bc : Edge B C) (ab : Edge A B) : Edge A C :=
  ab.trans bc

end Edge

end CRRG
