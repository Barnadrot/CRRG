import CRRG.Basic

/-!
# CRRG.Debt

Composition debt in candidate targets (Spec §8.2).

A syntactically exact proposition can still hide the real research gap by
introducing extra hypotheses casually. The spec's example: describing an edge as

```text
H2 -> FpMomentBudget
```

while silently relying on `DimKerPsi4ResidualBound` and `LandedH2Count` as well.
The proposition `H2CompletionResult → FpMomentBudget` is perfectly well-typed;
it is simply not the obligation anyone can discharge.

§8.2 permits two honest encodings:

- **Shape A** — the exact proposition consumes every parent explicitly;
- **Shape B** — the entire unresolved source obligation is packaged into one
  bundle, which the target then consumes.

This module provides both, plus a proof that they are equivalent, so the choice
between them is presentational rather than semantic. What is forbidden — naming
some premises and quietly relying on others — is not expressible here: the
premise list is part of the record, and the target is *computed* from it.
-/

namespace CRRG

/-- The proposition `p₁ → p₂ → … → conclusion`.

    Building the target from the premise list is what removes the option of
    naming some premises and relying on others: there is no second place to put
    a hypothesis. -/
def chain : List Prop → Prop → Prop
  | [], concl => concl
  | p :: ps, concl => p → chain ps concl

/-- Every premise of a `chain` may be discharged to reach the conclusion. -/
theorem chain_apply : ∀ (ps : List Prop) (c : Prop), chain ps c → (∀ p ∈ ps, p) → c
  | [], _, h, _ => h
  | p :: ps, c, h, hall =>
      chain_apply ps c (h (hall p (List.mem_cons_self ..)))
        (fun q hq => hall q (List.mem_cons_of_mem _ hq))

/-- Conversely, anything that follows from all the premises is a `chain`. -/
theorem chain_intro : ∀ (ps : List Prop) (c : Prop), ((∀ p ∈ ps, p) → c) → chain ps c
  | [], _, h => h (fun _ hp => absurd hp (List.not_mem_nil))
  | p :: ps, c, h =>
      fun hp => chain_intro ps c (fun hrest =>
        h (fun q hq =>
          match List.mem_cons.mp hq with
          | .inl heq => heq ▸ hp
          | .inr hmem => hrest q hmem))

/-- A candidate edge's composition debt: the premises it actually consumes and
    the conclusion it actually reaches (§8.2, §8.3).

    The premise list is the machine-readable statement of what is still owed.
    An orchestrator can read it without parsing a proposition. -/
structure CompositionDebt where
  /-- Every premise the edge consumes. Nothing may be left implicit. -/
  premises : List Prop
  /-- What the edge establishes once every premise is discharged. -/
  conclusion : Prop

namespace CompositionDebt

/-- **Shape A** (§8.2): the exact target proposition, consuming every parent
    explicitly. -/
def shapeA (d : CompositionDebt) : Prop := chain d.premises d.conclusion

/-- **Shape B** (§8.2): the entire unresolved source obligation as one bundle. -/
structure Bundle (d : CompositionDebt) : Prop where
  /-- Every premise holds. -/
  holds : ∀ p ∈ d.premises, p

/-- **Shape B** target: the bundled obligation implies the conclusion. -/
def shapeB (d : CompositionDebt) : Prop := d.Bundle → d.conclusion

/-- The two honest encodings are equivalent. Choosing between them is a
    presentational decision, not a change of obligation — which is exactly what
    §8.2 means by "both are acceptable". -/
theorem shapeA_iff_shapeB (d : CompositionDebt) : d.shapeA ↔ d.shapeB :=
  ⟨fun h b => chain_apply d.premises d.conclusion h b.holds,
   fun h => chain_intro d.premises d.conclusion (fun hall => h ⟨hall⟩)⟩

/-- Discharging the debt: the target plus proofs of every premise yields the
    conclusion. This is the only way to consume a candidate edge, and it forces
    every premise to be accounted for. -/
theorem discharge (d : CompositionDebt) (target : d.shapeA)
    (hs : ∀ p ∈ d.premises, p) : d.conclusion :=
  chain_apply d.premises d.conclusion target hs

/-- The debt as a CRRG goal. -/
def goal (d : CompositionDebt) : Goal := ⟨d.shapeA⟩

/-- A debt with no premises is just its conclusion: there is nothing owed. -/
theorem shapeA_nil (c : Prop) : (CompositionDebt.mk [] c).shapeA = c := rfl

/-- Adding a premise strictly weakens what the edge asserts, which is the point:
    an edge that consumes more is claiming less. -/
theorem shapeA_cons (p : Prop) (ps : List Prop) (c : Prop) :
    (CompositionDebt.mk (p :: ps) c).shapeA = (p → (CompositionDebt.mk ps c).shapeA) := rfl

end CompositionDebt

end CRRG
