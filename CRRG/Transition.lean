import CRRG.Frontier

/-!
# CRRG.Transition

First-class frontier transitions: an accepted research-state mutation is itself
a proof object, carrying source state, target state, and the preservation
witness that makes composition sound.

A `Transition source target` says only this: discharging every leaf of `target`
discharges every leaf of `source`. That is the whole semantics, and it is
deliberately the weakest statement that supports the chain

```text
F0 --T1--> F1 --T2--> ... --Tn--> Fn
```

whose kernel-produced composite `Transition F0 Fn` makes closing `Fn` entail the
original root through one certificate (`Transition.closeRoot`), instead of
re-deriving the entailment once per generation.

The definition is universe-polymorphic in *both* frontiers because the existing
operators change universe level: `splitLeaf` lands in `max u v`, so a transition
relating a frontier to its own split is necessarily heterogeneous.

Refutation is not a root-preserving transition and is deliberately absent here;
it remains its own proof-carrying fact.
-/

namespace CRRG

universe u v w

namespace Frontier

/-- Every live obligation of `F` is discharged. -/
abbrev AllClosed {root : Goal} (F : Frontier.{u} root) : Prop :=
  ∀ t, (F.leaf t).claim

/-- A certified research-state transition: closing `target` closes `source`.

    Universe-polymorphic in both frontiers; see the module header. -/
structure Transition {root : Goal}
    (source : Frontier.{u} root) (target : Frontier.{v} root) : Prop where
  preserve : target.AllClosed → source.AllClosed

namespace Transition

/-- Identity transition: a frontier transitions to itself. -/
theorem refl {root : Goal} (F : Frontier.{u} root) : Transition F F :=
  ⟨_root_.id⟩

/-- Composition of transitions, rootward.
    Three universe parameters: the middle frontier need not share a level with
    either end. -/
theorem comp {root : Goal} {F : Frontier.{u} root} {G : Frontier.{v} root}
    {H : Frontier.{w} root} (fg : Transition F G) (gh : Transition G H) :
    Transition F H :=
  ⟨fun h => fg.preserve (gh.preserve h)⟩

/-- **Root-closure transport.** Closing the target of a transition discharges
    the original root, through the *source* frontier's `closeRoot`. This is what
    makes a composite transition usable: the root obligation never has to be
    re-established at the far end of the chain. -/
theorem closeRoot {root : Goal} {source : Frontier.{u} root}
    {target : Frontier.{v} root} (T : Transition source target) :
    target.AllClosed → root.claim :=
  fun h => source.closeRoot (T.preserve h)

end Transition

/-! ### The transition induced by each frontier operator

Spec 20 requires every existing operator to expose or induce a transition
witness. Each `preserve` below mirrors that operator's own `closeRoot` body,
stopping one step short of applying `F.closeRoot` — which is precisely the
content that was previously locked inside the operator and unavailable as a
composable object. -/

/-- An `Edge` refinement of one leaf is a transition. -/
theorem refineLeaf_transition {root : Goal} (F : Frontier.{u} root)
    (dec : DecidableEq F.Task) (t₀ : F.Task) {child : Goal}
    (e : Edge (F.leaf t₀) child) :
    Transition F (F.refineLeaf dec t₀ e) :=
  ⟨fun h t =>
    @dite _ (t = t₀) (dec t t₀)
      (fun ht => ht ▸ e.discharge (by simpa [refineLeaf, ht] using h t))
      (fun ht => by simpa [refineLeaf, ht] using h t)⟩

/-- A `Split` refinement of one leaf is a transition. Note the universes: the
    target lives in `max u v`, which is why `Transition` may not identify the
    two frontier levels. -/
theorem splitLeaf_transition {root : Goal} (F : Frontier.{u} root)
    (dec : DecidableEq F.Task) (t₀ : F.Task) (s : Split.{v} (F.leaf t₀)) :
    Transition F (F.splitLeaf dec t₀ s) :=
  ⟨fun h t =>
    @dite _ (t = t₀) (dec t t₀)
      (fun ht => ht ▸ s.discharge (fun b => h (.inr b)))
      (fun ht => h (.inl ⟨t, ht⟩))⟩

/-- Retiring a proved leaf is a transition. The retired obligation is supplied
    by the proof the operator already demanded, not by the target frontier. -/
theorem retireLeaf_transition {root : Goal} (F : Frontier.{u} root)
    (dec : DecidableEq F.Task) (t₀ : F.Task) (proof : (F.leaf t₀).claim) :
    Transition F (F.retireLeaf dec t₀ proof) :=
  ⟨fun h t =>
    @dite _ (t = t₀) (dec t t₀)
      (fun ht => ht ▸ proof)
      (fun ht => h ⟨t, ht⟩)⟩

end Frontier

end CRRG
