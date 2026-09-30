import CRRGCore.Basic
import CRRGCore.Easier
import CRRGCore.Guarded

/-!
# CRRGCore.State — the committed research state: propose → verify → commit or reject

This module closes gaps G1 (commit step), G5 (negatives and backtracking), G8 (outcome
classification), G10 (accounting) and G12 (identity of repeated obligations); see `STATUS.md`.

* **Lineage by construction.** `State` has a private constructor. The only producers are
  `State.initial`, `State.commit`, `State.refute` and `State.learn`, so every state value is reached
  from the initial one by verified steps. No lineage script is needed.
* **Registry.** Obligations are registered once, append-only; an obligation's key is its index.
  Each entry carries its label and the certificate for that label.
* **Commit.** A `Move` replaces one leaf by a finite list of children, which are old keys or new
  entries, with a coverage certificate. `commit` returns `.error` or the new state plus a *computed*
  tag. `commit_transition` is the invariant theorem.
* **Negatives.** `refute` records a learned conflict, the key of a refuted obligation together with
  its disproof, then backtracks. `learn` propagates a conflict along a supplied implication. `commit`
  rejects any child whose key is a learned conflict, so a refuted obligation is never re-admitted.
* **Certified easier.** The tag is computed from labels, never asserted. `easierSucc_wf` proves
  that no infinite chain of certified-easier commits exists.
-/

namespace CRRGCore

/-! ## Labels with certificates -/

/-- What a label claims about its goal. A `sized` label must be an actual instance of an
owner-pinned family, with its pinned size. (Rung 2 has no label: it settles by evaluation and closes
the leaf; see `Move.closeByComputation`.) -/
def LabelOK (fams : List Family) (g : Goal) : Label → Prop
  | .top => True
  | .sized f n => ∃ hf : f < fams.length, ∃ q : (fams[f]'hf).Idx,
      g = ⟨(fams[f]'hf).claim q⟩ ∧ n = (fams[f]'hf).size q

/-- A registry entry: an obligation, its label, and the label's certificate. -/
structure Entry (fams : List Family) where
  goal : Goal
  label : Label
  ok : LabelOK fams goal label

/-- Key `k` holds: it is registered and its goal is proved. A missing key never holds. -/
def holds {fams : List Family} (reg : List (Entry fams)) (k : Nat) : Prop :=
  ∃ e, reg[k]? = some e ∧ e.goal.claim

theorem holds_append {fams : List Family} {reg ext : List (Entry fams)} {k : Nat}
    (hk : k < reg.length) : holds (reg ++ ext) k ↔ holds reg k := by
  simp [holds, List.getElem?_append_left hk]

theorem holds_iff {fams : List Family} {reg : List (Entry fams)} {k : Nat} (hk : k < reg.length) :
    holds reg k ↔ (reg[k]'hk).goal.claim := by
  constructor
  · rintro ⟨e, he, hc⟩
    rw [List.getElem?_eq_getElem hk] at he
    cases he
    exact hc
  · intro h
    exact ⟨reg[k]'hk, List.getElem?_eq_getElem hk, h⟩

/-- The label of key `k` (`top` if absent). -/
def labelOf {fams : List Family} (reg : List (Entry fams)) (k : Nat) : Label :=
  match reg[k]? with
  | some e => e.label
  | none => .top

theorem labelOf_append {fams : List Family} {reg ext : List (Entry fams)} {k : Nat}
    (hk : k < reg.length) : labelOf (reg ++ ext) k = labelOf reg k := by
  simp [labelOf, List.getElem?_append_left hk]

/-! ## Children and their resolution -/

/-- A child of a proposed move: an already-registered obligation, or a new entry. -/
inductive Child (fams : List Family) where
  | old (key : Nat)
  | new (entry : Entry fams)

/-- What the child asserts, read in the registry at proposal time. -/
def Child.claim {fams : List Family} (reg : List (Entry fams)) : Child fams → Prop
  | .old k => holds reg k
  | .new e => e.goal.claim

/-- The child's label. -/
def Child.label {fams : List Family} (reg : List (Entry fams)) : Child fams → Label
  | .old k => labelOf reg k
  | .new e => e.label

/-- Old children must name registered keys. -/
def Child.valid {fams : List Family} (reg : List (Entry fams)) : Child fams → Bool
  | .old k => decide (k < reg.length)
  | .new _ => true

/-- Register the new children (appending, in order) and return their keys. -/
def resolve {fams : List Family} :
    List (Entry fams) → List (Child fams) → List (Entry fams) × List Nat
  | reg, [] => (reg, [])
  | reg, .old k :: cs => let r := resolve reg cs; (r.1, k :: r.2)
  | reg, .new e :: cs => let r := resolve (reg ++ [e]) cs; (r.1, reg.length :: r.2)

theorem resolve_prefix {fams : List Family} :
    ∀ (reg : List (Entry fams)) (cs : List (Child fams)),
      ∃ ext, (resolve reg cs).1 = reg ++ ext
  | reg, [] => ⟨[], by simp [resolve]⟩
  | reg, .old k :: cs => by
    obtain ⟨ext, h⟩ := resolve_prefix reg cs
    exact ⟨ext, by simp [resolve, h]⟩
  | reg, .new e :: cs => by
    obtain ⟨ext, h⟩ := resolve_prefix (reg ++ [e]) cs
    exact ⟨e :: ext, by simp [resolve, h]⟩

theorem resolve_length_le {fams : List Family} (reg : List (Entry fams)) (cs : List (Child fams)) :
    reg.length ≤ (resolve reg cs).1.length := by
  obtain ⟨ext, h⟩ := resolve_prefix reg cs
  rw [h, List.length_append]
  omega

/-- The keys are valid in the extended registry. -/
theorem resolve_keys_valid {fams : List Family} :
    ∀ (reg : List (Entry fams)) (cs : List (Child fams)),
      (∀ c ∈ cs, c.valid reg = true) → ∀ k ∈ (resolve reg cs).2, k < (resolve reg cs).1.length
  | reg, [], _ => by simp [resolve]
  | reg, .old k :: cs, hv => by
    intro j hj
    simp only [resolve, List.mem_cons] at hj
    rcases hj with rfl | hj
    · have hk := hv (.old j) (List.mem_cons_self ..)
      simp [Child.valid] at hk
      exact Nat.lt_of_lt_of_le hk (resolve_length_le reg cs)
    · exact resolve_keys_valid reg cs (fun c hc => hv c (List.mem_cons_of_mem _ hc)) j hj
  | reg, .new e :: cs, hv => by
    intro j hj
    simp only [resolve, List.mem_cons] at hj
    have hle := resolve_length_le (reg ++ [e]) cs
    rcases hj with rfl | hj
    · show reg.length < (resolve (reg ++ [e]) cs).1.length
      simp at hle; omega
    · refine resolve_keys_valid (reg ++ [e]) cs (fun c hc => ?_) j hj
      have := hv c (List.mem_cons_of_mem _ hc)
      cases c with
      | old k => simp [Child.valid] at this ⊢; omega
      | new _ => rfl

/-- Validity is preserved when the registry grows. -/
theorem Child.valid_mono {fams : List Family} {reg : List (Entry fams)} {e : Entry fams}
    {c : Child fams} (h : c.valid reg = true) : c.valid (reg ++ [e]) = true := by
  cases c with
  | old k => simp [Child.valid] at h ⊢; omega
  | new _ => rfl

/-- A child's claim does not change when the registry grows (for valid children). -/
theorem Child.claim_mono {fams : List Family} {reg : List (Entry fams)} {e : Entry fams}
    {c : Child fams} (h : c.valid reg = true) : c.claim (reg ++ [e]) ↔ c.claim reg := by
  cases c with
  | old k =>
    simp [Child.valid] at h
    exact holds_append h
  | new _ => exact Iff.rfl

/-- If every returned key holds in the extended registry, every child's claim holds. -/
theorem resolve_claims {fams : List Family} :
    ∀ (reg : List (Entry fams)) (cs : List (Child fams)),
      (∀ c ∈ cs, c.valid reg = true) →
      (∀ k ∈ (resolve reg cs).2, holds (resolve reg cs).1 k) → ∀ c ∈ cs, c.claim reg
  | reg, [], _, _ => by simp
  | reg, .old k :: cs, hv, hh => by
    intro c hc
    simp only [resolve] at hh
    have hk := hv (.old k) (List.mem_cons_self ..)
    simp [Child.valid] at hk
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨ext, hext⟩ := resolve_prefix reg cs
      have := hh k (List.mem_cons_self ..)
      rw [hext] at this
      exact (holds_append hk).mp this
    · exact resolve_claims reg cs (fun c hc => hv c (List.mem_cons_of_mem _ hc))
        (fun j hj => hh j (List.mem_cons_of_mem _ hj)) c hc
  | reg, .new e :: cs, hv, hh => by
    intro c hc
    simp only [resolve] at hh
    have hv' : ∀ c ∈ cs, c.valid (reg ++ [e]) = true :=
      fun c hc => Child.valid_mono (hv c (List.mem_cons_of_mem _ hc))
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨ext, hext⟩ := resolve_prefix (reg ++ [e]) cs
      have := hh reg.length (List.mem_cons_self ..)
      rw [hext] at this
      have hlt : reg.length < (reg ++ [e]).length := by simp
      rw [holds_append hlt, holds_iff hlt] at this
      simpa [Child.claim] using this
    · have := resolve_claims (reg ++ [e]) cs hv' (fun j hj => hh j (List.mem_cons_of_mem _ hj)) c hc
      exact (Child.claim_mono (hv c (List.mem_cons_of_mem _ hc))).mp this

/-- The labels of the returned keys, read in the extended registry, are the children's labels. -/
theorem resolve_labels {fams : List Family} :
    ∀ (reg : List (Entry fams)) (cs : List (Child fams)),
      (∀ c ∈ cs, c.valid reg = true) →
      (resolve reg cs).2.map (labelOf (resolve reg cs).1) = cs.map (Child.label reg)
  | reg, [], _ => by simp [resolve]
  | reg, .old k :: cs, hv => by
    have hk := hv (.old k) (List.mem_cons_self ..)
    simp [Child.valid] at hk
    obtain ⟨ext, hext⟩ := resolve_prefix reg cs
    have ih := resolve_labels reg cs (fun c hc => hv c (List.mem_cons_of_mem _ hc))
    simp only [resolve, List.map_cons, Child.label]
    rw [ih, hext, labelOf_append hk]
  | reg, .new e :: cs, hv => by
    have hv' : ∀ c ∈ cs, c.valid (reg ++ [e]) = true :=
      fun c hc => Child.valid_mono (hv c (List.mem_cons_of_mem _ hc))
    obtain ⟨ext, hext⟩ := resolve_prefix (reg ++ [e]) cs
    have ih := resolve_labels (reg ++ [e]) cs hv'
    simp only [resolve, List.map_cons, Child.label]
    have hlt : reg.length < (reg ++ [e]).length := by simp
    rw [ih, hext, labelOf_append hlt]
    have hmap : cs.map (Child.label (reg ++ [e])) = cs.map (Child.label reg) := by
      apply List.map_congr_left
      intro c hc
      have := hv c (List.mem_cons_of_mem _ hc)
      cases c with
      | old k =>
        simp [Child.valid] at this
        simp [Child.label, labelOf_append this]
      | new _ => rfl
    rw [hmap]
    simp [labelOf]

/-! ## The state -/

/-- A history snapshot: an earlier leaf list, still a sound frontier for the current registry. -/
def SnapshotOK {fams : List Family} (root : Goal) (reg : List (Entry fams)) (h : List Nat) : Prop :=
  (∀ k ∈ h, k < reg.length) ∧ ((∀ k ∈ h, holds reg k) → root.claim)

/-- Key 0 of the registry is the root. -/
def RootAt {fams : List Family} (reg : List (Entry fams)) (root : Goal) : Prop :=
  ∃ e, reg[0]? = some e ∧ e.goal = root

theorem RootAt.pos {fams : List Family} {reg : List (Entry fams)} {root : Goal}
    (h : RootAt reg root) : 0 < reg.length := by
  obtain ⟨e, he, _⟩ := h
  rcases hr : reg with _ | ⟨a, t⟩
  · rw [hr] at he; simp at he
  · simp

theorem RootAt.holds {fams : List Family} {reg : List (Entry fams)} {root : Goal}
    (h : RootAt reg root) : holds reg 0 ↔ root.claim := by
  obtain ⟨e, he, hg⟩ := h
  constructor
  · rintro ⟨e', he', hc⟩
    rw [he] at he'
    cases he'
    exact hg ▸ hc
  · intro hr
    exact ⟨e, he, hg ▸ hr⟩

theorem RootAt.append {fams : List Family} {reg ext : List (Entry fams)} {root : Goal}
    (h : RootAt reg root) : RootAt (reg ++ ext) root := by
  obtain ⟨e, he, hg⟩ := h
  exact ⟨e, by rw [List.getElem?_append_left (RootAt.pos ⟨e, he, hg⟩)]; exact he, hg⟩

/-- The certified research state for one root. The constructor is private: states are produced
only by `initial`, `commit`, `refute` and `learn`. -/
structure State (root : Goal) where
  private mk ::
  /-- owner-pinned families, fixed at `initial` -/
  fams : List Family
  /-- the append-only registry; the key of an obligation is its index -/
  reg : List (Entry fams)
  /-- the live frontier, as keys -/
  leaves : List Nat
  /-- learned conflicts: keys of refuted obligations -/
  conflicts : List Nat
  /-- earlier frontiers, most recent first -/
  history : List (List Nat)
  /-- commits tagged certified easier -/
  easierCount : Nat
  /-- all commits -/
  commitCount : Nat
  /-- the record: labels of the last credited frontier (record-low rule) -/
  record : List Label
  root_key : RootAt reg root
  leaves_valid : ∀ k ∈ leaves, k < reg.length
  conflicts_valid : ∀ k ∈ conflicts, k < reg.length
  conflicts_sound : ∀ k ∈ conflicts, ¬ holds reg k
  closeRoot : (∀ k ∈ leaves, holds reg k) → root.claim
  history_ok : ∀ h ∈ history, SnapshotOK root reg h

namespace State

variable {root : Goal}

/-- The initial state: the root is key 0 and the only leaf. The owner pins the families here, and a
measurable root is **born measured**: `rootLabel` with its `LabelOK` proof (review item 4).
Unmeasured roots use the default `top`. -/
def initial (root : Goal) (fams : List Family) (rootLabel : Label := .top)
    (hLabel : LabelOK fams root rootLabel := by trivial) : State root where
  fams := fams
  reg := [⟨root, rootLabel, hLabel⟩]
  leaves := [0]
  conflicts := []
  history := []
  easierCount := 0
  commitCount := 0
  record := [rootLabel]
  root_key := ⟨_, rfl, rfl⟩
  leaves_valid := by simp
  conflicts_valid := by simp
  conflicts_sound := by simp
  closeRoot h := by
    have := h 0 (List.mem_singleton.mpr rfl)
    exact (holds_iff (reg := [⟨root, rootLabel, hLabel⟩]) (by simp)).mp this
  history_ok := by simp

/-- The frontier view of a state: the leaves as goals. -/
def frontier (S : State root) : Frontier root where
  leaves := S.leaves.map fun k => ⟨holds S.reg k⟩
  closeRoot h := S.closeRoot fun k hk => h ⟨holds S.reg k⟩ (List.mem_map.mpr ⟨k, hk, rfl⟩)

theorem allClosed_iff (S : State root) :
    S.frontier.AllClosed ↔ ∀ k ∈ S.leaves, holds S.reg k := by
  constructor
  · intro h k hk
    exact h ⟨holds S.reg k⟩ (List.mem_map.mpr ⟨k, hk, rfl⟩)
  · intro h g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
    exact h k hk

/-- The goal registered at leaf position `i`. -/
def leafGoal (S : State root) (i : Fin S.leaves.length) : Goal :=
  (S.reg[S.leaves[i]]'(S.leaves_valid _ (List.getElem_mem _))).goal

/-- The labels of the live leaves, in order. -/
def leafLabels (S : State root) : List Label := S.leaves.map (labelOf S.reg)

/-- Is the root refuted? -/
def rootRefuted (S : State root) : Bool := S.conflicts.contains 0

theorem rootRefuted_sound (S : State root) (h : S.rootRefuted = true) : ¬ root.claim := by
  intro hr
  have hmem : 0 ∈ S.conflicts := by simpa [rootRefuted] using h
  exact S.conflicts_sound 0 hmem ((S.root_key.holds).mpr hr)

/-- The learned conflicts with their claims (for the admission-time restatement check, D1). -/
def conflictClaims (S : State root) : List (Nat × Prop) :=
  S.conflicts.filterMap fun k => (S.reg[k]?).map fun e => (k, e.goal.claim)

/-- The claims of all registered obligations, with their keys (for key reuse at admission). -/
def registeredClaims (S : State root) : List (Nat × Prop) :=
  (List.range S.reg.length).filterMap fun k => (S.reg[k]?).map fun e => (k, e.goal.claim)

end State

/-! ## Moves and commit -/

/-- A proposed move: replace leaf `pos` by `children`, with the coverage certificate stated
against the registered goal of that leaf. -/
structure Move {root : Goal} (S : State root) where
  pos : Fin S.leaves.length
  children : List (Child S.fams)
  cover : (∀ c ∈ children, c.claim S.reg) → (S.leafGoal pos).claim
  /-- optional kernel proof that the new frontier's labels are DM-below the record -/
  recordCert : Option (PLift (DMLt (replaceList S.leafLabels pos
    (children.map (Child.label S.reg))) S.record)) := none

/-- Why a proposed move is rejected. -/
inductive Reject where
  /-- an old child names an unregistered key -/
  | unregisteredKey
  /-- a child is a learned conflict (a refuted obligation, or one implying it) -/
  | learnedConflict (key : Nat)
  /-- the route's root is refuted: the route is dead, and no move is admitted (review item 6) -/
  | rootRefuted
  deriving Repr, DecidableEq

/-- The computed tag of an accepted commit. -/
inductive Tag where
  /-- every child label is strictly below the replaced leaf's label (a closure has no children) -/
  | certifiedEasier
  /-- sound, but not certified easier -/
  | notCertifiedEasier
  deriving Repr, DecidableEq

namespace State

variable {root : Goal}

/-- The frontier's labels after the move (position `pos` replaced by the children's labels). -/
def newLabels (S : State root) (m : Move S) : List Label :=
  replaceList S.leafLabels m.pos (m.children.map (Child.label S.reg))

/-- The local test: every child label is strictly below the replaced leaf's label. -/
def localEasier (S : State root) (m : Move S) : Bool :=
  (m.children.map (Child.label S.reg)).all (fun l => l.ltb (labelOf S.reg S.leaves[m.pos]))

/-- **The credit rule (record-low).** A commit is certified easier only if the new frontier's labels
are strictly below the **record**, the labels of the last credited frontier, in the
Dershowitz–Manna order. Either:
* the frontier is still the record and the move is a local decrease (computed), or
* the proposer supplies a kernel proof `recordCert` of the DM decrease against the record.

Since the record is below every earlier credited frontier, this is "below every frontier the route
has been credited for". Growing and then shrinking back earns nothing (the record-low rule).
The tag is computed; it is never asserted. -/
def creditOf (S : State root) (m : Move S) : Tag :=
  if (S.localEasier m && decide (S.leafLabels = S.record)) || m.recordCert.isSome
  then .certifiedEasier else .notCertifiedEasier

theorem length_leafLabels (S : State root) : S.leafLabels.length = S.leaves.length := by
  simp [leafLabels]

/-- **The credit rule is sound**: a credited move's new labels are DM-below the record. -/
theorem creditOf_sound (S : State root) (m : Move S) (h : S.creditOf m = .certifiedEasier) :
    DMLt (S.newLabels m) S.record := by
  unfold creditOf at h
  split at h
  · rename_i hc
    rw [Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with ⟨hloc, heq⟩ | hcert
    · have heq : S.leafLabels = S.record := of_decide_eq_true heq
      rw [← heq]
      apply DMLt.of_step
      have hi : (m.pos : Nat) < S.leafLabels.length := by
        rw [length_leafLabels]; exact m.pos.isLt
      refine Step.of_local S.leafLabels m.pos hi _ fun x hx => ?_
      have := List.all_eq_true.mp hloc x hx
      have hget : S.leafLabels[(m.pos : Nat)] = labelOf S.reg S.leaves[m.pos] := by
        simp [leafLabels]
      rw [hget]
      exact (Label.ltb_iff _ _).mp this
    · cases hr : m.recordCert with
      | none => rw [hr] at hcert; cases hcert
      | some p => exact p.down
  · cases h

/-- The first learned conflict among the keys, if any. -/
def firstConflict (conflicts keys : List Nat) : Option Nat :=
  keys.find? (fun k => conflicts.contains k)

theorem firstConflict_none {conflicts keys : List Nat} (h : firstConflict conflicts keys = none) :
    ∀ k ∈ keys, k ∉ conflicts := by
  intro k hk hc
  have := List.find?_eq_none.mp h k hk
  simp [hc] at this

/-- The state after a verified move. -/
private def applyMove (S : State root) (m : Move S)
    (hvalid : ∀ c ∈ m.children, c.valid S.reg = true) : State root :=
  let r := resolve S.reg m.children
  have hpre := resolve_prefix S.reg m.children
  have hlen := resolve_length_le S.reg m.children
  have hkeys := resolve_keys_valid S.reg m.children hvalid
  { fams := S.fams
    reg := r.1
    leaves := replaceList S.leaves m.pos r.2
    conflicts := S.conflicts
    history := S.leaves :: S.history
    easierCount :=
      match S.creditOf m with
      | .certifiedEasier => S.easierCount + 1
      | .notCertifiedEasier => S.easierCount
    commitCount := S.commitCount + 1
    record :=
      match S.creditOf m with
      | .certifiedEasier => S.newLabels m
      | .notCertifiedEasier => S.record
    root_key := by
      obtain ⟨ext, h⟩ := hpre
      show RootAt r.1 root
      rw [h]
      exact S.root_key.append
    leaves_valid := by
      intro k hk
      rcases mem_replaceList hk with hk | hk | hk
      · exact hkeys k hk
      · exact Nat.lt_of_lt_of_le (S.leaves_valid k (List.mem_of_mem_take hk)) hlen
      · exact Nat.lt_of_lt_of_le (S.leaves_valid k (List.mem_of_mem_drop hk)) hlen
    conflicts_valid := fun k hk => Nat.lt_of_lt_of_le (S.conflicts_valid k hk) hlen
    conflicts_sound := by
      intro k hk hh
      obtain ⟨ext, h⟩ := hpre
      have hh' : holds (S.reg ++ ext) k := by rw [← h]; exact hh
      exact S.conflicts_sound k hk ((holds_append (S.conflicts_valid k hk)).mp hh')
    closeRoot := by
      intro hall
      obtain ⟨ext, h⟩ := hpre
      apply S.closeRoot
      intro k hk
      rcases mem_around m.pos.isLt hk with rfl | hmem | hmem
      · have hc := resolve_claims S.reg m.children hvalid
          (fun j hj => hall j (mem_replaceList_of_new hj))
        have hlg := m.cover hc
        exact (holds_iff (S.leaves_valid _ (List.getElem_mem _))).mpr hlg
      · have := hall k (mem_replaceList_of_take hmem)
        rw [h] at this
        exact (holds_append (S.leaves_valid k (List.mem_of_mem_take hmem))).mp this
      · have := hall k (mem_replaceList_of_drop hmem)
        rw [h] at this
        exact (holds_append (S.leaves_valid k (List.mem_of_mem_drop hmem))).mp this
    history_ok := by
      obtain ⟨ext, h⟩ := hpre
      have lift : ∀ l, SnapshotOK root S.reg l → SnapshotOK root r.1 l := by
        intro l ⟨hv, hc⟩
        refine ⟨fun k hk => Nat.lt_of_lt_of_le (hv k hk) hlen, fun hall => hc fun k hk => ?_⟩
        have := hall k hk
        rw [h] at this
        exact (holds_append (hv k hk)).mp this
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · exact lift _ ⟨S.leaves_valid, S.closeRoot⟩
      · exact lift l (S.history_ok l hl) }

/-- **Commit: verify, then commit or reject.** The coverage certificate is already checked by the
kernel, because a `Move` cannot be built without it. The remaining checks are decidable:
* the route is not dead (root not refuted);
* old keys are registered;
* no learned conflict is among the children.

The tag is the record-low credit rule (`creditOf`). -/
def commit (S : State root) (m : Move S) : Except Reject (State root × Tag) :=
  if S.rootRefuted then .error .rootRefuted else
  if hvalid : m.children.all (fun c => c.valid S.reg) then
    match _hc : firstConflict S.conflicts (resolve S.reg m.children).2 with
    | some k => .error (.learnedConflict k)
    | none =>
      .ok (applyMove S m (fun c hc => List.all_eq_true.mp hvalid c hc),
        S.creditOf m)
  else .error .unregisteredKey

/-- **The commit invariant.** Every accepted commit is a `Transition` of frontiers: closing the new
frontier closes the old one. -/
theorem commit_transition (S S' : State root) (m : Move S) (t : Tag)
    (h : commit S m = .ok (S', t)) : Transition S.frontier S'.frontier := by
  unfold commit at h
  split at h
  · cases h
  split at h
  · rename_i hvalid
    split at h
    · cases h
    · cases h
      refine ⟨fun hall => ?_⟩
      rw [allClosed_iff] at hall ⊢
      have hv : ∀ c ∈ m.children, c.valid S.reg = true :=
        fun c hc => List.all_eq_true.mp hvalid c hc
      obtain ⟨ext, hext⟩ := resolve_prefix S.reg m.children
      intro k hk
      rcases mem_around m.pos.isLt hk with rfl | hmem | hmem
      · have hc := resolve_claims S.reg m.children hv
          (fun j hj => hall j (mem_replaceList_of_new hj))
        exact (holds_iff (S.leaves_valid _ (List.getElem_mem _))).mpr (m.cover hc)
      · have := hall k (mem_replaceList_of_take hmem)
        change holds (resolve S.reg m.children).1 k at this
        rw [hext] at this
        exact (holds_append (S.leaves_valid k (List.mem_of_mem_take hmem))).mp this
      · have := hall k (mem_replaceList_of_drop hmem)
        change holds (resolve S.reg m.children).1 k at this
        rw [hext] at this
        exact (holds_append (S.leaves_valid k (List.mem_of_mem_drop hmem))).mp this
  · cases h

/-- **Learned conflicts are never re-admitted.** An accepted commit introduces no child key that
is a learned conflict. -/
theorem commit_no_conflict (S S' : State root) (m : Move S) (t : Tag)
    (h : commit S m = .ok (S', t)) : ∀ k ∈ (resolve S.reg m.children).2, k ∉ S.conflicts := by
  unfold commit at h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    · rename_i hc
      exact firstConflict_none hc
  · cases h

/-- The frontier labels after an accepted commit are the move's `newLabels`. -/
theorem commit_leafLabels (S S' : State root) (m : Move S) (t : Tag)
    (h : commit S m = .ok (S', t)) : S'.leafLabels = S.newLabels m := by
  unfold commit at h
  split at h
  · cases h
  split at h
  · rename_i hvalid
    split at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      have hv : ∀ c ∈ m.children, c.valid S.reg = true :=
        fun c hc => List.all_eq_true.mp hvalid c hc
      obtain ⟨ext, hext⟩ := resolve_prefix S.reg m.children
      have hlabels := resolve_labels S.reg m.children hv
      simp only [leafLabels, applyMove, newLabels]
      rw [map_replaceList, hlabels]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hk' : k < S.reg.length := S.leaves_valid k hk
      rw [hext, labelOf_append hk']
  · cases h

/-- The tag returned by an accepted commit is `creditOf`. -/
theorem commit_tag (S S' : State root) (m : Move S) (t : Tag)
    (h : commit S m = .ok (S', t)) : t = S.creditOf m := by
  unfold commit at h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2.symm
  · cases h

/-- The record after an accepted commit. -/
theorem commit_record (S S' : State root) (m : Move S) (t : Tag)
    (h : commit S m = .ok (S', t)) :
    S'.record = match S.creditOf m with
      | .certifiedEasier => S.newLabels m
      | .notCertifiedEasier => S.record := by
  unfold commit at h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      rfl
  · cases h

/-- **A credited commit lowers the record** in the (well-founded) DM order. -/
theorem commit_credit_record (S S' : State root) (m : Move S)
    (h : commit S m = .ok (S', .certifiedEasier)) : DMLt S'.record S.record := by
  have ht := commit_tag S S' m _ h
  have hr := commit_record S S' m _ h
  rw [← ht] at hr
  rw [hr]
  exact creditOf_sound S m ht.symm

/-- An uncounted commit leaves the record unchanged. -/
theorem commit_uncounted_record (S S' : State root) (m : Move S)
    (h : commit S m = .ok (S', .notCertifiedEasier)) : S'.record = S.record := by
  have ht := commit_tag S S' m _ h
  have hr := commit_record S S' m _ h
  rw [← ht] at hr
  exact hr

/-- **A dead route admits nothing.** Once the root is refuted, every move is rejected. -/
theorem commit_rootRefuted (S : State root) (m : Move S) (h : S.rootRefuted = true) :
    commit S m = .error .rootRefuted := by
  simp [commit, h]

/-- The certified-easier successor relation on states. -/
def EasierSucc (S' S : State root) : Prop :=
  ∃ m : Move S, commit S m = .ok (S', .certifiedEasier)

/-- **No infinite chain of certified-easier commits exists.** -/
theorem easierSucc_wf : WellFounded (@EasierSucc root) := by
  have : Subrelation (@EasierSucc root) (InvImage DMLt record) := by
    intro a b ⟨m, hm⟩
    exact commit_credit_record b a m hm
  exact this.wf (InvImage.wf _ DMLt.wf)

/-! ## Negatives: refute, learn, backtrack -/

/-- Backtrack target: the most recent history frontier with no conflicted key, else the root. -/
def backtrackTarget (conflicts : List Nat) (history : List (List Nat)) : List Nat :=
  match history.find? (fun h => h.all (fun k => !conflicts.contains k)) with
  | some h => h
  | none => [0]

theorem backtrackTarget_ok {fams : List Family} (root : Goal) (reg : List (Entry fams))
    (conflicts : List Nat) (history : List (List Nat))
    (hroot : RootAt reg root)
    (hhist : ∀ h ∈ history, SnapshotOK root reg h) :
    SnapshotOK root reg (backtrackTarget conflicts history) := by
  unfold backtrackTarget
  split
  · rename_i h hfind
    exact hhist h (List.mem_of_find?_eq_some hfind)
  · refine ⟨by simp [hroot.pos], fun hall => ?_⟩
    exact hroot.holds.mp (hall 0 (List.mem_singleton.mpr rfl))

/-- Add a conflict and backtrack if the live frontier contains a conflicted key. -/
private def withConflict (S : State root) (k : Nat) (hk : k < S.reg.length)
    (hrefuted : ¬ holds S.reg k) : State root :=
  let conflicts := k :: S.conflicts
  let dead := S.leaves.any (fun j => conflicts.contains j)
  have hok := backtrackTarget_ok root S.reg conflicts (S.leaves :: S.history) S.root_key
    (by
      intro h hh
      rcases List.mem_cons.mp hh with rfl | hh
      · exact ⟨S.leaves_valid, S.closeRoot⟩
      · exact S.history_ok h hh)
  { fams := S.fams
    reg := S.reg
    leaves := if dead then backtrackTarget conflicts (S.leaves :: S.history) else S.leaves
    conflicts := conflicts
    history := S.leaves :: S.history
    easierCount := S.easierCount
    commitCount := S.commitCount
    record := S.record
    root_key := S.root_key
    leaves_valid := by
      split
      · exact hok.1
      · exact S.leaves_valid
    conflicts_valid := by
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hk
      · exact S.conflicts_valid j hj
    conflicts_sound := by
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hrefuted
      · exact S.conflicts_sound j hj
    closeRoot := by
      split
      · exact hok.2
      · exact S.closeRoot
    history_ok := by
      intro h hh
      rcases List.mem_cons.mp hh with rfl | hh
      · exact ⟨S.leaves_valid, S.closeRoot⟩
      · exact S.history_ok h hh }

/-- **Refute a leaf.** The disproof of the exact registered obligation becomes a learned conflict,
and the state backtracks. -/
def refute (S : State root) (i : Fin S.leaves.length) (h : ¬ (S.leafGoal i).claim) : State root :=
  withConflict S S.leaves[i] (S.leaves_valid _ (List.getElem_mem _))
    (fun hh => h ((holds_iff (S.leaves_valid _ (List.getElem_mem _))).mp hh))

/-- **Learn** (propagate a conflict). If obligation `k'` implies a learned conflict `k`, then `k'`
is refuted too. This is how a restatement with a new key is blocked, once any detector supplies
the implication. -/
def learn (S : State root) (k' : Nat) (hk' : k' < S.reg.length) (k : Nat) (hk : k ∈ S.conflicts)
    (imp : holds S.reg k' → holds S.reg k) : State root :=
  withConflict S k' hk' (fun hh => S.conflicts_sound k hk (imp hh))

/-! ## Every run earns finitely many credits (the record-low rule) -/

/-- One step of any run: a commit, a refutation or a learned conflict. -/
inductive Advance (S : State root) : State root → Prop
  | commit (m : Move S) (t : Tag) (S' : State root) (h : commit S m = .ok (S', t)) : Advance S S'
  | refute (i : Fin S.leaves.length) (h : ¬ (S.leafGoal i).claim) : Advance S (S.refute i h)
  | learn (k' : Nat) (hk' : k' < S.reg.length) (k : Nat) (hk : k ∈ S.conflicts)
      (imp : holds S.reg k' → holds S.reg k) : Advance S (S.learn k' hk' k hk imp)

/-- A credited step. -/
def Credited (S S' : State root) : Prop := ∃ m : Move S, commit S m = .ok (S', .certifiedEasier)

theorem refute_record (S : State root) (i : Fin S.leaves.length) (h : ¬ (S.leafGoal i).claim) :
    (S.refute i h).record = S.record := rfl

theorem learn_record (S : State root) (k' : Nat) (hk' : k' < S.reg.length) (k : Nat)
    (hk : k ∈ S.conflicts) (imp : holds S.reg k' → holds S.reg k) :
    (S.learn k' hk' k hk imp).record = S.record := rfl

/-- Along any step the record stays or strictly drops. -/
theorem advance_record {S S' : State root} (h : Advance S S') :
    S'.record = S.record ∨ DMLt S'.record S.record := by
  cases h with
  | commit m t S' hc =>
    cases t with
    | certifiedEasier => exact Or.inr (commit_credit_record S S' m hc)
    | notCertifiedEasier => exact Or.inl (commit_uncounted_record S S' m hc)
  | refute i h => exact Or.inl (refute_record S i h)
  | learn k' hk' k hk imp => exact Or.inl (learn_record S k' hk' k hk imp)

/-- Along a run, the record at a later index is equal to or DM-below an earlier one. -/
theorem run_record_mono (s : Nat → State root) (hs : ∀ i, Advance (s i) (s (i + 1))) :
    ∀ i j, i ≤ j → (s j).record = (s i).record ∨ DMLt (s j).record (s i).record := by
  intro i j hij
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact Or.inl rfl
  | succ j ih =>
    by_cases hij' : i ≤ j
    · have ih := ih hij'
      rcases advance_record (hs j) with h | h
      · rw [h]; exact ih
      · rcases ih with ih | ih
        · exact Or.inr (ih ▸ h)
        · exact Or.inr (Relation.TransGen.trans h ih)
    · have : i = j + 1 := by omega
      subst this; exact Or.inl rfl

/-- **Every run earns only finitely many credits.** There is no run (commits, refutations and
learned conflicts in any order) with credited steps beyond every index. Unlike `easierSucc_wf`,
this covers mixed runs: grow-then-shrink cycles cannot re-earn credit. -/
theorem no_infinite_credits :
    ¬ ∃ s : Nat → State root, (∀ i, Advance (s i) (s (i + 1))) ∧
      (∀ i, ∃ j, i ≤ j ∧ Credited (s j) (s (j + 1))) := by
  rintro ⟨s, hs, hinf⟩
  have key : ∀ r, Acc DMLt r → ∀ i, (s i).record = r → False := by
    intro r hr
    induction hr with
    | intro r _ ih =>
      intro i hi
      obtain ⟨j, hij, m, hm⟩ := hinf i
      have hdrop := commit_credit_record (s j) (s (j + 1)) m hm
      have hmono := run_record_mono s hs i j hij
      apply ih (s (j + 1)).record _ (j + 1) rfl
      rw [← hi]
      rcases hmono with h | h
      · rw [← h]; exact hdrop
      · exact Relation.TransGen.trans hdrop h
  exact key _ (DMLt.wf.apply _) 0 rfl

/-! ## Part 2, M2: conflict persistence, including stutters -/

/-- The only permitted intersection of frontier and conflicts is the refuted root fallback. -/
def Clean (S : State root) : Prop :=
  (∀ k ∈ S.leaves, k ∉ S.conflicts) ∨ (S.leaves = [0] ∧ 0 ∈ S.conflicts)

/-- A run step may be an admitted state change or a stutter. -/
def Next (S S' : State root) : Prop := Advance S S' ∨ S' = S

theorem initial_clean (fams : List Family) (l : Label) (hl : LabelOK fams root l) :
    (initial root fams l hl).Clean := by
  left
  simp [initial]

theorem commit_conflicts (S S' : State root) (m : Move S) (t : Tag)
    (h : commit S m = .ok (S', t)) : S'.conflicts = S.conflicts := by
  unfold commit at h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    · cases h; rfl
  · cases h

theorem commit_clean (S S' : State root) (m : Move S) (t : Tag)
    (h : commit S m = .ok (S', t)) (hS : S.Clean) : S'.Clean := by
  rcases hS with hS | ⟨_, h0⟩
  · have hchildren := commit_no_conflict S S' m t h
    unfold commit at h
    split at h
    · cases h
    split at h
    · split at h
      · cases h
      · cases h
        left
        intro k hk
        change k ∉ S.conflicts
        rcases mem_replaceList hk with hk | hk | hk
        · exact hchildren k hk
        · exact hS k (List.mem_of_mem_take hk)
        · exact hS k (List.mem_of_mem_drop hk)
    · cases h
  · have hr : S.rootRefuted = true := by simp [rootRefuted, h0]
    rw [commit_rootRefuted S m hr] at h
    cases h

theorem backtrackTarget_clean (conflicts : List Nat) (history : List (List Nat)) :
    (∀ k ∈ backtrackTarget conflicts history, k ∉ conflicts) ∨
      (backtrackTarget conflicts history = [0] ∧ 0 ∈ conflicts) := by
  unfold backtrackTarget
  split
  · rename_i l hl
    left
    have hall := List.find?_some hl
    intro k hk
    have h := List.all_eq_true.mp hall k hk
    simpa using h
  · by_cases h0 : 0 ∈ conflicts
    · exact .inr ⟨rfl, h0⟩
    · left; simpa using h0

theorem advance_conflicts {S S' : State root} (h : Advance S S') :
    ∀ k ∈ S.conflicts, k ∈ S'.conflicts := by
  cases h with
  | commit m t S' hc => rw [commit_conflicts S S' m t hc]; exact fun _ hk => hk
  | refute i h => exact fun k hk => List.mem_cons_of_mem _ hk
  | learn k' hk' k hk imp => exact fun j hj => List.mem_cons_of_mem _ hj

theorem advance_clean {S S' : State root} (h : Advance S S') (hS : S.Clean) : S'.Clean := by
  have hneg (k : Nat) (hk : k < S.reg.length) (hn : ¬ holds S.reg k) :
      (withConflict S k hk hn).Clean := by
    unfold Clean withConflict
    dsimp
    split
    · exact backtrackTarget_clean _ _
    · rename_i hnone
      left
      intro j hj hc
      have : S.leaves.any (fun j => (k :: S.conflicts).contains j) = true :=
        List.any_eq_true.mpr ⟨j, hj, by simpa using hc⟩
      exact hnone this
  cases h with
  | commit m t S' hc => exact commit_clean S S' m t hc hS
  | refute i h => exact hneg _ _ _
  | learn k' hk' k hk imp => exact hneg _ _ _

theorem next_conflicts {S S' : State root} (h : Next S S') :
    ∀ k ∈ S.conflicts, k ∈ S'.conflicts := by
  rcases h with h | rfl
  · exact advance_conflicts h
  · exact fun _ hk => hk

theorem next_clean {S S' : State root} (h : Next S S') (hS : S.Clean) : S'.Clean := by
  rcases h with h | rfl
  · exact advance_clean h hS
  · exact hS

theorem run_conflicts_mono (s : Nat → State root)
    (hs : ∀ i, Advance (s i) (s (i + 1)) ∨ s (i + 1) = s i)
    {i j : Nat} (hij : i ≤ j) : ∀ k ∈ (s i).conflicts, k ∈ (s j).conflicts := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact fun _ hk => hk
  | succ j ih =>
    by_cases hij' : i ≤ j
    · exact fun k hk => next_conflicts (hs j) k (ih hij' k hk)
    · have : i = j + 1 := by omega
      subst i
      exact fun _ hk => hk

theorem run_clean (s : Nat → State root)
    (hs : ∀ i, Advance (s i) (s (i + 1)) ∨ s (i + 1) = s i)
    (h0 : (s 0).Clean) : ∀ i, (s i).Clean := by
  intro i
  induction i with
  | zero => exact h0
  | succ i ih => exact next_clean (hs i) ih

theorem run_no_readmission (s : Nat → State root)
    (hs : ∀ i, Advance (s i) (s (i + 1)) ∨ s (i + 1) = s i)
    {i j : Nat} (hij : i ≤ j) (m : Move (s j)) (t : Tag)
    (hm : commit (s j) m = .ok (s (j + 1), t)) :
    ∀ k ∈ (resolve (s j).reg m.children).2, k ∉ (s i).conflicts := by
  intro k hk hconf
  exact commit_no_conflict (s j) (s (j + 1)) m t hm k hk
    (run_conflicts_mono s hs hij k hconf)

/-- Every previously learned key remains certified false in the current registry. -/
theorem run_conflict_refuted (s : Nat → State root)
    (hs : ∀ i, Advance (s i) (s (i + 1)) ∨ s (i + 1) = s i)
    {i j : Nat} (hij : i ≤ j) {k : Nat} (hk : k ∈ (s i).conflicts) :
    ¬ holds (s j).reg k :=
  (s j).conflicts_sound k (run_conflicts_mono s hs hij k hk)

/-! ## Part 3, M4: repeatable accepted self-moves -/

def selfMove (S : State root) (i : Fin S.leaves.length) : Move S where
  pos := i
  children := [.old S.leaves[i]]
  cover h := (holds_iff (S.leaves_valid _ (List.getElem_mem _))).mp
    (h (.old S.leaves[i]) (List.mem_singleton.mpr rfl))

/-! ## Part 4: constructive list reconstruction and the M4 retry -/

universe u

theorem take_self_drop {α : Type u} (l : List α) (i : Fin l.length) :
    l.take i.val ++ l[i] :: l.drop (i.val + 1) = l := by
  change l.take i.val ++ l[i.val] :: l.drop (i.val + 1) = l
  rw [List.getElem_cons_drop i.isLt, List.take_append_drop]

theorem selfMove_local_false (S : State root) (i : Fin S.leaves.length) :
    S.localEasier (selfMove S i) = false := by
  change ((labelOf S.reg S.leaves[i]).ltb (labelOf S.reg S.leaves[i]) && true) = false
  cases labelOf S.reg S.leaves[i] <;> simp [Label.ltb]

theorem selfMove_valid (S : State root) (i : Fin S.leaves.length) :
    (selfMove S i).children.all (fun c => c.valid S.reg) = true := by
  change (decide (S.leaves[i.val] < S.reg.length) && true) = true
  have hk : decide (S.leaves[i.val] < S.reg.length) = true :=
    decide_eq_true (S.leaves_valid _ (List.getElem_mem i.isLt))
  exact congrArg (fun b : Bool => b && true) hk

theorem selfMove_credit (S : State root) (i : Fin S.leaves.length) :
    S.creditOf (selfMove S i) = .notCertifiedEasier := by
  unfold creditOf
  rw [selfMove_local_false]
  rfl

theorem selfMove_commit (S : State root) (hS : S.Clean) (h0 : 0 ∉ S.conflicts)
    (i : Fin S.leaves.length) :
    ∃ S', commit S (selfMove S i) = .ok (S', .notCertifiedEasier) ∧
      S'.leaves = S.leaves ∧ S'.conflicts = S.conflicts := by
  have hk : S.leaves[i.val] ∉ S.conflicts := by
    rcases hS with hS | ⟨_, hbad⟩
    · exact hS _ (List.getElem_mem i.isLt)
    · exact (h0 hbad).elim
  have hr : S.rootRefuted = false := by simpa [rootRefuted] using h0
  have hv := selfMove_valid S i
  have hf : firstConflict S.conflicts (resolve S.reg (selfMove S i).children).2 = none := by
    simp [selfMove, resolve, firstConflict, hk]
  refine ⟨applyMove S (selfMove S i) (fun c hc => List.all_eq_true.mp hv c hc), ?_, ?_, rfl⟩
  · simp only [commit, hr, Bool.false_eq_true, if_false, dif_pos hv, selfMove_credit]
    split
    · rename_i k hsome
      have : none = some k := hf.symm.trans hsome
      cases this
    · rfl
  · change replaceList S.leaves i [S.leaves[i]] = S.leaves
    unfold replaceList
    rw [List.append_assoc, List.singleton_append]
    exact take_self_drop S.leaves i

/-- Computed successor from the existing commit API; rejection leaves the state unchanged. -/
def selfNext (S : State root) (i : Fin S.leaves.length) : State root :=
  match commit S (selfMove S i) with
  | .ok (S', _) => S'
  | .error _ => S

theorem selfNext_spec (S : State root) (hS : S.Clean) (h0 : 0 ∉ S.conflicts)
    (i : Fin S.leaves.length) :
    commit S (selfMove S i) = .ok (selfNext S i, .notCertifiedEasier) ∧
      (selfNext S i).leaves = S.leaves ∧ (selfNext S i).conflicts = S.conflicts := by
  obtain ⟨T, hc, hl, hk⟩ := selfMove_commit S hS h0 i
  have hn : selfNext S i = T := by simp only [selfNext, hc]
  rw [hn]
  exact ⟨hc, hl, hk⟩

theorem infinite_uncredited (S : State root) (hS : S.Clean) (h0 : 0 ∉ S.conflicts)
    (hne : S.leaves ≠ []) :
    ∃ s : Nat → State root, s 0 = S ∧
      ∀ n, ∃ m : Move (s n), commit (s n) m = .ok (s (n + 1), .notCertifiedEasier) := by
  let Good := { T : State root // T.Clean ∧ 0 ∉ T.conflicts ∧ T.leaves ≠ [] }
  let pos (q : Good) : Fin q.val.leaves.length := ⟨0, List.length_pos_iff.mpr q.property.2.2⟩
  let next (q : Good) : Good :=
    let hs := selfNext_spec q.val q.property.1 q.property.2.1 (pos q)
    ⟨selfNext q.val (pos q),
      advance_clean (.commit (selfMove q.val (pos q)) _ _ hs.1) q.property.1,
      by rw [hs.2.2]; exact q.property.2.1,
      by rw [hs.2.1]; exact q.property.2.2⟩
  let seq : Nat → Good := fun n => Nat.rec ⟨S, hS, h0, hne⟩ (fun _ q => next q) n
  refine ⟨fun n => (seq n).val, rfl, ?_⟩
  intro n
  exact ⟨selfMove (seq n).val (pos (seq n)),
    (selfNext_spec (seq n).val (seq n).property.1 (seq n).property.2.1 (pos (seq n))).1⟩


end State

/-! ## Convenience constructors for moves -/

namespace Move

variable {root : Goal} {S : State root}

/-- A move from a split of the leaf's goal. Every child is new, with an unmeasured label. -/
def ofSplit (S : State root) (i : Fin S.leaves.length) (s : Split (S.leafGoal i)) : Move S where
  pos := i
  children := s.children.map fun g => .new ⟨g, .top, trivial⟩
  cover h := s.discharge fun c hc =>
    h (.new ⟨c, .top, trivial⟩) (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- A move from an edge (refinement), with an unmeasured child. -/
def ofEdge (S : State root) (i : Fin S.leaves.length) (child : Goal)
    (e : Edge (S.leafGoal i) child) : Move S where
  pos := i
  children := [.new ⟨child, .top, trivial⟩]
  cover h := e.discharge (h _ (List.mem_singleton.mpr rfl))

/-- A closure: a proof of the leaf. -/
def close (S : State root) (i : Fin S.leaves.length) (proof : (S.leafGoal i).claim) : Move S where
  pos := i
  children := []
  cover _ := proof

/-- **Rung 2 settled in the kernel**: close a leaf by a decision procedure together with the
evaluated result. With `h := rfl` the kernel runs the program. -/
def closeByComputation (S : State root) (i : Fin S.leaves.length) (c : MechCert (S.leafGoal i))
    (h : c.decide () = true) : Move S :=
  close S i (c.settle h)

/-- The claims of the move's new children (for the admission-time restatement check, D1). -/
def freshClaims (m : Move S) : List Prop :=
  m.children.filterMap fun
    | .new e => some e.goal.claim
    | .old _ => none

end Move

end CRRGCore
