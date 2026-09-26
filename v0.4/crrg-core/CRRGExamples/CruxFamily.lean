import CRRGCore

/-!
# Crux families: one shared guarded edge, several consumers (synthetic example)

A **crux family** is one shared guarded edge consumed by the crux nodes of several routes. Each
member either **discharges** the edge's guard (and gets the pass leaf) or keeps a **named escape
leaf** in its own frontier. An admitted result on the shared edge narrows the escape leaves of every
member through one function, `Family.admit`, so the members' frontiers change consistently.

**Synthetic example.** The guard, the members, the regions and the evidence below are made up to
exercise every part of the mechanism; they model no particular problem. `families/demo.json` is the
same guard in the runner's JSON form, and `FamilyAgreement.lean` checks that the two agree.

**Labels used below.**
* *proved*: a theorem over all inputs, checked by the Lean kernel.
* *computed*: a `decide` check on the synthetic instance, also kernel-checked, but only for that
  instance.
* *design*: modelling choices, stated in comments.
-/

namespace CRRGExamples.CruxFamily

open CRRGCore

/-! ## The shared edge's guard fields (synthetic) -/

/-- The guard fields of the shared edge, one constructor per clause of its condition. -/
inductive Field where
  | mode1        -- the consumer's node is in mode 1
  | mOdd         -- the modulus `m` is odd
  | mCertified   -- data obligation: an external certificate for `m`, cited as evidence
  | kDvd         -- the step `k` divides `m + 1`
  | kRange       -- `k < m ≤ 4 k`
  | xWindow      -- the consumer's own value lies in its window: `lo ≤ x ≤ hi`
  | profile      -- joint: ONE witness with minimum degree at least 2 and mass at most 40
  deriving DecidableEq, Repr

/-- Every field of the guard, in order. -/
def allFields : List Field := [.mode1, .mOdd, .mCertified, .kDvd, .kRange, .xWindow, .profile]

/-- What a consumer supplies about its instance. `none` means the consumer does not supply it. -/
structure Inst where
  mode : Nat
  m : Nat
  mCertified : Option Bool   -- data obligation, with its evidence reference in the JSON
  k : Nat
  lo : Nat
  x : Nat
  hi : Nat
  minDeg : Option Nat        -- the joint witness: its minimum degree…
  mass : Nat                 -- …and its mass (one witness carries both, by construction)
  deriving DecidableEq, Repr

/-- The guard's numeric constants (the JSON's `value`s; `FamilyAgreement.numbers_agree`). -/
def modeReq : Nat := 1
def minDegLow : Nat := 2
def massBudget : Nat := 40

/-- Whether a field holds on an instance. Missing data never holds. -/
def Field.holds : Field → Inst → Bool
  | .mode1, i => i.mode == modeReq
  | .mOdd, i => i.m % 2 == 1
  | .mCertified, i => i.mCertified == some true
  | .kDvd, i => i.k != 0 && (i.m + 1) % i.k == 0
  | .kRange, i => decide (i.k < i.m) && decide (i.m ≤ 4 * i.k)
  | .xWindow, i => decide (i.lo ≤ i.x) && decide (i.x ≤ i.hi)
  | .profile, i => match i.minDeg with
      | some d => decide (minDegLow ≤ d) && decide (i.mass ≤ massBudget)
      | none => false

/-- The guard of the shared edge: every field holds. -/
def guard (i : Inst) : Prop := ∀ f ∈ allFields, f.holds i = true

instance (i : Inst) : Decidable (guard i) := by unfold guard; infer_instance

/-- The fields that fail on an instance (the runner reports exactly these). -/
def failing (i : Inst) : List Field := allFields.filter fun f => !f.holds i

/-- *proved*: the guard holds iff no field fails. -/
theorem guard_iff_no_failing (i : Inst) : guard i ↔ failing i = [] := by
  unfold guard failing
  constructor
  · intro h
    rw [List.filter_eq_nil_iff]
    intro f hf
    simp [h f hf]
  · intro h f hf
    rw [List.filter_eq_nil_iff] at h
    have := h f hf
    simpa using this

/-! ## Members (synthetic) -/

/-- What the member's crux node needs from the edge. The shared edge **bills** (it pays for the
node's obligation). An **exclusion** node needs a different kind of statement, which a bill does
not give, whatever the guard (*design*). -/
inductive NodeKind where
  | bill | exclusion
  deriving DecidableEq, Repr

/-- A member: a route's crux node, what it needs, and its instance for the shared edge. -/
structure Member where
  route : String
  node : String
  kind : NodeKind
  inst : Inst
  deriving DecidableEq, Repr

/-- The edge is usable by a member iff the member discharges the guard **and** needs a bill. -/
def usable (m : Member) : Prop := guard m.inst ∧ m.kind = .bill

instance (m : Member) : Decidable (usable m) := by unfold usable; infer_instance

/-- Route A's billing node: every field holds (`m = 11`, `k = 4`, `x = 25 ∈ [20, 30]`, profile
`(2, 36)`). -/
def aPass : Member :=
  ⟨"route-a", "A1", .bill, ⟨1, 11, some true, 4, 20, 25, 30, some 2, 36⟩⟩

/-- Route A's exclusion node: the same instance (so the guard holds), but a bill does not give what
it needs. -/
def aExcl : Member := { aPass with node := "A0", kind := .exclusion }

/-- Route B: its value lies below the window, and it supplies no profile. -/
def bLow : Member :=
  ⟨"route-b", "B1", .bill, ⟨1, 11, some true, 4, 20, 12, 30, none, 0⟩⟩

/-- Route C: mode 2, an even modulus, no certificate, a step that fails both `k` fields, and a
profile over the mass budget. -/
def cEven : Member :=
  ⟨"route-c", "C1", .bill, ⟨2, 12, none, 2, 0, 0, 0, some 3, 50⟩⟩

/-- The synthetic family's members. -/
def members : List Member := [aPass, aExcl, bLow, cEven]

/-- *computed*: who discharges the guard: only route A's two nodes (they share the instance). -/
theorem discharge_status :
    members.map (fun m => decide (guard m.inst)) = [true, true, false, false] := by
  decide

/-- *computed*: who can use the edge: only route A's billing node. -/
theorem usable_status :
    members.map (fun m => decide (usable m)) = [true, false, false, false] := by
  decide

/-- *computed*: the failing fields per member (what each must supply or cannot supply). -/
theorem failing_bLow : failing bLow.inst = [.xWindow, .profile] := by decide
theorem failing_cEven : failing cEven.inst =
    [.mode1, .mOdd, .mCertified, .kDvd, .kRange, .profile] := by decide

/-! ## Claiming the edge requires discharging the guard -/

/-- A member's claim of the shared edge: it must carry a proof of the guard on its instance. -/
structure Claim (m : Member) : Prop where
  discharge : guard m.inst

/-- *proved*: a member whose guard fails cannot claim the edge (no term of `Claim m` exists). -/
theorem no_claim_without_guard (m : Member) (h : ¬ guard m.inst) : ¬ Claim m :=
  fun c => h c.discharge

/-- *computed*: routes B and C cannot claim; route A can. -/
theorem bLow_no_claim : ¬ Claim bLow := no_claim_without_guard _ (by decide)
theorem cEven_no_claim : ¬ Claim cEven := no_claim_without_guard _ (by decide)
theorem aPass_claim : Claim aPass := ⟨by decide⟩

/-- *proved*: a claim is exactly a `GuardedEdge` pass: from the claim and the shared edge's paper
proof (`paper → bill`), the member gets its bill; without the guard it keeps the escape leaf. -/
def memberEdge (m : Member) (bill paper : Goal) (proof : guard m.inst → paper.claim → bill.claim) :
    GuardedEdge bill paper (guard m.inst) := ⟨proof⟩

/-- The member's split: pass leaf `guard → paper` and escape leaf `¬ guard → bill`. -/
def memberSplit (m : Member) (bill paper : Goal)
    (proof : guard m.inst → paper.claim → bill.claim) : Split bill :=
  (memberEdge m bill paper proof).toSplit

/-! ## Escape leaves and admitted evidence -/

/-- A named escape leaf, or a region still open: a list of closed intervals of a parameter `x` or
of a second parameter `y`. -/
inductive Leaf where
  | named (name : String)
  | xRegion (open_ : List (Nat × Nat))
  | yRegion (open_ : List (Nat × Nat))
  deriving DecidableEq, Repr

/-- Remove the closed interval `[a, b]` from one open interval. -/
def cutOne (a b : Nat) : Nat × Nat → List (Nat × Nat)
  | (lo, hi) =>
    if b < lo || hi < a then [(lo, hi)]
    else (if lo < a then [(lo, a - 1)] else []) ++ (if b < hi then [(b + 1, hi)] else [])

/-- Remove `[a, b]` from a region. -/
def cut (a b : Nat) (r : List (Nat × Nat)) : List (Nat × Nat) := r.flatMap (cutOne a b)

/-- An admitted result on the shared edge: the named leaves it closes and the intervals it bills on
each region. -/
structure Evidence where
  id : String
  closes : List String
  xClosed : List (Nat × Nat)
  yClosed : List (Nat × Nat) := []
  deriving DecidableEq, Repr

/-- Apply evidence to one leaf. -/
def Leaf.narrow (e : Evidence) : Leaf → Option Leaf
  | .named n => if e.closes.contains n then none else some (.named n)
  | .xRegion r =>
    let r' := e.xClosed.foldl (fun acc (ab : Nat × Nat) => cut ab.1 ab.2 acc) r
    if r' = [] then none else some (.xRegion r')
  | .yRegion r =>
    let r' := e.yClosed.foldl (fun acc (ab : Nat × Nat) => cut ab.1 ab.2 acc) r
    if r' = [] then none else some (.yRegion r')

/-- A member's state in the family: its instance and its open escape leaves. -/
structure MemberState where
  member : Member
  leaves : List Leaf
  deriving DecidableEq, Repr

/-- Evidence narrows a member's leaves **only if the member can use the edge** (guard discharged,
billing node); otherwise the member's frontier is unchanged. -/
def MemberState.admit (e : Evidence) (s : MemberState) : MemberState :=
  if usable s.member then { s with leaves := s.leaves.filterMap (Leaf.narrow e) } else s

/-- The family: the shared edge's evidence and every member's state. -/
structure Family where
  evidence : List String
  states : List MemberState
  deriving DecidableEq, Repr

/-- **One admitted result updates every member through the same function.** -/
def Family.admit (e : Evidence) (F : Family) : Family :=
  ⟨e.id :: F.evidence, F.states.map (MemberState.admit e)⟩

/-- *proved*: admission keeps the member list (same members, same order). -/
theorem admit_members (e : Evidence) (F : Family) :
    (F.admit e).states.map (·.member) = F.states.map (·.member) := by
  simp [Family.admit, List.map_map, Function.comp_def, MemberState.admit]
  intro s _
  split <;> rfl

/-- *proved*: a member that does not discharge the guard is untouched by any admission. -/
theorem admit_nondischarging (e : Evidence) (s : MemberState) (h : ¬ guard s.member.inst) :
    s.admit e = s := by
  simp [MemberState.admit, usable, h]

/-- *proved*: an exclusion node is untouched by any admission, even when its guard holds. -/
theorem admit_exclusion (e : Evidence) (s : MemberState) (h : s.member.kind = .exclusion) :
    s.admit e = s := by
  simp [MemberState.admit, usable, h]

/-- *proved*: every member is updated by the same rule (consistency): the family's new states are
exactly the per-member admissions. -/
theorem admit_pointwise (e : Evidence) (F : Family) (i : Nat) :
    (F.admit e).states[i]? = (F.states[i]?).map (MemberState.admit e) := by
  simp [Family.admit]

/-- *proved*: admission never opens a new named leaf: every named leaf after admission was there
before. -/
theorem admit_named_monotone (e : Evidence) (s : MemberState) (n : String) :
    Leaf.named n ∈ (s.admit e).leaves → Leaf.named n ∈ s.leaves := by
  unfold MemberState.admit
  split
  · intro h
    rw [List.mem_filterMap] at h
    obtain ⟨l, hl, hn⟩ := h
    cases l with
    | named m =>
      simp only [Leaf.narrow] at hn
      split at hn
      · cases hn
      · cases hn; exact hl
    | xRegion r =>
      simp only [Leaf.narrow] at hn
      split at hn
      · cases hn
      · cases hn
    | yRegion r =>
      simp only [Leaf.narrow] at hn
      split at hn
      · cases hn
      · cases hn
  · exact id

/-! ## The synthetic family and four admitted results -/

/-- The escape leaves of a member that can use the edge: three named cases and two open regions,
`x ∈ [0, 99]` and `y ∈ [0, 49]`. -/
def usableLeaves : List Leaf :=
  [.named "case-a", .named "case-b", .named "case-c", .xRegion [(0, 99)], .yRegion [(0, 49)]]

/-- Members that cannot use the edge keep one named leaf: the node's own claim, to be met by their
own instantiation, or by an exclusion argument when the guard holds but the node is not a bill. -/
def ownLeaf (m : Member) : List Leaf :=
  if guard m.inst then [.named "exclusion-form"] else [.named "own-instantiation"]

def family0 : Family :=
  ⟨[], members.map fun m => ⟨m, if decide (usable m) then usableLeaves else ownLeaf m⟩⟩

def ownInstantiation : List Leaf := [.named "own-instantiation"]

/-- `ev-1`: closes `case-a` and bills `x ∈ [60, 99]`. -/
def ev1 : Evidence := ⟨"ev-1", ["case-a"], [(60, 99)], []⟩

/-- `ev-2`: closes `case-b` and bills `x ∈ [0, 29]` and the overlapping `x ∈ [25, 44]`. -/
def ev2 : Evidence := ⟨"ev-2", ["case-b"], [(0, 29), (25, 44)], []⟩

/-- `ev-3`: bills `x ∈ [45, 59]`, the last open part of the `x` region. -/
def ev3 : Evidence := ⟨"ev-3", [], [(45, 59)], []⟩

/-- `ev-4`: bills `y ∈ [30, 49]`. -/
def ev4 : Evidence := ⟨"ev-4", [], [], [(30, 49)]⟩

/-- Route A's billing node after `ev-1` and `ev-2`: `x` is open only on `[45, 59]`. -/
def afterTwo : List Leaf := [.named "case-c", .xRegion [(45, 59)], .yRegion [(0, 49)]]

/-- Route A's billing node after all four: the `x` region is closed and `y` is open on `[0, 29]`. -/
def afterAll : List Leaf := [.named "case-c", .yRegion [(0, 29)]]

/-- The family after `ev-1`, `ev-2`, `ev-3` and `ev-4`. -/
def family4 : Family := (((family0.admit ev1).admit ev2).admit ev3).admit ev4

/-- *computed*: after the four admissions, route A's billing node carries exactly `afterAll`, and
the other members are unchanged. -/
theorem after_all4 :
    family4.states.map (·.leaves) =
      [afterAll, [.named "exclusion-form"], ownInstantiation, ownInstantiation] := by
  decide

/-- *computed*: admitting the four results in reverse order gives the same states (the intervals
are cut in a different order, and the `x` region is split in two on the way). -/
theorem after_all4_reversed :
    ((((family0.admit ev4).admit ev3).admit ev2).admit ev1).states = family4.states := by
  decide

/-- *computed*: after `ev-1` then `ev-2`, route A's billing node carries exactly `afterTwo`, and
every other member is unchanged. -/
theorem after_two :
    ((family0.admit ev1).admit ev2).states.map (·.leaves) =
      [afterTwo, [.named "exclusion-form"], ownInstantiation, ownInstantiation] := by
  decide

/-- *computed*: the order of admission does not matter on this instance. The general statement is
`CRRGClassical.admitAll_perm` in crrg-classical. -/
theorem admit_order_irrelevant :
    ((family0.admit ev1).admit ev2).states = ((family0.admit ev2).admit ev1).states := by
  decide

end CRRGExamples.CruxFamily
