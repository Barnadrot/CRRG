#!/usr/bin/env python3
"""Writes the runner's negative-control and positive suite into runner/tests/<case>/.

Each case has Submission.lean, manifest.json and expect.json. expect.json holds the exact verdict,
the exact reason codes, the commit tag when accepted, where the case comes from, and, for forgeries,
the reasons expected when the lint is bypassed (--continue-after-lint: defence in depth).
Regenerate with `python3 runner/make_tests.py`; the files are committed, so reviewers can read them.
"""

import json
import os
import shutil

HERE = os.path.dirname(os.path.abspath(__file__))
TESTS = os.path.join(HERE, "tests")

HEAD = """import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
"""
TAIL = "end Sub\n"
IMPORTS = ["CRRGExamples.Negatives"]

# A legitimate move used by probes whose point is elsewhere (forgeries, lint): settle 8 % 2 = 0.
LEGIT_MOVE = """def move : Move (E1 8) :=
  Move.closeByComputation (E1 8) ⟨0, Nat.zero_lt_one⟩ (evenCert 8) rfl
"""
LEGIT = {"state": "CRRGExamples.E1 8", "move": "Sub.move"}

# The Probe2 forgery (a review probe, adapted to the current State fields), parameterised by name.
FORGE = """import Lean
import CRRGExamples.Negatives
open Lean Meta Elab Command
open CRRGCore CRRGExamples

def forgeState (declName : Name) : CommandElabM Unit := do
  let mkN := Name.mkNum `_private.CRRGCore.State 0 ++ `CRRGCore.State.mk
  let (val, ty) ← liftTermElabM do
    let stConst ← mkConstWithFreshMVarLevels ``CRRGCore.State
    let goalTy := (← inferType stConst).bindingDomain!
    withLocalDeclD `root goalTy fun root => do
      withLocalDeclD `S (mkApp stConst root) fun S => do
        let p (f : Name) := mkAppM (``CRRGCore.State ++ f) #[S]
        let args := #[← p `fams, ← p `reg, ← p `leaves, ← p `conflicts, ← p `history,
                      mkNatLit 1000000, ← p `commitCount, ← p `record, ← p `root_key,
                      ← p `leaves_valid, ← p `conflicts_valid, ← p `conflicts_sound,
                      ← p `closeRoot, ← p `history_ok]
        let v ← mkAppM mkN args
        let v ← instantiateMVars (← mkLambdaFVars #[root, S] v)
        let t ← instantiateMVars (← inferType v)
        return (v, t)
  liftCoreM <| addDecl (.defnDecl (mkDefinitionValEx declName [] ty val .abbrev .safe [declName]))
"""

CASES = {}


def case(name, source, origin, verdict, reasons, tag=None, state=None, move=None, r1=None,
         imports=None, bypass=None, note=None, guard_claim=None):
    CASES[name] = dict(source=source, origin=origin, verdict=verdict, reasons=sorted(reasons),
                       tag=tag, state=state or LEGIT["state"], move=move or LEGIT["move"], r1=r1,
                       imports=IMPORTS if imports is None else imports, bypass=bypass, note=note,
                       guard_claim=guard_claim)


def sub(body):
    return HEAD + body + TAIL


# ---------------------------------------------------------------- forgeries and the lint
case("probe2_forgery",
     FORGE + "\nelab \"#forge\" : command => forgeState `forgedBump\n#forge\n\nnamespace Sub\n"
     + LEGIT_MOVE + TAIL,
     "Probe2 (G1): a State built through the private constructor with addDecl",
     "reject", ["META_COMMAND", "META_IMPORT"],
     bypass=["LINEAGE", "META_COMMAND", "META_IMPORT"])

case("probe4_hidden_name",
     FORGE + "\nelab \"#forge_hidden\" : command =>\n"
     "  forgeState (Name.mkNum `_private.CRRGCore.State 0 ++ `hiddenBump)\n#forge_hidden\n\n"
     "namespace Sub\n" + LEGIT_MOVE + TAIL,
     "Probe4: the forgery under a private-looking name",
     "reject", ["META_COMMAND", "META_IMPORT"],
     bypass=["LINEAGE", "META_COMMAND", "META_IMPORT"])

case("eval_command",
     sub("#eval (2 + 2 : Nat)\n" + LEGIT_MOVE),
     "meta-free lint: #eval can run CommandElabM code", "reject", ["META_COMMAND"])

case("macro_command",
     sub("macro \"cheat\" : term => `(sorry)\n" + LEGIT_MOVE),
     "meta-free lint: a user macro", "reject", ["META_COMMAND"])

case("skip_kernel_option",
     sub("set_option debug.skipKernelTC true\n" + LEGIT_MOVE),
     "lint: options that bypass the kernel are refused", "reject", ["FORBIDDEN_OPTION"])

case("import_tools",
     "import CRRGTools\n" + sub(LEGIT_MOVE),
     "lint: the runner's own tools (and Lean) are not importable", "reject", ["META_IMPORT"])

case("import_audit_transitive",
     "import CRRGExamples.Audit\n" + sub(LEGIT_MOVE),
     "lint: an allowed module that transitively imports CRRGTools", "reject", ["META_IMPORT"],
     imports=["CRRGExamples.Negatives", "CRRGExamples.Audit"])

case("import_not_allowed",
     "import CRRGExamples.Lineage\n" + sub(LEGIT_MOVE),
     "lint: a module outside the allow-list", "reject", ["IMPORT_NOT_ALLOWED"])

case("private_ctor_syntax",
     sub("def bump {root : Goal} (S : State root) : State root := { S with easierCount := 1000000 }\n"
         + LEGIT_MOVE),
     "G1 without meta: the private constructor is refused by the elaborator", "reject",
     ["COMPILE_ERROR"])

# ---------------------------------------------------------------- axioms
case("sorry_cover",
     sub("""def move : Move (E1 3) :=
  Move.close (E1 3) ⟨0, Nat.zero_lt_one⟩ sorry
"""),
     "a closure proved by sorry", "reject", ["AXIOM"], state="CRRGExamples.E1 3")

case("axiom_cheat",
     sub("""axiom cheat : False
def move : Move (E1 3) :=
  Move.close (E1 3) ⟨0, Nat.zero_lt_one⟩ cheat.elim
"""),
     "a closure proved from a new axiom", "reject", ["AXIOM"], state="CRRGExamples.E1 3")

case("native_decide",
     sub("""def move : Move (E1 8) :=
  Move.close (E1 8) ⟨0, Nat.zero_lt_one⟩ (show 8 % 2 = 0 by native_decide)
"""),
     "a closure through native_decide (trusts the compiler, not the kernel)", "reject", ["AXIOM"])

case("item5_classical_cert",
     sub("""noncomputable def classicalCert (p : Prop) : MechCert ⟨p⟩ where
  decide _ := @decide p (Classical.propDecidable p)
  sound_true h := @of_decide_eq_true p (Classical.propDecidable p) h
  sound_false h := @of_decide_eq_false p (Classical.propDecidable p) h
def move : Move (E1 8) :=
  Move.closeByComputation (E1 8) ⟨0, Nat.zero_lt_one⟩ (classicalCert _) rfl
"""),
     "review item 5: a classical 'decision procedure' cannot settle by evaluation", "reject",
     ["COMPILE_ERROR"])

# ---------------------------------------------------------------- D1 admission, restatements
case("d1_conflict_defeq",
     sub("""def OneEqTwo : Prop := 1 = 2
def move : Move F2 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new ⟨⟨OneEqTwo⟩, .top, trivial⟩]
  cover h := by
    have h1 : OneEqTwo := h _ (List.mem_singleton.mpr rfl)
    exact absurd (show 1 = 2 from h1) (by decide)
"""),
     "review item 4/6: a refuted obligation re-admitted under a definitional restatement",
     "reject", ["D1_CONFLICT"], state="CRRGExamples.F2")

case("d1_reuse_live_key",
     sub("""def move : Move F2 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new ⟨⟨R⟩, .top, trivial⟩]
  cover h := h _ (List.mem_singleton.mpr rfl)
"""),
     "a fresh copy of live registered keys (0 and 2) must reuse them", "reject", ["D1_REUSE"],
     state="CRRGExamples.F2")

case("classcap_restatement",
     sub("""def move : Move C0 :=
  Move.ofEdge C0 ⟨0, Nat.zero_lt_one⟩ ⟨ClassCap⟩ ⟨fun h n => (h n).symm⟩
"""),
     "the class-cap pattern: a definitional restatement of the live root", "reject",
     ["D1_REUSE"], state="CRRGExamples.C0")

case("item4_restate_measured_root",
     sub("""def move : Move G0 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new (rangeEntry (0, 9))]
  cover h := h _ (List.mem_singleton.mpr rfl)
"""),
     "review item 4: an exact restatement of the measured root", "reject", ["D1_REUSE"],
     state="CRRGExamples.G0")

case("readmit_by_key",
     sub("""def move : Move F2 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.old 1]
  cover h := by
    have h1 : holds F2.reg 1 := h (.old 1) (List.mem_singleton.mpr rfl)
    have hv : 1 < F2.reg.length := by decide
    have h12 : 1 = 2 := (holds_iff hv).mp h1
    exact absurd h12 (by decide)
"""),
     "example 5: a refuted obligation re-admitted by its key", "reject",
     ["COMMIT_REJECT:learnedConflict"], state="CRRGExamples.F2")

case("dead_root",
     sub("""def move : Move dead :=
  Move.ofEdge dead ⟨0, Nat.zero_lt_one⟩ ⟨1 = 2 ∧ True⟩ ⟨fun h => h.1⟩
"""),
     "review item 6: a move on a route whose root is refuted", "reject",
     ["COMMIT_REJECT:rootRefuted"], state="CRRGExamples.dead")

# ---------------------------------------------------------------- R1 on definitions
R1_DEFS = """namespace Sealed
def Bound (n : Nat) : Prop := n + 0 = n
end Sealed
def NewQuantity (n : Nat) : Prop := 0 + n = n
def Leaf : Prop := ∀ n, NewQuantity n
"""
R1_MOVE = """def move : Move (H0 (∀ n, Sealed.Bound n)) :=
  Move.ofEdge (H0 (∀ n, Sealed.Bound n)) ⟨0, Nat.zero_lt_one⟩ ⟨Leaf⟩
    ⟨fun _ _ => rfl⟩
"""
R1_STATE = "CRRGExamples.H0 (∀ n, Sub.Sealed.Bound n)"


def r1(agreements):
    return {"sealed": ["Sub.Sealed"], "agreements": agreements}


case("r1_missing", sub(R1_DEFS + R1_MOVE),
     "R1: a new definition with no agreement lemma", "reject", ["R1"],
     state=R1_STATE, r1=r1([]))

case("r1_vacuous",
     sub(R1_DEFS + "theorem vac (n : Nat) : NewQuantity n → True := fun _ => trivial\n" + R1_MOVE),
     "R1: a vacuous 'agreement' (→ True)", "reject", ["R1"], state=R1_STATE, r1=r1(["Sub.vac"]))

case("r1_fake_conjunction",
     sub(R1_DEFS + """theorem fake (n : Nat) :
    (NewQuantity n → NewQuantity n) ∧ (Sealed.Bound n → Sealed.Bound n) := ⟨id, id⟩
""" + R1_MOVE),
     "review item 8: a conjunction of tautologies mentioning both names", "reject", ["R1"],
     state=R1_STATE, r1=r1(["Sub.fake"]))

# ---------------------------------------------------------------- legitimate moves
case("r1_agree", sub(R1_DEFS + """theorem agree (n : Nat) : NewQuantity n ↔ Sealed.Bound n :=
  ⟨fun _ => rfl, fun _ => Nat.zero_add n⟩
""" + R1_MOVE),
     "R1: a typed agreement lemma (↔ with the sealed definition)", "accept", [],
     tag="notCertifiedEasier", state=R1_STATE, r1=r1(["Sub.agree"]))

case("split_ab", sub("""def split : Split ((S0 (1 = 1) (2 = 2)).leafGoal ⟨0, Nat.zero_lt_one⟩) where
  children := [⟨1 = 1⟩, ⟨2 = 2⟩]
  discharge h := ⟨h ⟨1 = 1⟩ (by simp), h ⟨2 = 2⟩ (by simp)⟩
def move : Move (S0 (1 = 1) (2 = 2)) := Move.ofSplit _ ⟨0, Nat.zero_lt_one⟩ split
"""),
     "example 1: P = A ∧ B split into {A, B}", "accept", [], tag="notCertifiedEasier",
     state="CRRGExamples.S0 (1 = 1) (2 = 2)")

case("range_split", sub("""def move : Move G0 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new (rangeEntry (0, 4)), .new (rangeEntry (5, 9))]
  cover h := (rangeSplit Pt 0 4 9).discharge fun c hc => by
    simp [rangeSplit] at hc
    rcases hc with rfl | rfl
    · exact h (.new (rangeEntry (0, 4))) (by simp)
    · exact h (.new (rangeEntry (5, 9))) (by simp)
"""),
     "example 6: an owner-pinned range split (rung 3)", "accept", [], tag="certifiedEasier",
     state="CRRGExamples.G0")

case("comments_mention_meta", sub("""/-! This file does not `import Lean`, and uses no `elab`, `macro`, `syntax`,
`run_cmd`, `initialize` or `#eval`. /- nested: set_option debug.skipKernelTC true -/ -/
-- a line comment naming #eval and elab
def note : String := "elab macro #eval import Lean"
""" + LEGIT_MOVE),
     "lint false-positive control: meta words inside comments and strings are not commands",
     "accept", [], tag="certifiedEasier")

case("close_by_computation", sub(LEGIT_MOVE),
     "example 3: rung 2 settled in the kernel", "accept", [], tag="certifiedEasier")

case("item4_growth", sub("""def move : Move G0 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new (rangeEntry (0, 19))]
  cover h := by
    have hp : rangeFam.claim (0, 19) := h _ (List.mem_singleton.mpr rfl)
    show ∀ x, 0 ≤ x → x ≤ 9 → Pt x
    exact fun x h0 h9 => hp x h0 (by omega)
"""),
     "review item 4: growth is sound and admitted, but earns no credit", "accept", [],
     tag="notCertifiedEasier", state="CRRGExamples.G0")

case("item4_grow_from_top", sub("""def move : Move (State.initial (rangeGoal Pt 0 9) fams) where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new (rangeEntry (0, 19))]
  cover h := by
    have hp : rangeFam.claim (0, 19) := h _ (List.mem_singleton.mpr rfl)
    show ∀ x, 0 ≤ x → x ≤ 9 → Pt x
    exact fun x h0 h9 => hp x h0 (by omega)
"""),
     "review item 4 (original probe): top → sized was credited; now it is not", "accept", [],
     tag="notCertifiedEasier",
     state="CRRGCore.State.initial (CRRGCore.rangeGoal CRRGExamples.Pt 0 9) CRRGExamples.fams")

case("grow_then_shrink", sub("""def move : Move G1g where
  pos := ⟨0, by decide⟩
  children := [.old 1, .new (rangeEntry (5, 19))]
  cover h := by
    have hv : 1 < G1g.reg.length := by decide
    have h1 : rangeFam.claim (0, 4) := (holds_iff hv).mp (h (.old 1) (by simp))
    have h2 : rangeFam.claim (5, 19) := h (.new (rangeEntry (5, 19))) (by simp)
    show ∀ x, 0 ≤ x → x ≤ 19 → Pt x
    intro x h0 h19
    by_cases hx : x ≤ 4
    · exact h1 x h0 hx
    · exact h2 x (by omega) h19
"""),
     "record-low rule: after growing [0,4] to [0,19], shrinking back (reusing key 1, as D1 "
     "requires) is a local decrease but not below the record", "accept", [],
     tag="notCertifiedEasier", state="CRRGExamples.G1g")

case("propositional_restatement", sub("""def move : Move Q2 where
  pos := ⟨0, Nat.zero_lt_one⟩
  children := [.new ⟨⟨swapped 11⟩, .top, trivial⟩]
  cover h := by
    have h1 : swapped 11 := h _ (List.mem_singleton.mpr rfl)
    exact absurd ((direct_iff_swapped 11).mpr h1) (by unfold direct; decide)
"""),
     "review item 8 (known limit): a propositional restatement of a refuted claim passes D1; "
     "it is caught only after a detector supplies the implication to State.learn (Negatives 4b)",
     "accept", [], tag="notCertifiedEasier", state="CRRGExamples.Q2",
     note="documented limit, not a runner guarantee: see RUNNER.md")


# ---------------------------------------------------------------- guard-fields rule
# The family is synthetic: families/demo.json, edge "toy-edge". Its Lean model is
# CRRGExamples.CruxFamily.guard, and CRRGExamples.FamilyAgreement checks that the two agree.
DEMO_INST = {"mode": 1, "m": 11, "k": 4, "lo": 20, "hi": 30}
DEMO_OK = {
    "mode_1": {},
    "m_odd": {},
    "m_certified": {"evidence": "certificate for m = 11 (synthetic)"},
    "k_divides": {},
    "k_range": {},
    "x_window": {"x": 25},
    "profile": {"witness": "w-1", "minDeg": 2, "mass": 36},
}


def demo(instance=None, arrow="toy-edge", **changes):
    fields = {k: dict(v) for k, v in DEMO_OK.items()}
    for k, v in changes.items():
        if v is None:
            fields.pop(k)
        else:
            fields[k] = v
    return {"family": "demo", "arrow": arrow, "instance": dict(DEMO_INST, **(instance or {})),
            "fields": fields}


case("guard_accept", sub(LEGIT_MOVE),
     "synthetic family: a contract discharges every guard field of the shared edge", "accept", [],
     tag="certifiedEasier", guard_claim=demo())

case("guard_missing_field", sub(LEGIT_MOVE),
     "synthetic family: the contract omits the window field", "reject", ["GUARD_FIELD_MISSING"],
     guard_claim=demo(x_window=None))

case("guard_data_no_evidence", sub(LEGIT_MOVE),
     "synthetic family: a data obligation (the certificate for m) claimed without an evidence "
     "reference", "reject", ["GUARD_FIELD_MISSING"], guard_claim=demo(m_certified={}))

case("guard_window_fails", sub(LEGIT_MOVE),
     "synthetic family: the contract's value x = 12 lies below its window [20, 30]", "reject",
     ["GUARD_FIELD_FAILS"], guard_claim=demo(x_window={"x": 12}))

case("guard_over_budget", sub(LEGIT_MOVE),
     "synthetic family: a profile with mass 41, one past the budget", "reject",
     ["GUARD_FIELD_FAILS"], guard_claim=demo(profile={"witness": "w-2", "minDeg": 2, "mass": 41}))

case("guard_wrong_mode", sub(LEGIT_MOVE),
     "synthetic family: a consumer in mode 2 claims the edge", "reject", ["GUARD_FIELD_FAILS"],
     guard_claim=demo(instance={"mode": 2}))

case("guard_divides_fails", sub(LEGIT_MOVE),
     "synthetic family: the step k = 5 does not divide m + 1 = 12 (the range field still holds)",
     "reject", ["GUARD_FIELD_FAILS"], guard_claim=demo(instance={"k": 5}))

case("guard_joint_split", sub(LEGIT_MOVE),
     "synthetic family: the joint profile field typed as two separate existentials (one witness "
     "with the degree, another with the mass)", "reject", ["GUARD_JOINT_SPLIT"],
     guard_claim=demo(profile=[{"witness": "w-a", "minDeg": 2}, {"witness": "w-b", "mass": 36}]))

case("guard_unknown_edge", sub(LEGIT_MOVE),
     "synthetic family: the contract names an edge the family does not register", "reject",
     ["GUARD_UNKNOWN_EDGE"], guard_claim=demo(arrow="no-such-edge"))


def main():
    if os.path.isdir(TESTS):
        shutil.rmtree(TESTS)
    for name, c in CASES.items():
        d = os.path.join(TESTS, name)
        os.makedirs(d)
        open(os.path.join(d, "Submission.lean"), "w", encoding="utf-8").write(c["source"])
        man = {"submission": "Submission.lean", "imports": c["imports"], "state": c["state"],
               "move": c["move"]}
        if c["r1"]:
            man["r1"] = c["r1"]
        if c["guard_claim"]:
            man["guard_claim"] = c["guard_claim"]
        json.dump(man, open(os.path.join(d, "manifest.json"), "w", encoding="utf-8"),
                  indent=2, ensure_ascii=False)
        exp = {"origin": c["origin"], "verdict": c["verdict"], "reasons": c["reasons"]}
        if c["tag"]:
            exp["tag"] = c["tag"]
        if c["bypass"] is not None:
            exp["reasons_if_lint_bypassed"] = sorted(c["bypass"])
        if c["note"]:
            exp["note"] = c["note"]
        json.dump(exp, open(os.path.join(d, "expect.json"), "w", encoding="utf-8"),
                  indent=2, ensure_ascii=False)
    print(f"wrote {len(CASES)} cases to {TESTS}")


if __name__ == "__main__":
    main()
