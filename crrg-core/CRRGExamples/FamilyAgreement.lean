import CRRGExamples.FamilyDemoJson

/-!
# JSON–Lean guard agreement for a crux family (synthetic example)

`families/demo.json` is the runner-facing record of the shared edge's guard (what
`runner/guard_fields.py` checks a consuming contract against), and `CruxFamily.guard` is the Lean
guard. `families/gen_lean.py` generates `FamilyDemoJson.lean` from the JSON, including the JSON
checker's own verdicts on fixed sample instances, and `build.sh` fails if that file is stale. The
theorems below, all checked by `decide`, tie the two together **mechanically**: the same field ids
and kinds in the same order, the same numeric constants, and the same verdict on every sample.
-/

namespace CRRGExamples.FamilyAgreement

open CRRGExamples.CruxFamily CRRGExamples.FamilyDemoJson

/-- The JSON id of each Lean guard field. -/
def Field.jsonId : Field → String
  | .mode1 => "mode_1" | .mOdd => "m_odd" | .mCertified => "m_certified" | .kDvd => "k_divides"
  | .kRange => "k_range" | .xWindow => "x_window" | .profile => "profile"

/-- The JSON kind of each Lean guard field: a data obligation is an `Option` the consumer fills, and
the profile is joint (one witness carries both of its values). -/
def Field.jsonKind : Field → String
  | .mCertified => "data"
  | .profile => "joint"
  | _ => "decidable"

/-- *computed*: the shared edge's fields agree, in order, with kinds. -/
theorem fields_agree :
    edgeFields = allFields.map (fun f => (Field.jsonId f, Field.jsonKind f)) := by decide

/-- *computed*: every numeric constant in the JSON checks is the Lean model's constant. -/
theorem numbers_agree :
    edgeNumbers = [("mode_1", "mode", "==", modeReq), ("profile", "minDeg", ">=", minDegLow),
      ("profile", "mass", "<=", massBudget)] := by decide

/-- *computed*: on every sample, `CruxFamily.guard` gives the JSON checker's verdict. -/
theorem samples_agree :
    edgeSamples.all (fun s => decide (guard s.2.1) == s.2.2) = true := by decide

/-- *computed*: the samples are not vacuous: both verdicts occur. -/
theorem samples_both_verdicts :
    (edgeSamples.map (·.2.2)).contains true = true ∧
      (edgeSamples.map (·.2.2)).contains false = true := by decide

end CRRGExamples.FamilyAgreement
