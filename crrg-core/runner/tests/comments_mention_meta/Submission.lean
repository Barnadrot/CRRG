import CRRGExamples.Negatives
open CRRGCore CRRGExamples
namespace Sub
/-! This file does not `import Lean`, and uses no `elab`, `macro`, `syntax`,
`run_cmd`, `initialize` or `#eval`. /- nested: set_option debug.skipKernelTC true -/ -/
-- a line comment naming #eval and elab
def note : String := "elab macro #eval import Lean"
def move : Move (E1 8) :=
  Move.closeByComputation (E1 8) ⟨0, Nat.zero_lt_one⟩ (evenCert 8) rfl
end Sub
