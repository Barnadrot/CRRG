import Lake
open Lake DSL

/-
CRRG core, Phase 0 ("close CRRG fully"). Lean core only: no Mathlib, no other dependency.
-/
package «crrg-core» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib «CRRGCore» where
  srcDir := "."

/- Meta tools (seal, lineage audit, admission checks, R1, rung-2 audit). Imports `Lean`.
   Used by the gate runner; never imported by the certified core. -/
lean_lib «CRRGTools» where
  srcDir := "."

lean_lib «CRRGExamples» where
  srcDir := "."
