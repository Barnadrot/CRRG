import Lake
open Lake DSL

package «CRRG» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib «CRRG» where
  srcDir := "."

-- Test support, shipped for downstream adapters (see `CRRGTest.lean`).
-- A separate library on purpose: `import CRRG` does not pull it in, so the
-- shipped core semantics stay Lean-core-only and unencumbered.
lean_lib «CRRGTest» where
  srcDir := "."

lean_lib «Test» where
  srcDir := "."
