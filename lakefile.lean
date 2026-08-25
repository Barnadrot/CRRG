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

lean_lib «Test» where
  srcDir := "."
