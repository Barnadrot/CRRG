import Lake
open Lake DSL

/-! The first slice of the faithful classical CRRG. A PARALLEL library: it may import Mathlib
(trusted, pinned to c5ea00351c). It depends on crrg-core by path, for the bridge to the list-based
`DMLt` and for the crux-family model. Nothing in crrg-core depends on it. -/

package «crrg-classical»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

require «crrg-core» from ".." / "crrg-core"

@[default_target]
lean_lib CRRGClassical
