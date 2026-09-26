import CRRGCore.Basic
import CRRGCore.Easier
import CRRGCore.Guarded
import CRRGCore.State
import CRRGCore.Route

/-!
# CRRGCore — a closed CRRG core (Phase 0)

The certified modules only: `Basic`, `Easier`, `Guarded`, `State`, `Route`. They import Lean core
(`Init`) only, so `import CRRGCore` exposes no metaprogramming API (`Lean.addDecl`, `elab`
support libraries). The meta tools live in the separate library `CRRGTools`, which submitted files
must not import (see README, "Runner obligations").
-/
