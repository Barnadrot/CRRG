import CRRGCore

/-!
# The certified core carries no metaprogramming (review item 2)

`CRRGCore` imports only Lean's prelude, not the `Lean` meta framework. A file that imports only
the core cannot reach `addDecl`, so the forgery of `CRRGExamples/Lineage.lean` needs an extra
`import Lean`, which the runner forbids in submitted files.
-/

/-- error: Unknown identifier `Lean.addDecl` -/
#guard_msgs in
#check Lean.addDecl
