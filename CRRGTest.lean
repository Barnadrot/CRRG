import CRRGTest.ExpectFailure

/-!
# CRRGTest — test support, shipped for downstream adapters

CRRG is an anti-reward-hacking system, so its most important tests are the ones
that assert a construction is **rejected**. A downstream `ResearchGraph` adapter
needs exactly the same discipline — that a weakened leaf, an incomplete split,
or a dropped guard branch fails to compile — and until this library existed the
harness for writing those tests lived inside CRRG's own test suite, where no
consumer could reach it.

This is a **separate** Lake library from `CRRG`. `import CRRG` does not pull it
in, and nothing in the core depends on it, so the shipped semantics stay exactly
as dependency-light as §2.2 requires. A consumer opts in:

```lean
require CRRG from ...

lean_lib «MyGraph» where
  srcDir := "."
```

```lean
import CRRGTest.ExpectFailure

#expect_failure
theorem weakenedLeaf : Edge myParent myEasierChild := ...
```

Like the core, this library depends on Lean core only.
-/
