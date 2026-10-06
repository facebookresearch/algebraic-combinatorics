/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Lake
open Lake DSL

package «algcomb» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.34.1"

require REPL from git
  "https://github.com/leanprover-community/repl" @ "v4.34.0"

require checkdecls from git
  "https://github.com/PatrickMassot/checkdecls.git"

@[default_target]
lean_lib «AlgebraicCombinatorics» where
  globs := #[.submodules `AlgebraicCombinatorics]
