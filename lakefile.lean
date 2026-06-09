import Lake
open Lake DSL

package goldbach_proof where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib GoldbachProof where
  srcDir := "."

lean_exe goldbach_proof where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
