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

-- Mathlib upstream PR candidates (not part of the Goldbach proof chain).
lean_lib UpstreamPR1 where
  srcDir := "upstream"
  roots := #[`Mathlib_PR1_RayleighDecomposition]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
