# goldbach-lean4

**Axiom-free Lean 4 formalization of the theoretical ingredients of a sparse-eigensolver approach to Goldbach verification.**

Companion repository to *"Scalable Goldbach Verification via Sparse Hamiltonian Eigensolvers: An Axiom-Free Lean 4 Formalization"* (J. Berent, NextSense Inc., 2026, submitted).

## Contents

| Module | Theorems | Subject |
|--------|----------|---------|
| `GoldbachProof/Basic.lean` | core defs + bridges | `primesUpTo`, `goldbachPairs`, `E_gold`; `E_gold_pos_implies_goldbach` and converse `exists_pair_implies_E_gold_pos` (witness pair ⇒ machine-checked `E_gold N > 0`) |
| `GoldbachProof/Jensen.lean` | 10 | Convexity of `1/(x−c)`, weighted Jensen inequality (uniform + general weights) |
| `GoldbachProof/CourantFischer.lean` | 26 | Courant–Fischer-style minimax ingredients, eigenvalue ordering, rank-1 perturbation interlacing via dimension intersection — fills a gap in Mathlib spectral theory |
| `GoldbachProof/CauchyInterlacing.lean` | 14 | Cauchy interlacing for Hermitian matrices (rank-1 case fully proved) |
| `GoldbachProof/APSpread.lean` | 11 | Arithmetic-progression equidistribution bound scaffolding |
| `GoldbachProof/PNTTarget.lean` | research | PNT→Goldbach bridge scaffolding; carries one explicit research axiom (`pnt_in_ap`) and is **deliberately excluded from the default build** |

**Default build: 0 custom axioms, 0 `sorry`.** Verify any theorem's axiom footprint with `#print axioms <name>` — only Lean foundations (`propext`, `Quot.sound`, `Classical.choice`) appear.

## Build

Requires [elan](https://github.com/leanprover/elan). Toolchain and Mathlib revision are pinned by `lean-toolchain` / `lake-manifest.json`.

```bash
lake exe cache get   # fetch Mathlib build cache
lake build           # builds the axiom-free GoldbachProof library
```

## Status

- All five custom axioms of the February 2026 draft were eliminated by April 21, 2026 (proved or removed).
- Numerical verification code (sparse Lanczos eigensolver, dense scaling study) lives in the companion paper's artifact; this repository contains the formal mathematics.

## License

Apache 2.0 (matching Mathlib).
