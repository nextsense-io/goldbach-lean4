import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-!
# Frobenius Norm Eigenvalue Identity (Theorem #17)

For a real symmetric (Hermitian) matrix A:
  ∑_{ij} A_{ij}² = ∑_i λᵢ²

Proof via the spectral theorem: A = U·diag(λ)·Uᵀ, so
  trace(A²) = trace(U·diag(λ²)·Uᵀ) = trace(diag(λ²)) = ∑ λᵢ²
and trace(A²) = ∑_{ij} A_{ij}² for symmetric A.

Proved by hand 2026-06-24 (theorem #17 in the Goldbach proof chain).
STATUS: AXIOM-FREE
-/

open Matrix Unitary

namespace SpectralTargets

/-- The Frobenius norm squared of a real Hermitian matrix equals the sum of squares
    of its eigenvalues: ∑_{ij} A_{ij}² = ∑_i λᵢ². -/
theorem frobenius_norm_eigenvalues {m : ℕ} [NeZero m] [DecidableEq (Fin m)]
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian) :
    ∑ i : Fin m, ∑ j : Fin m, A i j ^ 2 =
    ∑ i : Fin m, hA.eigenvalues i ^ 2 := by
  -- Step 1: LHS = trace(A * A) via symmetry A j i = A i j
  have h_sym : ∀ a b : Fin m, A b a = A a b := fun a b => by
    have h := congr_fun (congr_fun hA b) a
    simp only [conjTranspose_apply, star_trivial] at h
    exact h.symm
  have h_lhs : ∑ i : Fin m, ∑ j : Fin m, A i j ^ 2 = (A * A).trace := by
    simp only [Matrix.trace, Matrix.diag, mul_apply, sq]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [h_sym a b]
  -- Step 2: trace(A * A) = ∑ λᵢ² via spectral theorem
  have h_rhs : (A * A).trace = ∑ i : Fin m, hA.eigenvalues i ^ 2 := by
    set D := diagonal (RCLike.ofReal ∘ hA.eigenvalues : Fin m → ℝ)
    set U := hA.eigenvectorUnitary
    -- A * A = conjStarAlgAut U (D * D) via map_mul
    have h_sq : A * A = conjStarAlgAut ℝ _ U (D * D) := by
      rw [hA.spectral_theorem]
      exact ((conjStarAlgAut ℝ _ U).map_mul D D).symm
    -- Expand and use trace invariance under unitary conjugation
    rw [h_sq, conjStarAlgAut_apply, trace_mul_cycle,
        Unitary.coe_star_mul_self, one_mul,
        diagonal_mul_diagonal, trace_diagonal]
    -- Simplify RCLike.ofReal on ℝ (identity coercion)
    simp [Function.comp, sq]
  rw [h_lhs, h_rhs]

#check @frobenius_norm_eigenvalues

end SpectralTargets
