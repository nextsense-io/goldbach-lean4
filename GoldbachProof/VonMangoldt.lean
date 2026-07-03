/-
B5: Von Mangoldt exponential sum — definitions and foundational bounds.

S_Λ(α, N) = ∑_{n<N} Λ(n) · e(2πinα) is the von Mangoldt exponential sum,
the key analytic object of the Hardy–Littlewood circle method for Goldbach.
ψ(N) = ∑_{n<N} Λ(n) is the Chebyshev psi function (truncated to n < N).

Theorems (all axiom-free):
  #41: vonMangoldt_exp_sum_at_zero  — S_Λ(0, N) = ψ(N)
  #42: vonMangoldt_exp_sum_norm_le  — ‖S_Λ(α, N)‖ ≤ ψ(N)
  #43: vonMangoldt_chebyshev_le     — ψ(N) ≤ N · log N
  #44: vonMangoldt_exp_sum_bound    — ‖S_Λ(α, N)‖ ≤ N · log N

Proved by hand (Cipher), 2026-07-02.
-/
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Complex Real ArithmeticFunction Finset

set_option maxHeartbeats 400000

namespace GoldbachBridge

/-- The von Mangoldt exponential sum:
    S_Λ(α, N) = ∑_{n < N} Λ(n) · e(2πinα).
    This is the fundamental analytic object of the Hardy–Littlewood circle method
    for Goldbach. On major arcs near a/q, S_Λ(α) ≈ (μ(q)/φ(q)) · v(α − a/q)
    where v(β) = ∑_{m≤N} e(mβ). -/
noncomputable def vonMangoldt_exp_sum (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N,
    (vonMangoldt n : ℝ) * Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * ↑α)

/-- The Chebyshev ψ-function (truncated): ψ(N) = ∑_{n < N} Λ(n). -/
noncomputable def psi (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (vonMangoldt n : ℝ)

/-- ψ(N) is nonneg (since Λ ≥ 0). -/
lemma psi_nonneg (N : ℕ) : 0 ≤ psi N :=
  Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)

private lemma exp_arg_norm_one (n : ℕ) (α : ℝ) :
    ‖Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * ↑α)‖ = 1 := by
  have hrw : 2 * ↑Real.pi * Complex.I * ↑n * ↑α =
      ↑(2 * Real.pi * (↑n : ℝ) * α) * Complex.I := by push_cast; ring
  rw [hrw, Complex.norm_exp_ofReal_mul_I]

/-- **Theorem #41. Von Mangoldt sum at zero** (B5).
    S_Λ(0, N) = ψ(N): at α = 0 every exponential factor is 1, so the sum
    reduces to the Chebyshev ψ-function value ∑_{n<N} Λ(n). -/
theorem vonMangoldt_exp_sum_at_zero (N : ℕ) :
    vonMangoldt_exp_sum N 0 = ↑(psi N) := by
  unfold vonMangoldt_exp_sum psi
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp [mul_zero, Complex.exp_zero]

/-- **Theorem #42. Von Mangoldt sum norm bound** (B5).
    ‖S_Λ(α, N)‖ ≤ ψ(N): the triangle inequality collapses to ψ(N) because
    each exponential factor e(nα) lies on the unit circle (norm = 1)
    and Λ(n) ≥ 0. -/
theorem vonMangoldt_exp_sum_norm_le (N : ℕ) (α : ℝ) :
    ‖vonMangoldt_exp_sum N α‖ ≤ psi N := by
  unfold vonMangoldt_exp_sum psi
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro n _
  rw [norm_mul, exp_arg_norm_one, mul_one,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg]

/-- **Theorem #43. Chebyshev ψ(N) ≤ N · log N** (B5).
    Classical trivial upper bound: Λ(n) ≤ log n ≤ log N for each n < N,
    so ψ(N) ≤ N · log N. -/
theorem vonMangoldt_chebyshev_le (N : ℕ) : psi N ≤ (N : ℝ) * Real.log N := by
  unfold psi
  rcases Nat.eq_zero_or_pos N with rfl | hN_pos
  · simp
  · have h1N : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    apply le_trans (Finset.sum_le_sum (fun n _ => vonMangoldt_le_log))
    calc ∑ n ∈ Finset.range N, Real.log ↑n
        ≤ ∑ _n ∈ Finset.range N, Real.log N := by
          apply Finset.sum_le_sum
          intro n hn
          rcases Nat.eq_zero_or_pos n with rfl | hn_pos
          · -- n = 0: log 0 = 0 ≤ log N (since N ≥ 1)
            simp only [Nat.cast_zero, Real.log_zero]
            exact Real.log_nonneg h1N
          · -- n ≥ 1: log n ≤ log N since n ≤ N
            exact Real.log_le_log (Nat.cast_pos.mpr hn_pos)
              (by exact_mod_cast (Finset.mem_range.mp hn).le)
      _ = N * Real.log N := by simp [Finset.sum_const, nsmul_eq_mul]

/-- **Theorem #44. Von Mangoldt exponential sum bound** (B5).
    ‖S_Λ(α, N)‖ ≤ N · log N: triangle bound (#42) + Chebyshev bound (#43). -/
theorem vonMangoldt_exp_sum_bound (N : ℕ) (α : ℝ) :
    ‖vonMangoldt_exp_sum N α‖ ≤ (N : ℝ) * Real.log N :=
  le_trans (vonMangoldt_exp_sum_norm_le N α) (vonMangoldt_chebyshev_le N)

/-- **Theorem #48. Chebyshev ψ is strictly positive for N ≥ 3** (B5).
    ψ(N) > 0 whenever N ≥ 3: the term Λ(2) = log 2 > 0 appears in the sum
    since 2 ∈ range N, and all other terms are nonneg. -/
theorem psi_pos_of_three_le (N : ℕ) (hN : 3 ≤ N) : 0 < psi N := by
  unfold psi
  rw [Finset.sum_pos_iff_of_nonneg (fun n _ => vonMangoldt_nonneg)]
  exact ⟨2, Finset.mem_range.mpr (by omega), by
    rw [vonMangoldt_apply_prime Nat.prime_two]; exact Real.log_pos one_lt_two⟩

/-- **Theorem #45. Chebyshev ψ is monotone** (B5).
    ψ(N) ≤ ψ(M) whenever N ≤ M, since Λ(n) ≥ 0 for all n and range N ⊆ range M. -/
theorem psi_mono (N M : ℕ) (h : N ≤ M) : psi N ≤ psi M := by
  unfold psi
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
  intro n _ _
  exact vonMangoldt_nonneg

end GoldbachBridge
