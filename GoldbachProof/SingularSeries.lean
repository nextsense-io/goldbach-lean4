/-
Singular series 𝔖(N) positivity — key theorems for the Goldbach circle method.

The singular series is 𝔖(N) = ∑_{q squarefree} c_q(-N)/φ(q)²
                              = ∏_p (1 + c_p(N)/(p-1)²)  [Euler product, N even]

This file proves:
  - eulerFactor_pos  (#19): Each factor 1 + c_p(N).re/(p-1)² > 0 for prime p, even N
  - (Future) singularSeries_pos: The full product 𝔖(N) > 0

The positivity chain:
  - p = 2: N even → 2 | N → c_2(N) = 1 → factor = 2 > 0
  - p | N (p odd prime): c_p(N) = p-1 → factor = p/(p-1) > 0
  - p ∤ N (p odd prime, p ≥ 3): c_p(N) = -1 → factor = 1 - 1/(p-1)² > 0
-/
import GoldbachProof.RamanujanHölder

open ArithmeticFunction

namespace GoldbachBridge

-- ============================================================
-- THEOREM #19: Euler factor positivity (real-valued form)
-- ============================================================

/-- **Euler factor positivity** (singular series, Theorem #19):
    For prime p and even N (i.e. 2 | N.natAbs), the Euler product factor
    `1 + c_p(N).re / (p-1)²` is strictly positive.

    Cases:
    - p = 2: 2 | N → c_2(N) = 1 → factor = 2 > 0
    - p | N.natAbs (p odd): c_p(N) = p-1 → factor = p/(p-1) > 0
    - p ∤ N.natAbs (p odd, hence p ≥ 3): c_p(N) = -1 → factor = (p-2)p/(p-1)² > 0

    Proved 2026-06-25. -/
theorem eulerFactor_pos (p : ℕ) (hp : p.Prime) (N : ℤ) (hN : (2 : ℕ) ∣ N.natAbs) :
    (0 : ℝ) < 1 + (ramanujanSumC p N).re / ((p : ℝ) - 1) ^ 2 := by
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    linarith [show (1 : ℝ) < (p : ℝ) from by exact_mod_cast hp.one_lt]
  have hp1_sq_pos : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by positivity
  by_cases hdvd : p ∣ N.natAbs
  · -- c_p(N) = (p:ℂ) - 1, so c_p(N).re = (p:ℝ) - 1
    have hre : (ramanujanSumC p N).re = (p : ℝ) - 1 := by
      rw [ramanujanSumC_prime p hp N, if_pos hdvd]
      simp [Complex.sub_re, Complex.one_re]
    rw [hre]
    have : 1 + ((p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 = (p : ℝ) / ((p : ℝ) - 1) := by
      field_simp; ring
    linarith [div_pos (show (0 : ℝ) < p from by exact_mod_cast hp.pos) hp1_pos]
  · -- c_p(N) = -1, so c_p(N).re = -1
    have hre : (ramanujanSumC p N).re = -1 := by
      rw [ramanujanSumC_prime p hp N, if_neg hdvd]
      simp [Complex.neg_re, Complex.one_re]
    rw [hre]
    -- Since p is prime and p ∤ N.natAbs but 2 | N.natAbs, p ≠ 2 (else 2 | N.natAbs → p | N.natAbs)
    have hp2 : p ≠ 2 := fun h => by subst h; exact hdvd hN
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hp2_pos : (0 : ℝ) < (p : ℝ) - 2 := by
      have hlt : (2 : ℕ) < p := by omega
      have : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hlt
      linarith
    have hrw : 1 + (-1 : ℝ) / ((p : ℝ) - 1) ^ 2 = ((p : ℝ) - 2) * p / ((p : ℝ) - 1) ^ 2 := by
      field_simp; ring
    rw [hrw]
    exact div_pos (mul_pos hp2_pos (by exact_mod_cast hp.pos)) hp1_sq_pos

end GoldbachBridge
