/-
Singular series 𝔖(N) positivity — key theorems for the Goldbach circle method.

The singular series is 𝔖(N) = ∑_{q squarefree} c_q(-N)/φ(q)²
                              = ∏_p (1 + c_p(N)/(p-1)²)  [Euler product, N even]

This file proves:
  - eulerFactor_pos  (#19): Each factor 1 + c_p(N).re/(p-1)² > 0 for prime p, even N
  - singularSeries_product_pos (#20): Finite partial product > 0
  - singularSeries_summable (#22): Euler factor series is absolutely summable (N ≠ 0)
  - singularSeries_multipliable (#23): The Euler product converges (N ≠ 0)
  - singularSeries_pos (#24): The full product 𝔖(N) > 0 (N ≠ 0 even)

The positivity chain:
  - p = 2: N even → 2 | N → c_2(N) = 1 → factor = 2 > 0
  - p | N (p odd prime): c_p(N) = p-1 → factor = p/(p-1) > 0
  - p ∤ N (p odd prime, p ≥ 3): c_p(N) = -1 → factor = 1 - 1/(p-1)² > 0

Key summability argument:
  - For p ∤ N: |c_p(N).re/(p-1)²| = 1/(p-1)² ≤ 4/p² (since p-1 ≥ p/2 for p ≥ 2)
  - Primes dividing N are finitely many (exceptional set)
  - ∑_{p prime} 4/p² < ∑_{n:ℕ} 4/n² < ∞ (p-series, exponent 2 > 1)
  - So ∑ |c_p(N).re/(p-1)²| converges; 𝔖(N) = exp(∑ log(factor)) > 0
-/
import GoldbachProof.RamanujanHölder
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

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

-- ============================================================
-- THEOREM #20: Finite Euler product positivity
-- ============================================================

/-- **Finite singular series product positivity** (Theorem #20):
    For any finite set S of primes and even N, the partial Euler product
    `∏ p ∈ S, (1 + c_p(N).re / (p-1)²)` is strictly positive.

    Direct corollary of `eulerFactor_pos` and `Finset.prod_pos`.
    This is the key intermediate step toward the full singular series
    positivity 𝔖(N) > 0 needed for the Hardy-Littlewood lower bound.

    Proved 2026-06-26. -/
theorem singularSeries_product_pos (N : ℤ) (hN : (2 : ℕ) ∣ N.natAbs)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (0 : ℝ) < ∏ p ∈ S, (1 + (ramanujanSumC p N).re / ((p : ℝ) - 1) ^ 2) := by
  apply Finset.prod_pos
  intro p hp
  exact eulerFactor_pos p (hS p hp) N hN

-- ============================================================
-- HELPER: gcd multiplicativity for coprime moduli
-- ============================================================

/-- For coprime m, n: gcd(m*n, k.natAbs) = gcd(m, k.natAbs) * gcd(n, k.natAbs). -/
private lemma gcd_natAbs_mul (m n : ℕ) (hcop : m.Coprime n) (k : ℤ) :
    Nat.gcd (m * n) k.natAbs = Nat.gcd m k.natAbs * Nat.gcd n k.natAbs :=
  hcop.mul_gcd k.natAbs

-- ============================================================
-- HELPER: μ multiplicativity for coprime arguments
-- ============================================================

/-- For coprime a, b: μ(a*b) = μ(a) * μ(b). -/
private lemma moebius_mul_of_coprime (a b : ℕ) (hcop : a.Coprime b) :
    (ArithmeticFunction.moebius (a * b) : ℂ) =
    (ArithmeticFunction.moebius a : ℂ) * (ArithmeticFunction.moebius b : ℂ) := by
  have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  exact_mod_cast h

-- ============================================================
-- HELPER: Euler factor absolute value bound for p ∤ N
-- ============================================================

/-- For prime p not dividing N.natAbs: |c_p(N).re / (p-1)²| = 1/(p-1)² ≤ 4/p².
    Key inequality: (p-1) ≥ p/2 for p ≥ 2, so (p-1)² ≥ p²/4, so 1/(p-1)² ≤ 4/p². -/
private lemma euler_factor_abs_bound {p : ℕ} (hp : p.Prime) (N : ℤ)
    (hdvd : ¬ p ∣ N.natAbs) :
    ‖(ramanujanSumC p N).re / ((p : ℝ) - 1) ^ 2‖ ≤ 4 / (p : ℝ) ^ 2 := by
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    linarith [show (1 : ℝ) < (p : ℝ) from by exact_mod_cast hp.one_lt]
  rw [ramanujanSumC_prime p hp N, if_neg hdvd]
  simp only [Complex.neg_re, Complex.one_re, Real.norm_eq_abs, neg_div]
  rw [abs_neg, abs_div, abs_one, abs_pow, abs_of_pos hp1_pos]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ((p : ℝ) - 2)]

-- ============================================================
-- HELPER: Finiteness of primes dividing N
-- ============================================================

/-- The set of primes dividing N.natAbs is finite for N ≠ 0. -/
private lemma prime_dvd_finite (N : ℤ) (hN : N ≠ 0) :
    Set.Finite {p : {p : ℕ // p.Prime} | (p : ℕ) ∣ N.natAbs} := by
  have h_image : (Subtype.val '' {p : {p : ℕ // p.Prime} | (p : ℕ) ∣ N.natAbs}).Finite := by
    apply Set.Finite.subset (Nat.divisors N.natAbs).finite_toSet
    intro n hn
    simp only [Set.mem_image, Set.mem_setOf_eq] at hn
    obtain ⟨⟨m, _⟩, hmdvd, rfl⟩ := hn
    simp only [Finset.mem_coe, Nat.mem_divisors]
    exact ⟨hmdvd, Int.natAbs_ne_zero.mpr hN⟩
  exact (Set.finite_image_iff Subtype.val_injective.injOn).mp h_image

-- ============================================================
-- THEOREM #22: Euler factor series summability
-- ============================================================

/-- **Euler factor series summability** (Theorem #22):
    For nonzero N, the series ∑_p c_p(N).re/(p-1)² over all primes converges absolutely.

    Proof structure:
    · Cofinitely (all p ∤ N): |c_p(N).re/(p-1)²| = 1/(p-1)² ≤ 4/p²
    · The bound 4/p² sums to ≤ 4·∑(1/n²) < ∞ (p-series, exponent 2)
    · Exceptions (p | N): finitely many, handled by `of_norm_bounded_eventually`

    Proved 2026-06-27. -/
theorem singularSeries_summable (N : ℤ) (hN : N ≠ 0) :
    Summable (fun p : {p : ℕ // p.Prime} =>
      (ramanujanSumC ↑p N).re / ((↑p : ℝ) - 1) ^ 2) := by
  -- Build bounding series: 4/p² is summable over primes (p-series, exp 2 > 1)
  have h_prime_sq : Summable (fun p : {p : ℕ // p.Prime} => (1 : ℝ) / (↑p : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      Subtype.coe_injective
  have h_bound : Summable (fun p : {p : ℕ // p.Prime} => (4 : ℝ) / (↑p : ℝ) ^ 2) := by
    have h4 := h_prime_sq.const_smul (4 : ℝ)
    refine h4.congr fun p => ?_
    simp only [smul_eq_mul, one_div]
    ring
  -- Apply comparison: bound holds cofinitely (fails only for finite primes p | N)
  refine Summable.of_norm_bounded_eventually h_bound ?_
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (prime_dvd_finite N hN)
  intro ⟨p, hp⟩ hmem
  simp only [Set.mem_setOf_eq, not_le] at hmem
  simp only [Set.mem_setOf_eq]
  by_contra hndvd
  exact absurd (euler_factor_abs_bound hp N hndvd) (not_le.mpr hmem)

-- ============================================================
-- THEOREM #23: Singular series multipliability
-- ============================================================

/-- **Singular series multipliability** (Theorem #23):
    For nonzero N, the Euler product ∏_p (1 + c_p(N)/(p-1)²) converges.
    Direct corollary of singularSeries_summable via
    `Real.multipliable_one_add_of_summable`.

    Proved 2026-06-27. -/
theorem singularSeries_multipliable (N : ℤ) (hN : N ≠ 0) :
    Multipliable (fun p : {p : ℕ // p.Prime} =>
      1 + (ramanujanSumC ↑p N).re / ((↑p : ℝ) - 1) ^ 2) :=
  Real.multipliable_one_add_of_summable (singularSeries_summable N hN)

-- ============================================================
-- DEFINITION: Singular series 𝔖(N)
-- ============================================================

/-- The Hardy-Littlewood singular series: 𝔖(N) = ∏_p (1 + c_p(N)/(p-1)²).
    This Euler product governs the expected density of Goldbach representations
    of even N. The positivity 𝔖(N) > 0 (Theorem #24) is essential for the
    Hardy-Littlewood lower bound r_2(N) ≥ C · 𝔖(N) · N/log²(N). -/
noncomputable def singularSeries (N : ℤ) : ℝ :=
  ∏' p : {p : ℕ // p.Prime}, (1 + (ramanujanSumC ↑p N).re / ((↑p : ℝ) - 1) ^ 2)

-- ============================================================
-- THEOREM #24: Singular series positivity (MAIN RESULT)
-- ============================================================

/-- **Singular series positivity** (Theorem #24):
    For nonzero even N, the singular series 𝔖(N) > 0.

    Proof: Each Euler factor f_p = 1 + c_p(N)/(p-1)² > 0 by `eulerFactor_pos`.
    The series ∑ log(f_p) converges by `Real.summable_log_one_add_of_summable`
    applied to the absolutely summable Euler factor series (Theorem #22).
    Therefore 𝔖(N) = exp(∑ log f_p) > 0 by `Real.rexp_tsum_eq_tprod`.

    This is a critical structural result: it shows the Hardy-Littlewood
    circle method predicts a positive (nonzero) density of Goldbach
    representations for all even N ≥ 4.

    Proved 2026-06-27. -/
theorem singularSeries_pos (N : ℤ) (hN : N ≠ 0) (hNeven : (2 : ℕ) ∣ N.natAbs) :
    0 < singularSeries N := by
  unfold singularSeries
  have hpos : ∀ p : {p : ℕ // p.Prime}, 0 < 1 + (ramanujanSumC ↑p N).re / ((↑p : ℝ) - 1) ^ 2 :=
    fun p => eulerFactor_pos p.val p.prop N hNeven
  have hlog : Summable (fun p : {p : ℕ // p.Prime} =>
      Real.log (1 + (ramanujanSumC ↑p N).re / ((↑p : ℝ) - 1) ^ 2)) :=
    Real.summable_log_one_add_of_summable (singularSeries_summable N hN)
  rw [← Real.rexp_tsum_eq_tprod hpos hlog]
  exact Real.exp_pos _

-- ============================================================
-- THEOREM #25: Euler factor formula (divisor case)
-- ============================================================

/-- **Euler factor formula — divisor case** (Theorem #25):
    For prime p dividing N.natAbs, the Euler factor equals p/(p-1).
    Corollary of `ramanujanSumC_prime`: c_p(N) = p-1, so
    1 + (p-1)/(p-1)² = 1 + 1/(p-1) = p/(p-1).
    Proved 2026-06-28. -/
theorem singularSeries_factor_dvd (p : ℕ) (hp : p.Prime) (N : ℤ)
    (hdvd : p ∣ N.natAbs) :
    1 + (ramanujanSumC p N).re / ((p : ℝ) - 1) ^ 2 = (p : ℝ) / ((p : ℝ) - 1) := by
  have hp1_ne : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  have hre : (ramanujanSumC p N).re = (p : ℝ) - 1 := by
    rw [ramanujanSumC_prime p hp N, if_pos hdvd]
    simp [Complex.sub_re, Complex.one_re]
  rw [hre]
  field_simp
  ring

-- ============================================================
-- THEOREM #26: Euler factor formula (non-divisor case)
-- ============================================================

/-- **Euler factor formula — non-divisor case** (Theorem #26):
    For prime p not dividing N.natAbs, the Euler factor equals (p-2)*p/(p-1)².
    Corollary of `ramanujanSumC_prime`: c_p(N) = -1, so
    1 + (-1)/(p-1)² = ((p-1)²-1)/(p-1)² = (p²-2p)/(p-1)² = p(p-2)/(p-1)².
    Proved 2026-06-28. -/
theorem singularSeries_factor_notDvd (p : ℕ) (hp : p.Prime) (N : ℤ)
    (hdvd : ¬ p ∣ N.natAbs) :
    1 + (ramanujanSumC p N).re / ((p : ℝ) - 1) ^ 2 =
    ((p : ℝ) - 2) * p / ((p : ℝ) - 1) ^ 2 := by
  have hp1_ne : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  have hre : (ramanujanSumC p N).re = -1 := by
    rw [ramanujanSumC_prime p hp N, if_neg hdvd]
    simp [Complex.neg_re, Complex.one_re]
  rw [hre]
  field_simp
  ring

-- ============================================================
-- THEOREM #27: p=2 factor is always 2 for even N
-- ============================================================

/-- **The p=2 Euler factor equals 2** (Theorem #27):
    For even N (2 | N.natAbs), the Euler factor at p=2 is exactly 2.
    Follows immediately from `singularSeries_factor_dvd` with p=2 (so p/(p-1) = 2/1 = 2).
    Proved 2026-06-28. -/
theorem singularSeries_factor_two (N : ℤ) (hNeven : (2 : ℕ) ∣ N.natAbs) :
    1 + (ramanujanSumC 2 N).re / ((2 : ℝ) - 1) ^ 2 = 2 := by
  have hp2 : Nat.Prime 2 := by decide
  have hre : (ramanujanSumC 2 N).re = (2 : ℝ) - 1 := by
    rw [ramanujanSumC_prime 2 hp2 N, if_pos hNeven]
    simp [Complex.sub_re, Complex.one_re]
  rw [hre]
  norm_num

-- ============================================================
-- THEOREM #28: Non-divisor factor < 1 for odd primes
-- ============================================================

/-- **Non-divisor Euler factor is strictly less than 1** (Theorem #28):
    For a prime p ≥ 3 not dividing N.natAbs, the Euler factor (p-2)p/(p-1)² < 1.
    Proof: (p-2)p < (p-1)², i.e., p²-2p < p²-2p+1, i.e., 0 < 1.
    This shows the non-divisor factors "push down" 𝔖(N) below 2 (while divisor
    factors push it up), giving the characteristic shape of the singular series.
    Proved 2026-06-28. -/
theorem eulerFactor_lt_one_notDvd (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (N : ℤ)
    (hdvd : ¬ p ∣ N.natAbs) :
    1 + (ramanujanSumC p N).re / ((p : ℝ) - 1) ^ 2 < 1 := by
  rw [singularSeries_factor_notDvd p hp N hdvd]
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  rw [div_lt_one (pow_pos hp1_pos 2)]
  have hp3r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  nlinarith

-- ============================================================
-- THEOREM #29: Euler factor ≥ 3/4 for odd primes
-- ============================================================

/-- **Euler factor uniform lower bound** (Theorem #29):
    For prime p ≥ 3 and even N, the Euler factor 1 + c_p(N).re/(p-1)² ≥ 3/4.

    Cases:
    - p | N.natAbs: factor = p/(p-1) ≥ 3/2 ≥ 3/4 (since p ≥ 3 → p/(p-1) ≥ 3/2)
    - p ∤ N.natAbs: factor = (p-2)p/(p-1)². Need 4(p-2)p ≥ 3(p-1)².
      This is p²-2p-3 ≥ 0 ↔ (p-3)(p+1) ≥ 0, which holds for p ≥ 3.
      Minimum 3/4 is achieved exactly at p=3, p ∤ N.

    Proved 2026-06-28. -/
theorem eulerFactor_ge_three_quarters (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (N : ℤ)
    (hNeven : (2 : ℕ) ∣ N.natAbs) :
    3 / 4 ≤ 1 + (ramanujanSumC p N).re / ((p : ℝ) - 1) ^ 2 := by
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  have hp1_ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hp1_pos
  have hp3r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  by_cases hdvd : p ∣ N.natAbs
  · -- dvd case: factor = p/(p-1); show p/(p-1) - 3/4 = (p+3)/(4*(p-1)) ≥ 0
    rw [singularSeries_factor_dvd p hp N hdvd]
    have hshift : (p : ℝ) / ((p : ℝ) - 1) - 3 / 4 =
        ((p : ℝ) + 3) / (4 * ((p : ℝ) - 1)) := by field_simp; ring
    linarith [div_nonneg
      (by linarith [show (0:ℝ) < (p:ℝ) from by exact_mod_cast hp.pos] : (0:ℝ) ≤ (p:ℝ) + 3)
      (by linarith : (0:ℝ) ≤ 4 * ((p:ℝ) - 1)),
      hshift.symm.le.ge]
  · -- notDvd case: factor = (p-2)*p/(p-1)²; show factor - 3/4 = (p²-2p-3)/(4*(p-1)²) ≥ 0
    rw [singularSeries_factor_notDvd p hp N hdvd]
    have hshift : ((p : ℝ) - 2) * (p : ℝ) / ((p : ℝ) - 1) ^ 2 - 3 / 4 =
        ((p : ℝ) ^ 2 - 2 * (p : ℝ) - 3) / (4 * ((p : ℝ) - 1) ^ 2) := by field_simp; ring
    linarith [div_nonneg
      (by nlinarith : (0:ℝ) ≤ (p:ℝ)^2 - 2*(p:ℝ) - 3)
      (by positivity : (0:ℝ) ≤ 4 * ((p:ℝ) - 1)^2),
      hshift.symm.le.ge]

-- ============================================================
-- THEOREM #30: Euler factor deviation bound
-- ============================================================

/-- **Euler factor absolute deviation bound** (Theorem #30):
    For any prime p, |factor - 1| ≤ p/(p-1)².
    This simplifies as: |c_p(N).re/(p-1)²| ≤ p/(p-1)².
    - If p | N: c_p(N).re = p-1, so |(p-1)/(p-1)²| = 1/(p-1) ≤ p/(p-1)² [since p-1 ≤ p].
    - If p ∤ N: c_p(N).re = -1, so |-1/(p-1)²| = 1/(p-1)² ≤ p/(p-1)² [since 1 ≤ p].
    Used to bound the convergence rate of ∑ |factor-1| ≤ ∑_p p/(p-1)² < ∞.
    Proved 2026-06-28. -/
theorem singularSeries_factor_bound_abs (p : ℕ) (hp : p.Prime) (N : ℤ) :
    |1 + (ramanujanSumC p N).re / ((p : ℝ) - 1) ^ 2 - 1| ≤
    (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  have hp1_ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hp1_pos
  have hp1sq_pos : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := pow_pos hp1_pos 2
  have hp1sq_ne : ((p : ℝ) - 1) ^ 2 ≠ 0 := ne_of_gt hp1sq_pos
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  -- Simplify: |1 + re/(p-1)² - 1| = |re/(p-1)²| = |re| / (p-1)²
  have hsimp : 1 + (ramanujanSumC p N).re / ((p : ℝ) - 1) ^ 2 - 1 =
      (ramanujanSumC p N).re / ((p : ℝ) - 1) ^ 2 := by ring
  rw [hsimp, abs_div, abs_of_pos hp1sq_pos]
  by_cases hdvd : p ∣ N.natAbs
  · -- dvd: c_p(N).re = p-1, so |p-1|/(p-1)² = 1/(p-1) ≤ p/(p-1)²
    have hre : (ramanujanSumC p N).re = (p : ℝ) - 1 := by
      rw [ramanujanSumC_prime p hp N, if_pos hdvd]; simp [Complex.sub_re, Complex.one_re]
    rw [hre, abs_of_pos hp1_pos]
    -- Goal: (p-1)/(p-1)² ≤ p/(p-1)²; equiv to p-1 ≤ p
    apply div_le_div_of_nonneg_right _ hp1sq_pos.le
    linarith
  · -- notDvd: c_p(N).re = -1, so |-1|/(p-1)² = 1/(p-1)² ≤ p/(p-1)²
    have hre : (ramanujanSumC p N).re = -1 := by
      rw [ramanujanSumC_prime p hp N, if_neg hdvd]; simp [Complex.neg_re, Complex.one_re]
    rw [hre]
    simp only [abs_neg, abs_one]
    -- Goal: 1/(p-1)² ≤ p/(p-1)²; equiv to 1 ≤ p
    apply div_le_div_of_nonneg_right _ hp1sq_pos.le
    linarith

-- ============================================================
-- THEOREM #31: Euler factor ≤ 2 for all primes and even N
-- ============================================================

/-- **Euler factor upper bound** (Theorem #31):
    For prime p and even N, the Euler factor 1 + c_p(N).re/(p-1)² ≤ 2.

    Cases:
    - p = 2, 2 | N: factor = 2 (exact value, achieved at p=2)
    - p | N.natAbs, p ≥ 3: factor = p/(p-1) = 1 + 1/(p-1) < 2 (since (p-2)/(p-1) ≥ 0)
    - p ∤ N.natAbs: factor = (p-2)p/(p-1)² < 1 < 2

    The upper bound 2 is tight: achieved at p=2 for any even N.
    Proved 2026-06-28. -/
theorem eulerFactor_le_two (p : ℕ) (hp : p.Prime) (N : ℤ) (hNeven : (2 : ℕ) ∣ N.natAbs) :
    1 + (ramanujanSumC p N).re / ((p : ℝ) - 1) ^ 2 ≤ 2 := by
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  by_cases hdvd : p ∣ N.natAbs
  · -- dvd case: factor = p/(p-1); show 2 - p/(p-1) = (p-2)/(p-1) ≥ 0
    rw [singularSeries_factor_dvd p hp N hdvd]
    have hshift : 2 - (p : ℝ) / ((p : ℝ) - 1) =
        ((p : ℝ) - 2) / ((p : ℝ) - 1) := by field_simp; ring
    have h_nonneg : (0 : ℝ) ≤ 2 - (p : ℝ) / ((p : ℝ) - 1) := by
      rw [hshift]; exact div_nonneg (by linarith) hp1_pos.le
    linarith
  · -- notDvd case: factor = (p-2)p/(p-1)² ≤ 1 ≤ 2
    have hlt : 1 + (ramanujanSumC p N).re / ((p : ℝ) - 1) ^ 2 < 1 := by
      -- Note: this requires p ≥ 3 (p is odd prime since p ∤ N.natAbs but 2 | N.natAbs)
      have hp2 : p ≠ 2 := fun h => by subst h; exact hdvd hNeven
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      exact eulerFactor_lt_one_notDvd p hp hp3 N hdvd
    linarith

-- ============================================================
-- THEOREM #32: Combined if-else Euler factor formula
-- ============================================================

/-- **Euler factor combined formula** (Theorem #32):
    For prime p and even N, the Euler factor equals:
    - p/(p-1)    if p | N.natAbs (divisor case)
    - (p-2)p/(p-1)² if p ∤ N.natAbs (non-divisor case)
    Direct corollary combining Theorems #25 and #26.
    Proved 2026-06-28. -/
theorem singularSeries_factor_cases (p : ℕ) (hp : p.Prime) (N : ℤ) (hNeven : (2 : ℕ) ∣ N.natAbs) :
    1 + (ramanujanSumC p N).re / ((p : ℝ) - 1) ^ 2 =
    if p ∣ N.natAbs then (p : ℝ) / ((p : ℝ) - 1)
    else ((p : ℝ) - 2) * (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  by_cases hdvd : p ∣ N.natAbs
  · rw [if_pos hdvd, singularSeries_factor_dvd p hp N hdvd]
  · rw [if_neg hdvd, singularSeries_factor_notDvd p hp N hdvd]

-- ============================================================
-- THEOREM #33: Singular series is nonneg
-- ============================================================

/-- **Singular series nonnegativity** (Theorem #33):
    For N ≠ 0 even, 0 ≤ 𝔖(N). Trivial corollary of `singularSeries_pos`.
    Proved 2026-06-28. -/
theorem singularSeries_nonneg (N : ℤ) (hN : N ≠ 0) (hNeven : (2 : ℕ) ∣ N.natAbs) :
    0 ≤ singularSeries N :=
  le_of_lt (singularSeries_pos N hN hNeven)

-- ============================================================
-- THEOREM #34: Divisor factor is strictly greater than 1
-- ============================================================

/-- **Divisor Euler factor strictly exceeds 1** (Theorem #34):
    For any prime p dividing N.natAbs, the Euler factor 1 + c_p(N).re/(p-1)² > 1.

    By `singularSeries_factor_dvd`, the factor equals p/(p-1).
    Since p > p-1 > 0, we have p/(p-1) > 1.
    This contrasts with non-divisor odd prime factors (Theorem #28), which are < 1.

    Proved 2026-06-29. -/
theorem singularSeries_factor_dvd_gt_one (p : ℕ) (hp : p.Prime)
    (N : ℤ) (hdvd : p ∣ N.natAbs) :
    1 < 1 + (ramanujanSumC p N).re / ((p : ℝ) - 1) ^ 2 := by
  rw [singularSeries_factor_dvd p hp N hdvd]
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    linarith [show (1 : ℝ) < (p : ℝ) from by exact_mod_cast hp.one_lt]
  rw [one_lt_div hp1_pos]
  linarith [show (1 : ℝ) < (p : ℝ) from by exact_mod_cast hp.one_lt]

-- ============================================================
-- THEOREM #35: Factor ≥ 1 iff p divides N (for odd primes)
-- ============================================================

/-- **Divisibility criterion via Euler factor** (Theorem #35):
    For prime p ≥ 3 and even N, the Euler factor satisfies:
      1 ≤ 1 + c_p(N).re/(p-1)² ↔ p ∣ N.natAbs

    Forward: if factor ≥ 1 but p ∤ N, then `eulerFactor_lt_one_notDvd` gives factor < 1,
    a contradiction.
    Backward: if p ∣ N, then factor > 1 ≥ 1 by `singularSeries_factor_dvd_gt_one`.

    This gives an arithmetic characterization: the p-th Euler factor exceeds 1
    precisely when p is a prime divisor of the target N.

    Proved 2026-06-29. -/
theorem singularSeries_factor_ge_one_iff_dvd (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (N : ℤ) :
    1 ≤ 1 + (ramanujanSumC p N).re / ((p : ℝ) - 1) ^ 2 ↔ p ∣ N.natAbs := by
  constructor
  · intro hle
    by_contra hndvd
    exact absurd hle (not_le.mpr (eulerFactor_lt_one_notDvd p hp hp3 N hndvd))
  · intro hdvd
    linarith [singularSeries_factor_dvd_gt_one p hp N hdvd]

-- ============================================================
-- THEOREM #36: Singular series depends only on prime support
-- ============================================================

/-- **Singular series radical invariance** (Theorem #36):
    If N and M have the same set of prime divisors (i.e., for every prime p,
    p ∣ N.natAbs ↔ p ∣ M.natAbs), then 𝔖(N) = 𝔖(M).

    Proof: Each Euler factor 1 + c_p(N).re/(p-1)² depends only on whether p | N.natAbs
    (via `ramanujanSumC_prime`). The identity follows by `tprod_congr`.

    Consequence: 𝔖(N) is constant on classes of even integers sharing the same
    radical (squarefree kernel). In particular, 𝔖(2p) = 𝔖(2p²) for prime p,
    and 𝔖(N) = 𝔖(N') whenever N and N' are in the same "arithmetic type"
    (same prime support).

    Proved 2026-06-29. -/
theorem singularSeries_eq_of_same_prime_factors (N M : ℤ)
    (h : ∀ p : ℕ, p.Prime → (p ∣ N.natAbs ↔ p ∣ M.natAbs)) :
    singularSeries N = singularSeries M := by
  unfold singularSeries
  apply tprod_congr
  intro ⟨p, hp⟩
  have hre_eq : (ramanujanSumC p N).re = (ramanujanSumC p M).re := by
    rw [ramanujanSumC_prime p hp N, ramanujanSumC_prime p hp M]
    by_cases hdvd : p ∣ N.natAbs
    · rw [if_pos hdvd, if_pos ((h p hp).mp hdvd)]
    · rw [if_neg hdvd, if_neg (fun hm => hdvd ((h p hp).mpr hm))]
  rw [hre_eq]

end GoldbachBridge
