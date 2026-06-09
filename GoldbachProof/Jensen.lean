/-
  Jensen's Inequality for the Secular Equation
  =============================================

  Formalizes: E₀ ≤ d_avg - λ from the secular equation
  via Jensen's inequality applied to f(x) = 1/(x - E₀).

  Mathematical context:
  - H_base = D - λ|u⟩⟨u| where D = diag(d₁,...,d_m) and |u⟩ = (1/√m)(1,...,1)
  - The ground state eigenvalue E₀ satisfies the secular equation:
      (1/m)∑ᵢ 1/(dᵢ - E₀) = 1/λ
  - Since f(x) = 1/(x - E₀) is convex for x > E₀, Jensen's inequality gives:
      (1/m)∑ᵢ 1/(dᵢ - E₀) ≥ 1/(d_avg - E₀)
  - Therefore: 1/λ ≥ 1/(d_avg - E₀), which means d_avg - E₀ ≥ λ, i.e., E₀ ≤ d_avg - λ

  Theorem inventory (10 theorems, 0 axioms, 0 sorry):
  - Theorem 1 (jensen_algebraic_core): Pure algebraic step — fully proved
  - Theorem 2 (jensen_algebraic_core_strict): Strict variant — fully proved
  - Theorem 3 (one_div_anti_of_pos): Reciprocal anti-monotonicity — fully proved
  - Theorem 4 (convexOn_inv_sub): Convexity of 1/(x-c) — PROVED via strictConvexOn_zpow
  - Theorem 5 (jensen_reciprocal_avg): Jensen for finite averages — PROVED via ConvexOn.map_sum_le
  - Theorem 6 (jensen_secular_bound): Full secular bound — fully proved
  - Theorem 5 (jensen_bound_from_secular): Interface theorem — fully proved
  - Theorem 6 (jensen_bound_from_finset): Finset data to bound — fully proved
  - Theorem 7 (jensen_gives_spectral_gap): Spectral gap connection — fully proved
  - Theorem 8 (spectral_gap_lower_bound): Quantitative gap bound — fully proved
-/

import GoldbachProof.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Finset

namespace Goldbach

/-! ### Theorem 1: Pure algebraic core

  If 1/λ ≥ 1/(d_avg - E) and both λ > 0 and d_avg - E > 0,
  then E ≤ d_avg - λ.

  This is the final step of the Jensen bound derivation.
-/

/-- The algebraic core: if 1/λ ≥ 1/(d_avg - E), then E ≤ d_avg - λ.
    This step takes the output of Jensen's inequality applied to the
    secular equation and produces the eigenvalue bound. -/
theorem jensen_algebraic_core
    (E d_avg lambda : ℝ)
    (h_lambda_pos : lambda > 0)
    (h_gap_pos : d_avg - E > 0)
    (h_ineq : 1 / lambda ≥ 1 / (d_avg - E)) :
    E ≤ d_avg - lambda := by
  -- From 1/λ ≥ 1/(d_avg - E) with both denominators positive,
  -- we get d_avg - E ≥ λ, i.e., E ≤ d_avg - λ.
  suffices h : lambda ≤ d_avg - E by linarith
  -- 1/(d_avg - E) ≤ 1/lambda, clear denominators
  have h2 : 1 / (d_avg - E) ≤ 1 / lambda := h_ineq
  rw [div_le_div_iff₀ h_gap_pos h_lambda_pos] at h2
  linarith

/-- Variant: strict inequality version. If 1/λ > 1/(d_avg - E), then E < d_avg - λ. -/
theorem jensen_algebraic_core_strict
    (E d_avg lambda : ℝ)
    (h_lambda_pos : lambda > 0)
    (h_gap_pos : d_avg - E > 0)
    (h_ineq : 1 / lambda > 1 / (d_avg - E)) :
    E < d_avg - lambda := by
  suffices h : lambda < d_avg - E by linarith
  have h2 : 1 / (d_avg - E) < 1 / lambda := h_ineq
  rw [div_lt_div_iff₀ h_gap_pos h_lambda_pos] at h2
  linarith

/-! ### Theorem 2: Reciprocal anti-monotonicity

  For positive reals, a ≤ b implies 1/b ≤ 1/a.
  This is already in Mathlib as `one_div_le_one_div_of_le`.
  We package it for our use case.
-/

/-- If 0 < a ≤ b, then 1/b ≤ 1/a. Direct wrapper around Mathlib. -/
theorem one_div_anti_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    1 / b ≤ 1 / a :=
  one_div_le_one_div_of_le ha hab

/-! ### Convexity of f(x) = 1/(x - c) on (c, ∞)

  Since 1/(x - c) = (x - c)^(-1), and Mathlib's `strictConvexOn_zpow` proves
  that x^m is strictly convex on (0, ∞) for m ≠ 0, 1, we obtain convexity
  of x^(-1) on (0, ∞). Translating by -c gives convexity of (x - c)^(-1) on (c, ∞).
-/

/-- The function f(x) = 1/(x - c) is convex on the open interval (c, ∞).

    Proof: By `strictConvexOn_zpow`, the function x ↦ x⁻¹ = x ^ (-1 : ℤ) is strictly
    convex on (0, ∞). Translating by -c via `ConvexOn.translate_right` gives that
    x ↦ (x - c)⁻¹ is convex on (c, ∞). Since 1/(x - c) = (x - c)⁻¹, this concludes
    the proof.

    This was previously axiomatized; now fully proved using Mathlib's
    `strictConvexOn_zpow` (Analysis.Convex.SpecificFunctions.Deriv).
-/
theorem convexOn_inv_sub (c : ℝ) :
    ConvexOn ℝ (Set.Ioi c) (fun x => 1 / (x - c)) := by
  have h_strict : StrictConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x ^ (-1 : ℤ)) :=
    strictConvexOn_zpow (by norm_num : (-1 : ℤ) ≠ 0) (by norm_num : (-1 : ℤ) ≠ 1)
  have h_convex : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x ^ (-1 : ℤ)) := h_strict.convexOn
  have h_translated := h_convex.translate_right (-c)
  convert h_translated using 1
  · ext x
    simp only [Set.mem_Ioi, Set.mem_preimage]
    constructor
    · intro h; linarith
    · intro h; linarith
  · ext x
    simp only [Function.comp, neg_add_eq_sub, zpow_neg_one, one_div]

/-! ### Jensen's inequality for finite uniform averages (PROVED)

  For a convex function f and points x₁, ..., xₘ in its domain,
  Jensen's inequality states:
    f((1/m) ∑ᵢ xᵢ) ≤ (1/m) ∑ᵢ f(xᵢ)

  Proved by applying `ConvexOn.map_sum_le` with uniform weights wᵢ = 1/m
  to f(x) = 1/(x - E), which is convex on (E, ∞) by `convexOn_inv_sub`.
-/

/-- Jensen's inequality for the reciprocal function on a finite set.

    If all dᵢ > E and d_avg = (1/m) ∑ᵢ dᵢ, then:
      1/(d_avg - E) ≤ (1/m) ∑ᵢ 1/(dᵢ - E)

    Proof: Apply `ConvexOn.map_sum_le` with uniform weights wᵢ = 1/|s|.
    The main work is converting between Mathlib's smul-based formulation
    and our division-based statement.
-/
theorem jensen_reciprocal_avg {ι : Type*}
    (s : Finset ι) (d : ι → ℝ) (E : ℝ)
    (hs : s.Nonempty)
    (h_above : ∀ i ∈ s, d i > E)
    (d_avg : ℝ)
    (h_avg : d_avg = (∑ i ∈ s, d i) / s.card) :
    1 / (d_avg - E) ≤ (∑ i ∈ s, (1 / (d i - E))) / s.card := by
  set f : ℝ → ℝ := fun x => 1 / (x - E) with hf_def
  have hf_convex : ConvexOn ℝ (Set.Ioi E) f := convexOn_inv_sub E
  have hcard_pos : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hcard_ne : (s.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  set w : ι → ℝ := fun _ => (1 : ℝ) / s.card with hw_def
  have hw_nonneg : ∀ i ∈ s, 0 ≤ w i := by
    intro i _; exact div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hw_sum : ∑ i ∈ s, w i = 1 := by
    simp only [hw_def]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    exact div_mul_cancel₀ 1 hcard_ne
  have hmem : ∀ i ∈ s, d i ∈ Set.Ioi E := by
    intro i hi; exact Set.mem_Ioi.mpr (h_above i hi)
  have h_jensen := hf_convex.map_sum_le hw_nonneg hw_sum hmem
  have h_lhs : ∑ i ∈ s, w i • d i = d_avg := by
    simp only [hw_def, smul_eq_mul]
    rw [← Finset.mul_sum, h_avg, div_mul_eq_mul_div, one_mul]
  have h_rhs : ∑ i ∈ s, w i • f (d i) = (∑ i ∈ s, f (d i)) / s.card := by
    simp only [hw_def, smul_eq_mul]
    rw [← Finset.mul_sum, div_mul_eq_mul_div, one_mul]
  rw [h_lhs, h_rhs] at h_jensen
  exact h_jensen

/-! ### Theorem 3: The full Jensen bound for the secular equation

  Combining the secular equation with Jensen's inequality:
  If (1/m) ∑ᵢ 1/(dᵢ - E) = 1/λ, then E ≤ d_avg - λ.
-/

/-- The full Jensen bound: if the secular equation holds
    and Jensen's inequality gives the lower bound on the average,
    then E ≤ d_avg - λ.

    This combines:
    - The secular equation: (1/m) ∑ᵢ 1/(dᵢ - E) = 1/λ
    - Jensen's inequality: (1/m) ∑ᵢ 1/(dᵢ - E) ≥ 1/(d_avg - E)
    - Algebraic core: 1/λ ≥ 1/(d_avg - E) implies E ≤ d_avg - λ
-/
theorem jensen_secular_bound
    (E d_avg lambda : ℝ)
    (h_lambda_pos : lambda > 0)
    (h_gap_pos : d_avg - E > 0)
    (h_secular_ge_jensen : 1 / lambda ≥ 1 / (d_avg - E)) :
    E ≤ d_avg - lambda :=
  jensen_algebraic_core E d_avg lambda h_lambda_pos h_gap_pos h_secular_ge_jensen

/-! ### Theorem 4: From secular equation + Jensen to the bound

  This is the "interface" theorem that takes the secular equation
  as a hypothesis (the average of reciprocals equals 1/λ)
  and the Jensen lower bound (average of reciprocals ≥ reciprocal of average)
  and concludes E₀ ≤ d_avg - λ.
-/

/-- Complete Jensen bound derivation from explicit hypotheses.
    Given:
    - secular_value = (1/m) ∑ᵢ 1/(dᵢ - E) (the average of reciprocals)
    - secular_value = 1/λ (the secular equation)
    - secular_value ≥ 1/(d_avg - E) (Jensen's inequality)
    - λ > 0 and d_avg > E
    Conclude: E ≤ d_avg - λ
-/
theorem jensen_bound_from_secular
    (E d_avg lambda secular_value : ℝ)
    (h_lambda_pos : lambda > 0)
    (h_gap_pos : d_avg - E > 0)
    (h_secular : secular_value = 1 / lambda)
    (h_jensen : secular_value ≥ 1 / (d_avg - E)) :
    E ≤ d_avg - lambda := by
  have h : 1 / lambda ≥ 1 / (d_avg - E) := by linarith
  exact jensen_algebraic_core E d_avg lambda h_lambda_pos h_gap_pos h

/-! ### Theorem 5: The complete chain from Finset data to the bound

  This theorem takes concrete Finset data (diagonal entries and secular equation)
  and produces the eigenvalue bound, threading through Jensen's inequality.
-/

/-- Complete Jensen bound from Finset data.
    Given a finite set of diagonal entries {dᵢ} with:
    - All dᵢ > E
    - The secular equation: (∑ 1/(dᵢ-E)) / m = 1/λ
    - d_avg = (∑ dᵢ) / m
    Conclude: E ≤ d_avg - λ
-/
theorem jensen_bound_from_finset {ι : Type*}
    (s : Finset ι) (d : ι → ℝ) (E lambda : ℝ)
    (hs : s.Nonempty)
    (h_lambda_pos : lambda > 0)
    (h_above : ∀ i ∈ s, d i > E)
    (d_avg : ℝ)
    (h_avg : d_avg = (∑ i ∈ s, d i) / s.card)
    (h_gap_pos : d_avg - E > 0)
    (h_secular : (∑ i ∈ s, (1 / (d i - E))) / s.card = 1 / lambda) :
    E ≤ d_avg - lambda := by
  -- Step 1: Jensen gives 1/(d_avg - E) ≤ (∑ 1/(dᵢ-E)) / m
  have h_jensen := jensen_reciprocal_avg s d E hs h_above d_avg h_avg
  -- Step 2: Combine with secular equation: 1/(d_avg - E) ≤ 1/λ
  have h_ineq : 1 / lambda ≥ 1 / (d_avg - E) := by
    calc 1 / (d_avg - E)
        ≤ (∑ i ∈ s, (1 / (d i - E))) / ↑(s.card) := h_jensen
      _ = 1 / lambda := h_secular
  -- Step 3: Apply algebraic core
  exact jensen_algebraic_core E d_avg lambda h_lambda_pos h_gap_pos h_ineq

/-! ### Theorem 6: Connection to spectral gap bound

  This connects Jensen's bound to the spectral_gap_positive theorem
  from Basic.lean, providing the E₀ ≤ d_avg - λ hypothesis.
-/

/-- The Jensen bound provides the E₀ ≤ d_avg - λ hypothesis needed
    by spectral_gap_positive. Combined with Cauchy interlacing (E₁ ≥ d_min),
    this gives the spectral gap bound Δ ≥ λ - (d_avg - d_min). -/
theorem jensen_gives_spectral_gap
    (lambda_L1 d_avg d_min E0 E1 : ℝ)
    (h_lambda_pos : lambda_L1 > 0)
    (h_gap_pos : d_avg - E0 > 0)
    (h_secular_jensen : 1 / lambda_L1 ≥ 1 / (d_avg - E0))
    (h_interlace : E1 ≥ d_min)
    (h_spread : lambda_L1 > d_avg - d_min) :
    E1 - E0 > 0 := by
  have h_jensen := jensen_algebraic_core E0 d_avg lambda_L1 h_lambda_pos h_gap_pos h_secular_jensen
  exact spectral_gap_positive lambda_L1 d_avg d_min E0 E1 h_jensen h_interlace h_spread

/-! ### Theorem 7: Quantitative spectral gap lower bound

  The spectral gap Δ = E₁ - E₀ is at least λ - (d_avg - d_min).
  This combines Jensen (E₀ ≤ d_avg - λ) with interlacing (E₁ ≥ d_min).
-/

/-- Quantitative lower bound on the spectral gap.
    Under Jensen + interlacing hypotheses:
      Δ = E₁ - E₀ ≥ λ - (d_avg - d_min) -/
theorem spectral_gap_lower_bound
    (lambda d_avg d_min E0 E1 : ℝ)
    (h_lambda_pos : lambda > 0)
    (h_gap_pos : d_avg - E0 > 0)
    (h_secular_jensen : 1 / lambda ≥ 1 / (d_avg - E0))
    (h_interlace : E1 ≥ d_min) :
    E1 - E0 ≥ lambda - (d_avg - d_min) := by
  have h_jensen := jensen_algebraic_core E0 d_avg lambda h_lambda_pos h_gap_pos h_secular_jensen
  -- E₀ ≤ d_avg - λ and E₁ ≥ d_min
  -- Therefore E₁ - E₀ ≥ d_min - (d_avg - λ) = λ - (d_avg - d_min)
  linarith

end Goldbach
