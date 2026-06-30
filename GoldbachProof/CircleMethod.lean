/-
Circle method foundational identities for the Hardy-Littlewood approach to Goldbach.

B3 (circle method setup):
  #37: char_integral_orthogonality  — ∫₀¹ e(kα) dα = δ_{k,0}
  #38: circle_method_convolution    — ∫₀¹ (∑_n f(n) e(nα))² e(-Nα) dα = ∑_{n+m=N} f(n)f(m)

Proved by hand (Cipher), 2026-06-30.
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open Complex Real MeasureTheory intervalIntegral

set_option maxHeartbeats 400000

namespace GoldbachBridge

private lemma fourier_one_eq_exp (k : ℤ) (x : ℝ) :
    fourier k (x : AddCircle (1 : ℝ)) =
    Complex.exp (2 * ↑Real.pi * Complex.I * ↑k * x) := by
  rw [fourier_coe_apply]; push_cast; congr 1; ring

/-- **Character orthogonality on [0,1]** (B3, theorem #37).
For `k : ℤ`, `∫₀¹ exp(2πikα) dα = if k = 0 then 1 else 0`.
This is the key kernel identity of the Hardy-Littlewood circle method.
Proved by hand (Cipher), 2026-06-30. -/
theorem char_integral_orthogonality (k : ℤ) :
    ∫ x in (0 : ℝ)..1, Complex.exp (2 * ↑Real.pi * Complex.I * ↑k * x) =
    if k = 0 then 1 else 0 := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  split_ifs with hk
  · -- k = 0: integrand simplifies to 1, ∫₀¹ 1 dα = 1
    subst hk
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero]
    rw [intervalIntegral.integral_const, sub_zero, one_smul]
  · -- k ≠ 0: antiderivative has equal values at endpoints 0 and 1
    have hk' : (-k : ℤ) ≠ 0 := neg_ne_zero.mpr hk
    -- Rewrite integrand as fourier k ∘ coe (avoiding simp_rw timeout)
    rw [integral_congr (fun x _ => (fourier_one_eq_exp k x).symm)]
    -- Continuity of fourier k ∘ coe
    have hcont : Continuous (fun x : ℝ => fourier k (x : AddCircle (1 : ℝ))) :=
      (fourier k).continuous.comp (AddCircle.continuous_mk' 1)
    -- FTC: antiderivative of (fourier k ∘ coe) is F = 1/(-2πi(-k)) * fourier k
    have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt
        (fun y : ℝ => (1:ℂ) / (-2 * ↑Real.pi * Complex.I * ↑(-k)) * fourier k ((y : ℝ) : AddCircle (1:ℝ)))
        (fourier k ((x : ℝ) : AddCircle (1:ℝ))) x := by
      intro x _
      have h := has_antideriv_at_fourier_neg (hT := ⟨one_pos⟩) (n := -k) hk' x
      simp only [neg_neg] at h
      exact h
    rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
    -- F(1) = F(0) because (1 : AddCircle 1) = (0 : AddCircle 1) (period 1)
    have h1eq0 : ((1 : ℝ) : AddCircle (1 : ℝ)) = (0 : AddCircle (1 : ℝ)) :=
      AddCircle.coe_period 1
    simp [h1eq0]

/-- Integrability of `α ↦ c * exp(b * α)` on any interval. -/
private lemma intervalIntegrable_const_mul_exp (c b : ℂ) (a d : ℝ) :
    IntervalIntegrable (fun α : ℝ => c * Complex.exp (b * α)) MeasureTheory.volume a d :=
  (continuous_const.mul (Complex.continuous_exp.comp
    (continuous_const.mul Complex.continuous_ofReal))).intervalIntegrable a d

/-- **Circle method convolution identity** (B3, theorem #38).
For `f : ℤ → ℂ`, finite support `S : Finset ℤ`, and `N : ℤ`:
  `∫₀¹ (∑_{n∈S} f(n)e(nα)) · (∑_{m∈S} f(m)e(mα)) · e(-Nα) dα = ∑_{n∈S,m∈S,n+m=N} f(n)f(m)`.
This is the foundational identity of the Hardy-Littlewood circle method: the integral
of the squared prime exponential sum detects the Goldbach representation count.
Proved by hand (Cipher), 2026-06-30. -/
theorem circle_method_convolution (f : ℤ → ℂ) (S : Finset ℤ) (N : ℤ) :
    ∫ α in (0 : ℝ)..1,
      (∑ n ∈ S, f n * Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * α)) *
      (∑ m ∈ S, f m * Complex.exp (2 * ↑Real.pi * Complex.I * ↑m * α)) *
      Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑N * α)) =
    ∑ n ∈ S, ∑ m ∈ S, if n + m = N then f n * f m else 0 := by
  -- Step 1: expand product of sums into a double sum with combined exponent
  have hexp : ∀ α : ℝ,
      (∑ n ∈ S, f n * Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * α)) *
      (∑ m ∈ S, f m * Complex.exp (2 * ↑Real.pi * Complex.I * ↑m * α)) *
      Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑N * α)) =
      ∑ n ∈ S, ∑ m ∈ S,
        f n * f m * Complex.exp (2 * ↑Real.pi * Complex.I * ↑(n + m - N) * α) := by
    intro α
    -- Expand (∑ An)(∑ Bm) = ∑ n, ∑ m, An * Bm, then multiply by e(-Nα)
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    -- distribute e(-Nα) into inner sum: (∑ m, X m) * C = ∑ m, X m * C
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    -- combine three exponentials: e(nα) * e(mα) * e(-Nα) = e((n+m-N)α)
    rw [show f n * Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * ↑α) *
          (f m * Complex.exp (2 * ↑Real.pi * Complex.I * ↑m * ↑α)) *
          Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑N * ↑α)) =
        f n * f m * (Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * ↑α) *
          Complex.exp (2 * ↑Real.pi * Complex.I * ↑m * ↑α) *
          Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑N * ↑α))) by ring]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1; congr 1; push_cast; ring
  simp_rw [hexp]
  -- Step 2: integrability of each (n, m) term
  have hint : ∀ n m : ℤ, IntervalIntegrable
      (fun α : ℝ => f n * f m * Complex.exp (2 * ↑Real.pi * Complex.I * ↑(n + m - N) * ↑α))
      MeasureTheory.volume 0 1 := fun n m =>
    intervalIntegrable_const_mul_exp _ _ _ _
  -- Step 3: swap ∫ and outer Σ
  have hint_outer : ∀ n ∈ S, IntervalIntegrable
      (fun α : ℝ => ∑ m ∈ S, f n * f m * Complex.exp (2 * ↑Real.pi * Complex.I * ↑(n + m - N) * ↑α))
      MeasureTheory.volume 0 1 :=
    fun n _ => by
      have h := IntervalIntegrable.sum S (fun m _ => hint n m)
      have heq : (∑ m ∈ S, fun α : ℝ => f n * f m * Complex.exp (2 * ↑Real.pi * Complex.I * ↑(n + m - N) * ↑α)) =
                 (fun α : ℝ => ∑ m ∈ S, f n * f m * Complex.exp (2 * ↑Real.pi * Complex.I * ↑(n + m - N) * ↑α)) :=
        funext (fun (α : ℝ) => Finset.sum_apply α S _)
      rwa [heq] at h
  rw [integral_finset_sum hint_outer]
  congr 1; ext n
  -- Step 4: swap ∫ and inner Σ
  rw [integral_finset_sum (fun m _ => hint n m)]
  congr 1; ext m
  -- Step 5: pull constant f(n)f(m) outside the integral
  rw [intervalIntegral.integral_const_mul]
  -- Step 6: apply character orthogonality
  rw [show (fun α : ℝ => Complex.exp (2 * ↑Real.pi * Complex.I * ↑(n + m - N) * ↑α)) =
      (fun α : ℝ => Complex.exp (2 * ↑Real.pi * Complex.I * ↑(n + m - N) * α)) from rfl]
  rw [char_integral_orthogonality (n + m - N)]
  -- Step 7: δ_{n+m-N,0} = δ_{n+m,N}
  simp only [Int.sub_eq_zero, mul_ite, mul_one, mul_zero]

end GoldbachBridge
