/-
Bridge lemmas for the "almost-all Goldbach" circle-method spine
(Track 3, gap analysis Jun 10 2026: ~/workforce/cipher/track3-gap-analysis.md).

B10-core (markov_counting) proved by the Archimedes engine
(DeepSeek-Prover-V2-7B), attempt #1, 2026-06-10. This is the counting heart
of the L²/Bessel exceptional-set bound: with f n = the major-arc deficit of
the Goldbach count at n, it converts an L¹ bound on the deficit into a bound
on the number of exceptional n.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Finset

namespace GoldbachBridge

/-- **Markov's inequality for finite sums** (B10-core).
The number of `n < N` with `f n ≥ t` is at most `(∑_{n<N} f n) / t`,
stated multiplied out to avoid division. -/
theorem markov_counting (N : ℕ) (f : ℕ → ℝ) (t : ℝ) (ht : 0 < t)
    (hf : ∀ n, 0 ≤ f n) :
    (((Finset.range N).filter (fun n => t ≤ f n)).card : ℝ) * t ≤
      ∑ n ∈ Finset.range N, f n := by
  have h₂ : ((Finset.range N).filter (fun n => t ≤ f n)).card * t ≤ ∑ n ∈ Finset.range N, f n := by
    calc
      ((Finset.range N).filter (fun n => t ≤ f n)).card * t
        = ∑ n ∈ (Finset.range N).filter (fun n => t ≤ f n), t := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ (Finset.range N).filter (fun n => t ≤ f n), f n := by
        apply Finset.sum_le_sum
        intro x hx
        have h₃ : t ≤ f x := by
          simp_all [Finset.mem_filter]
        linarith [hf x]
      _ ≤ ∑ n ∈ Finset.range N, f n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · apply Finset.filter_subset
        · intro x _ hx
          exact hf x
  exact h₂

/-- **Geometric sum norm bound** (B1 piece 1).
For `z` on the unit circle with `z ≠ 1`, the partial geometric sums are
uniformly bounded: `‖∑_{n<N} zⁿ‖ ≤ 2 / ‖1 - z‖`. With the Jordan sine
bound this gives the standard minor-arc linear exponential-sum estimate.
Proved by hand (Cipher), 2026-06-11. -/
theorem geom_sum_norm_le (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ 2 / ‖1 - z‖ := by
  have hz0 : (0:ℝ) < ‖1 - z‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => hz1 h.symm
  rw [geom_sum_eq hz1, norm_div, norm_sub_rev z 1]
  gcongr
  calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num

/-- **Orthogonality of additive characters** (B2 core).
For `q > 0` and `k : ℤ`, `∑_{a<q} e(2πi·k·a/q) = q` if `q ∣ k`, else `0`.
This is the finite-Parseval/major-arc extraction kernel of the circle
method: summing a character over a full period detects divisibility.
Proved by hand (Cipher), 2026-06-12, after the engine spent 300+ attempts. -/
theorem exp_orthogonality_int (q : ℕ) (hq : 0 < q) (k : ℤ) :
    ∑ a ∈ Finset.range q,
      Complex.exp (2 * Real.pi * Complex.I * k * a / q) =
    if (q : ℤ) ∣ k then (q : ℂ) else 0 := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * k / q) with hz
  have hterm : ∀ a ∈ Finset.range q,
      Complex.exp (2 * Real.pi * Complex.I * k * a / q) = z ^ a := by
    intro a _
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl hterm]
  by_cases hdvd : (q : ℤ) ∣ k
  · simp only [if_pos hdvd]
    obtain ⟨m, rfl⟩ := hdvd
    have hz1 : z = 1 := by
      rw [hz]
      have harg : 2 * Real.pi * Complex.I * ((q * m : ℤ) : ℂ) / q
          = (m : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        field_simp
      rw [harg, Complex.exp_int_mul_two_pi_mul_I]
    rw [hz1]
    simp
  · simp only [if_neg hdvd]
    have hz1 : z ≠ 1 := by
      rw [hz, Ne, Complex.exp_eq_one_iff]
      push_neg
      intro n hn
      apply hdvd
      refine ⟨n, ?_⟩
      have h2 : (2 * Real.pi * Complex.I) * ((k : ℂ) / q)
          = (2 * Real.pi * Complex.I) * n := by
        linear_combination hn
      have h3 : (k : ℂ) / q = n :=
        mul_left_cancel₀ Complex.two_pi_I_ne_zero h2
      have h4 : (k : ℂ) = (q : ℂ) * n := by
        field_simp at h3
        linear_combination h3
      exact_mod_cast h4
    have hzq : z ^ q = 1 := by
      rw [hz, ← Complex.exp_nat_mul]
      have harg : (q : ℂ) * (2 * Real.pi * Complex.I * k / q)
          = (k : ℂ) * (2 * Real.pi * Complex.I) := by
        field_simp
      rw [harg, Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hz1, hzq, sub_self, zero_div]

/-- **Half-angle norm identity** (B1 piece 2).
`‖1 - e(2πiα)‖ = 2|sin(πα)|`. Combined with `geom_sum_norm_le`, this gives
the standard minor-arc linear exponential-sum bound of the circle method.
Proved by hand (Cipher), 2026-06-14. -/
theorem norm_one_sub_exp (α : ℝ) :
    ‖(1 : ℂ) - Complex.exp (2 * Real.pi * Complex.I * α)‖ =
    2 * |Real.sin (Real.pi * α)| := by
  have hrw : (2 : ℂ) * Real.pi * Complex.I * α =
      Complex.I * ↑(2 * Real.pi * α) := by push_cast; ring
  rw [hrw, ← neg_sub, norm_neg, Complex.norm_exp_I_mul_ofReal_sub_one,
      show (2 * Real.pi * α) / 2 = Real.pi * α from by ring,
      Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]

end GoldbachBridge
