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

end GoldbachBridge
