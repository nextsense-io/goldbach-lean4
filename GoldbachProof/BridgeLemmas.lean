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

end GoldbachBridge
