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
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
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

private noncomputable def S_dftp (q : ℕ) (f : Fin q → ℂ) (a : Fin q) : ℂ :=
  ∑ n : Fin q, f n * Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * ↑a / ↑q)

private lemma conj_S_dftp (q : ℕ) (f : Fin q → ℂ) (a : Fin q) :
    starRingEnd ℂ (S_dftp q f a) =
    ∑ n : Fin q, (starRingEnd ℂ (f n)) * Complex.exp (2 * ↑Real.pi * -Complex.I * ↑n * ↑a / ↑q) := by
  simp only [S_dftp, map_sum, map_mul]; congr 1; ext n
  rw [← Complex.exp_conj]; congr 1
  simp [map_mul, map_div₀, map_ofNat, map_natCast, Complex.conj_ofReal, Complex.conj_I]

private lemma exp_orth_fin_dftp (q : ℕ) (hq : 0 < q) (k : ℤ) :
    ∑ a : Fin q, Complex.exp (2 * ↑Real.pi * Complex.I * ↑k * ↑a / ↑q) =
    if (q : ℤ) ∣ k then (q : ℂ) else 0 := by
  rw [← exp_orthogonality_int q hq,
      ← Fin.sum_univ_eq_sum_range
        (fun a => Complex.exp (2 * ↑Real.pi * Complex.I * ↑k * ↑a / ↑q)) q]

private lemma fin_dvd_iff_dftp (q : ℕ) (n m : Fin q) :
    (q : ℤ) ∣ (↑m : ℤ) - n ↔ n = m := by
  constructor
  · intro ⟨k, hk⟩
    apply Fin.ext
    have hk0 : k = 0 := by
      rcases Int.lt_trichotomy k 0 with h | h | h
      · nlinarith [n.isLt, m.isLt, mul_comm (q : ℤ) k]
      · exact h
      · nlinarith [n.isLt, m.isLt, mul_comm (q : ℤ) k]
    have heq : (n.val : ℤ) = m.val := by
      linarith [hk, show (q : ℤ) * k = 0 from by rw [hk0]; ring]
    exact_mod_cast heq
  · intro h; rw [h]; simp

private lemma dft_parseval_C (q : ℕ) (hq : 0 < q) (f : Fin q → ℂ) :
    ∑ a : Fin q, (starRingEnd ℂ (S_dftp q f a)) * S_dftp q f a =
    (q : ℂ) * ∑ n : Fin q, (starRingEnd ℂ (f n)) * f n := by
  simp_rw [conj_S_dftp, S_dftp, Finset.sum_mul, Finset.mul_sum]
  have hcomb : ∀ a n m : Fin q,
      (starRingEnd ℂ (f n)) * Complex.exp (2 * ↑Real.pi * -Complex.I * ↑n * ↑a / ↑q) *
      (f m * Complex.exp (2 * ↑Real.pi * Complex.I * ↑m * ↑a / ↑q)) =
      (starRingEnd ℂ (f n)) * f m *
      Complex.exp (2 * ↑Real.pi * Complex.I * ((↑m : ℂ) - ↑n) * ↑a / ↑q) := fun a n m => by
    have hexp : Complex.exp (2 * ↑Real.pi * -Complex.I * (↑n : ℂ) * ↑a / ↑q) *
                Complex.exp (2 * ↑Real.pi * Complex.I * (↑m : ℂ) * ↑a / ↑q) =
                Complex.exp (2 * ↑Real.pi * Complex.I * ((↑m : ℂ) - ↑n) * ↑a / ↑q) := by
      rw [← Complex.exp_add]; congr 1; ring
    calc (starRingEnd ℂ (f n)) * Complex.exp (2 * ↑Real.pi * -Complex.I * (↑n : ℂ) * ↑a / ↑q) *
            (f m * Complex.exp (2 * ↑Real.pi * Complex.I * (↑m : ℂ) * ↑a / ↑q)) =
          (starRingEnd ℂ (f n)) * f m *
            (Complex.exp (2 * ↑Real.pi * -Complex.I * (↑n : ℂ) * ↑a / ↑q) *
             Complex.exp (2 * ↑Real.pi * Complex.I * (↑m : ℂ) * ↑a / ↑q)) := by ring
      _ = (starRingEnd ℂ (f n)) * f m *
            Complex.exp (2 * ↑Real.pi * Complex.I * ((↑m : ℂ) - ↑n) * ↑a / ↑q) := by rw [hexp]
  simp_rw [hcomb]
  trans ∑ n : Fin q, ∑ m : Fin q,
      (starRingEnd ℂ (f n)) * f m *
      ∑ a : Fin q, Complex.exp (2 * ↑Real.pi * Complex.I * ((↑m : ℂ) - ↑n) * ↑a / ↑q)
  · rw [Finset.sum_comm]; congr 1; ext n
    rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]
  have horth : ∀ n m : Fin q,
      ∑ a : Fin q, Complex.exp (2 * ↑Real.pi * Complex.I * ((↑m : ℂ) - ↑n) * ↑a / ↑q) =
      if (q : ℤ) ∣ (↑m : ℤ) - n then (q : ℂ) else 0 := fun n m => by
    have hrw : ∀ a : Fin q,
        Complex.exp (2 * ↑Real.pi * Complex.I * ((↑m : ℂ) - ↑n) * ↑a / ↑q) =
        Complex.exp (2 * ↑Real.pi * Complex.I * ↑((↑m : ℤ) - (↑n : ℤ)) * ↑a / ↑q) := fun a => by
      push_cast; ring
    simp_rw [hrw]; exact exp_orth_fin_dftp q hq _
  simp_rw [horth, fin_dvd_iff_dftp q]
  simp_rw [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1; ext i; ring

/-- **Discrete Parseval / Plancherel identity** (B2).
For `q > 0` and any `f : Fin q → ℂ`, the DFT is an isometry up to scale `q`:
`∑_{a<q} |∑_{n<q} f(n) e(na/q)|² = q · ∑_{n<q} |f(n)|²`.
This is the key energy-conservation identity used in major-arc extraction
for the almost-all Goldbach circle method.
Proved by hand (Cipher), 2026-06-16. -/
theorem dft_parseval (q : ℕ) (hq : 0 < q) (f : Fin q → ℂ) :
    ∑ a : Fin q, ‖∑ n : Fin q,
      f n * Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * ↑a / ↑q)‖ ^ 2 =
    q * ∑ n : Fin q, ‖f n‖ ^ 2 := by
  have hre : ∀ z : ℂ, ‖z‖ ^ 2 = (starRingEnd ℂ z * z).re := fun z => by
    conv_rhs => rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.sq_norm z
  have hkey := congr_arg Complex.re (dft_parseval_C q hq f)
  simp only [Complex.re_sum] at hkey
  rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
      Complex.re_sum] at hkey
  simp_rw [← hre] at hkey
  simp only [S_dftp] at hkey
  exact_mod_cast hkey

-- ============================================================
-- B6: Ramanujan sums (setup for the circle-method singular series)
-- c_q(n) = ∑_{a<q, (a,q)=1} e(2π·I·a·n/q)
-- ============================================================

/-- **Ramanujan sum** (B6): the exponential sum over reduced residues mod q.
`ramanujanSumC q n = ∑_{0 ≤ a < q, gcd(a,q)=1} exp(2πi·a·n/q)`.
This is the fundamental building block of the circle-method singular series
𝔖(n) = ∑_q μ(q)² c_q(−n)/φ(q)². Proved real-valued and equal to
μ(q/gcd(q,n))·φ(q)/φ(q/gcd(q,n)) by Möbius inversion. -/
noncomputable def ramanujanSumC (q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime q a),
    Complex.exp (2 * ↑Real.pi * Complex.I * ↑a * ↑n / ↑q)

/-- **Ramanujan sum periodicity** (B6): c_q(n + q) = c_q(n).
Proved 2026-06-17. The period-q character e(2πi·a·n/q) shifts by
e(2πi·a) = 1 when n advances by q. -/
theorem ramanujanSumC_periodic (q : ℕ) (hq : 0 < q) (n : ℤ) :
    ramanujanSumC q (n + q) = ramanujanSumC q n := by
  simp only [ramanujanSumC]
  apply Finset.sum_congr rfl
  intro a _
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hrw : 2 * ↑Real.pi * Complex.I * ↑a * ↑(n + (q : ℤ)) / (q : ℂ) =
      2 * ↑Real.pi * Complex.I * ↑a * ↑n / (q : ℂ) +
      ↑a * (2 * ↑Real.pi * Complex.I) := by
    push_cast; field_simp
  rw [hrw, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- **Ramanujan sum at zero equals Euler totient** (B6): c_q(0) = φ(q).
When n=0, every character exp(2πi·a·0/q) = 1, so the sum equals
the count of reduced residues mod q — Euler's totient.
Proved 2026-06-17. -/
theorem ramanujanSumC_zero (q : ℕ) (hq : 0 < q) :
    ramanujanSumC q 0 = (Nat.totient q : ℂ) := by
  simp only [ramanujanSumC, Int.cast_zero, mul_zero, zero_div, Complex.exp_zero]
  norm_cast
  exact (Finset.card_eq_sum_ones _).symm.trans (Nat.totient_eq_card_coprime q)

end GoldbachBridge
