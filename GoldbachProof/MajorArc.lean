/-
B8: Major arc approximation for the Hardy-Littlewood circle method.

On major arcs near a rational a/q with q ≤ (log N)^B and |β| ≤ Q/N,
the von Mangoldt exponential sum satisfies:

  S_Λ(a/q + β) ≈ (μ(q)/φ(q)) · v(β, N)

where v(β, N) = ∑_{n < N} e(2πinβ) is the "completed" exponential sum
(unweighted, summing all integers up to N).

The approximation error is O(N / (log N)^A) and uses Siegel-Walfisz.

Theorems proved here (axiom-free):
  #46: expSum_at_zero                  — v(0, N) = N
  #47: expSum_norm_le                  — ‖v(β, N)‖ ≤ N
  #49: expSum_add_one                  — v(N+1) = v(N) + e(Nβ)
  #50: vonMangoldt_exp_sum_decompose   — S_Λ(a/q+β) = ∑_r e(ra/q)·S_r(β)

Definitions:
  SiegelWalfiszHyp A     — the Siegel-Walfisz hypothesis at level A
  major_arc_approx       — conditional approximation theorem (sorry)

Proved by hand (Cipher), 2026-07-03.
-/
import GoldbachProof.VonMangoldt
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

open Complex Real ArithmeticFunction Finset

set_option maxHeartbeats 400000

namespace GoldbachBridge

-- ---------------------------------------------------------------------------
-- The completed exponential sum  v(β, N) = ∑_{n < N} e(2πinβ)
-- ---------------------------------------------------------------------------

/-- The completed exponential sum:
    v(β, N) = ∑_{n < N} e(2πinβ).
    This is the "unweighted" version of vonMangoldt_exp_sum — it sums a
    pure complex exponential over all integers 0, 1, …, N-1.
    On major arcs near a/q, S_Λ(a/q + β) ≈ (μ(q)/φ(q)) · expSum(β, N). -/
noncomputable def expSum (N : ℕ) (β : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * ↑β)

/-- **Theorem #46. Completed sum at zero** (B8).
    v(0, N) = N: at β = 0 every exponential factor is 1, so expSum N 0 = N. -/
theorem expSum_at_zero (N : ℕ) : expSum N 0 = ↑N := by
  unfold expSum
  have : ∀ n : ℕ, Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * ↑(0 : ℝ)) = 1 := by
    intro n; simp [Complex.exp_zero]
  simp_rw [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- Norm of the exponential factor is 1 for any integer n and real β. -/
private lemma expSum_factor_norm_one (n : ℕ) (β : ℝ) :
    ‖Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * ↑β)‖ = 1 := by
  have hrw : 2 * ↑Real.pi * Complex.I * ↑n * ↑β =
      ↑(2 * Real.pi * (↑n : ℝ) * β) * Complex.I := by push_cast; ring
  rw [hrw, Complex.norm_exp_ofReal_mul_I]

/-- **Theorem #47. Completed sum norm bound** (B8).
    ‖v(β, N)‖ ≤ N: triangle inequality, each |e(nβ)| = 1. -/
theorem expSum_norm_le (N : ℕ) (β : ℝ) : ‖expSum N β‖ ≤ N := by
  unfold expSum
  apply le_trans (norm_sum_le _ _)
  have hone : ∑ n ∈ Finset.range N, ‖Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * ↑β)‖ =
              ∑ _n ∈ Finset.range N, (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro n _; exact expSum_factor_norm_one n β
  rw [hone, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

-- ---------------------------------------------------------------------------
-- Auxiliary lemmas for the major arc approximation
-- ---------------------------------------------------------------------------

/-- **Theorem #49. expSum telescopes** (B8).
    expSum (N+1) β = expSum N β + e(2πiNβ): one more term is added. -/
theorem expSum_add_one (N : ℕ) (β : ℝ) :
    expSum (N + 1) β = expSum N β +
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑N * ↑β) := by
  unfold expSum
  rw [Finset.sum_range_succ]

-- ---------------------------------------------------------------------------
-- The Siegel-Walfisz hypothesis
-- ---------------------------------------------------------------------------

/-- The Siegel-Walfisz hypothesis at level A.
    For any q ≤ (log N)^A and (a, q) = 1, the von Mangoldt sum over the
    arithmetic progression {n < N : n ≡ a (mod q)} approximates ψ(N)/φ(q)
    with a power-saving error O(ψ(N) / (log N)^A).

    This is a standard analytic number theory result (Siegel 1935, Walfisz 1936).
    It is NOT yet in Mathlib and we take it as a hypothesis for conditional theorems. -/
def SiegelWalfiszHyp (A : ℝ) : Prop :=
  ∀ (N q : ℕ) (a : ℤ),
    0 < N → 0 < q →
    Nat.Coprime q a.natAbs →
    (q : ℝ) ≤ Real.log N ^ A →
    ‖(∑ n ∈ Finset.range N,
        if (n : ZMod q) = (a : ZMod q) then (vonMangoldt n : ℝ) else 0 : ℝ) -
      psi N / (Nat.totient q : ℝ)‖ ≤
    psi N / Real.log N ^ A

-- ---------------------------------------------------------------------------
-- Residue class decomposition (B8 key step)
-- ---------------------------------------------------------------------------

/-- **Theorem #50. Residue class decomposition of S_Λ(a/q + β)** (B8).
    Grouping by n mod q:
      S_Λ(a/q + β) = ∑_{r<q} e(r·a/q) · ∑_{n<N, n≡r(q)} Λ(n)·e(n·β)
    Key: for n ≡ r (mod q), e(n·a/q) = e(r·a/q) because n = k·q + r
    and e(k·q·a/q) = e(k·a) = 1 (k·a is an integer). -/
theorem vonMangoldt_exp_sum_decompose (N q : ℕ) (a : ℤ) (β : ℝ) (hq : 0 < q) :
    vonMangoldt_exp_sum N ((a : ℝ) / q + β) =
    ∑ r ∈ Finset.range q,
      Complex.exp (2 * ↑π * I * ↑r * ↑a / ↑q) *
      ∑ n ∈ (Finset.range N).filter (fun n => n % q = r),
        (vonMangoldt n : ℝ) * Complex.exp (2 * ↑π * I * ↑n * ↑β) := by
  unfold vonMangoldt_exp_sum
  have hq_ne : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  simp_rw [show ∀ n : ℕ,
      (vonMangoldt n : ℝ) * Complex.exp (2 * ↑π * I * ↑n * ↑((a : ℝ) / q + β)) =
      Complex.exp (2 * ↑π * I * ↑n * ↑a / ↑q) *
        ((vonMangoldt n : ℝ) * Complex.exp (2 * ↑π * I * ↑n * ↑β)) from fun n => by
    rw [show (2 * ↑π * I * ↑n * ↑((a : ℝ) / q + β) : ℂ) =
        2 * ↑π * I * ↑n * ↑a / ↑q + 2 * ↑π * I * ↑n * ↑β by push_cast; ring,
      Complex.exp_add]; ring]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun n => n % q)
      (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hq))]
  apply Finset.sum_congr rfl
  intro r _
  have hexp_eq : ∀ n : ℕ, n % q = r →
      Complex.exp (2 * ↑π * I * ↑n * ↑a / ↑q) =
      Complex.exp (2 * ↑π * I * ↑r * ↑a / ↑q) := by
    intro n hn_mod
    have hn_dec : n / q * q + r = n := by
      have h := Nat.div_add_mod n q; rw [mul_comm] at h; rwa [hn_mod] at h
    have hn_cast : (n : ℂ) = ↑(n / q) * ↑q + ↑r := by exact_mod_cast hn_dec.symm
    have hstep : (2 * ↑π * I * ↑n * ↑a / ↑q : ℂ) =
        ↑(n / q : ℕ) * ↑a * (2 * ↑π * I) + 2 * ↑π * I * ↑r * ↑a / ↑q := by
      rw [hn_cast,
        show (2 * ↑π * I * (↑(n / q) * ↑q + ↑r) * ↑a / ↑q : ℂ) =
            2 * ↑π * I * ↑(n/q) * ↑q * ↑a / ↑q + 2 * ↑π * I * ↑r * ↑a / ↑q by ring]
      have hcancel : (2 * ↑π * I * ↑(n/q) * ↑q * ↑a / ↑q : ℂ) =
                     ↑(n/q : ℕ) * ↑a * (2 * ↑π * I) := by
        rw [show (2 * ↑π * I * ↑(n/q) * ↑q * ↑a / ↑q : ℂ) =
            ↑(n/q : ℕ) * ↑a * (2 * ↑π * I) * (↑q / ↑q) by ring,
          div_self hq_ne]; ring
      rw [hcancel]
    rw [hstep, Complex.exp_add]
    have hint : Complex.exp (↑(n / q : ℕ) * ↑a * (2 * ↑π * I)) = 1 := by
      have hcast : (↑(n / q : ℕ) : ℂ) * ↑a * (2 * ↑π * I) =
                   ↑((n / q : ℕ) * a : ℤ) * (2 * ↑π * I) := by
        simp only [Int.cast_mul, Int.cast_natCast]
      rw [hcast]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [hint, one_mul]
  rw [show ∑ n ∈ (Finset.range N).filter (fun n => n % q = r),
      Complex.exp (2 * ↑π * I * ↑n * ↑a / ↑q) *
      ((vonMangoldt n : ℝ) * Complex.exp (2 * ↑π * I * ↑n * ↑β)) =
      ∑ n ∈ (Finset.range N).filter (fun n => n % q = r),
      Complex.exp (2 * ↑π * I * ↑r * ↑a / ↑q) *
      ((vonMangoldt n : ℝ) * Complex.exp (2 * ↑π * I * ↑n * ↑β)) from
    Finset.sum_congr rfl (fun n hn => by
      rw [hexp_eq n (Finset.mem_filter.mp hn).2]),
    ← Finset.mul_sum]

-- ---------------------------------------------------------------------------
-- Residue-class Chebyshev ψ and rational-point evaluation
-- ---------------------------------------------------------------------------

/-- Residue-class restricted Chebyshev ψ:
    ψ_r(N, q) = ∑_{n < N, n ≡ r (mod q)} Λ(n). -/
noncomputable def psiResClass (N q r : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range N).filter (fun n => n % q = r), (vonMangoldt n : ℝ)

/-- **Theorem #52. Von Mangoldt sum at rational point α = a/q** (B8).
    At β = 0 (i.e., α = a/q exactly on a major arc center):
      S_Λ(a/q) = ∑_{r<q} e(2πi·r·a/q) · ψ_r(N, q)
    where ψ_r(N,q) = ∑_{n<N, n≡r(q)} Λ(n).
    Direct corollary of the residue class decompose (#50) at β = 0. -/
theorem vonMangoldt_exp_sum_at_rational (N q : ℕ) (a : ℤ) (hq : 0 < q) :
    vonMangoldt_exp_sum N ((a : ℝ) / q) =
    ∑ r ∈ Finset.range q,
      Complex.exp (2 * ↑π * I * ↑r * ↑a / ↑q) * ↑(psiResClass N q r) := by
  have h := vonMangoldt_exp_sum_decompose N q a 0 hq
  simp only [add_zero] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  unfold psiResClass
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp [mul_zero, Complex.exp_zero, mul_one]

-- ---------------------------------------------------------------------------
-- Major arc approximation (B8, conditional on Siegel-Walfisz)
-- ---------------------------------------------------------------------------

/-- **Major arc approximation** (B8, conditional on Siegel-Walfisz).
    For α = a/q + β with (a, q) = 1, q ≤ (log N)^A, |β| ≤ (log N)^A / N
    (major arc near a/q):

      S_Λ(a/q + β) ≈ (μ(q) / φ(q)) · v(β, N)

    where v(β, N) = expSum N β is the completed exponential sum.

    This is the key approximation connecting the von Mangoldt sum on major arcs
    to the singular series: integrating |S_Λ|² e(-2Nα) over all major arcs
    gives 𝔖(N) · (log N)^{-2} · N (up to lower-order terms), which is positive
    for even N ≥ 4 by singularSeries_pos (#24).

    The proof uses:
    1. Grouping S_Λ(a/q + β) by residue classes mod q
    2. Siegel-Walfisz to approximate each residue-class sum by ψ(N)/φ(q)
    3. The Ramanujan sum identity: ∑_{r mod q, (r,q)=1} e(ra/q) = μ(q) (proved: #14-#15)

    TODO: Full proof requires completing the residue-class grouping and
    applying Siegel-Walfisz termwise. The conditional statement is sound;
    completing the analytic details is the main B8 milestone. -/
theorem major_arc_approx
    (A : ℝ) (hA : 0 < A)
    (hSW : SiegelWalfiszHyp A)
    (N q : ℕ) (a : ℤ) (β : ℝ)
    (hN : 2 ≤ N)
    (hq : 0 < q) (haq : Nat.Coprime q a.natAbs)
    (hQ : (q : ℝ) ≤ Real.log N ^ A)
    (hβ : |β| ≤ Real.log N ^ A / N) :
    ‖vonMangoldt_exp_sum N ((a : ℝ) / q + β) -
      (ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ) *
      expSum N β‖ ≤
    2 * psi N / Real.log N ^ A := by
  sorry

end GoldbachBridge
