/-
Proving ramanujanSum_eq_moebius_sum (Hölder/von Sterneck formula) — Theorem #14.
-/
import GoldbachProof.BridgeLemmas
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Tactic

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction

namespace GoldbachBridge

-- HELPER 1: ∑_{d|n} μ(d) = [n=1] in ℂ
private lemma moebius_sum_eq_ite (n : ℕ) :
    ∑ d ∈ n.divisors, (moebius d : ℂ) = if n = 1 then 1 else 0 := by
  have h : (moebius * ζ : ArithmeticFunction ℂ) n = (1 : ArithmeticFunction ℂ) n :=
    congr_fun (congr_arg DFunLike.coe (coe_moebius_mul_coe_zeta (R := ℂ))) n
  rw [coe_mul_zeta_apply, one_apply] at h; exact h

-- HELPER 2: (gcd q a).divisors = q.divisors.filter (d | a)
private lemma gcd_divisors_filter (q a : ℕ) (hq : 0 < q) :
    (Nat.gcd q a).divisors = q.divisors.filter (fun d => d ∣ a) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter]
  constructor
  · intro ⟨h, _⟩
    exact ⟨⟨dvd_trans h (Nat.gcd_dvd_left q a), hq.ne'⟩,
           dvd_trans h (Nat.gcd_dvd_right q a)⟩
  · intro ⟨⟨hq', _⟩, ha⟩
    exact ⟨Nat.dvd_gcd hq' ha,
           (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left q a) hq).ne'⟩

-- HELPER 3: The bijection sum swap for inner exp sum
private lemma inner_sum_eq_orthogonality (q d : ℕ) (hq : 0 < q) (hd : 0 < d)
    (hdq : d ∣ q) (n : ℤ) :
    ∑ a ∈ (Finset.range q).filter (fun a => d ∣ a),
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑a * ↑n / ↑q) =
    ∑ b ∈ Finset.range (q / d),
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑b * ↑n / ↑(q / d)) := by
  have hqd : q / d * d = q := Nat.div_mul_cancel hdq
  have hqd_pos : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd
  symm
  apply Finset.sum_nbij (fun b => b * d)
  · -- maps into target
    intro b hb
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by nlinarith [Finset.mem_range.mp hb, hqd]),
            dvd_mul_left d b⟩
  · -- injective
    intro b₁ _ b₂ _ h; exact Nat.eq_of_mul_eq_mul_right hd h
  · -- surjective: a ∈ filter(d|a) → ∃ b, b*d = a and b < q/d
    intro a ha
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨k, hk⟩ := ha.2
    -- hk : a = d * k  (Lean dvd is ∃ c, a = b * c)
    refine ⟨k, ?_, (mul_comm k d).trans hk.symm⟩
    rw [Finset.mem_coe, Finset.mem_range]
    -- k < q/d. From hk : a = d*k and ha.1 : a < q, get d*k < q = (q/d)*d, so k < q/d.
    apply Nat.lt_of_mul_lt_mul_right
    rw [hqd, mul_comm]; exact hk ▸ ha.1
  · -- exponentials match via a = b*d substitution: 2πI*b*n/(q/d) = 2πI*(b*d)*n/q
    intro b _
    congr 1; push_cast
    have hq0C : (q:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
    have hqdC : ((q / d : ℕ) : ℂ) * d = q := by exact_mod_cast hqd
    have hqd0 : ((q / d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hqd_pos.ne'
    rw [div_eq_div_iff hqd0 hq0C]
    linear_combination (2 * ↑Real.pi * Complex.I * ↑b * ↑n) * hqdC.symm

-- HELPER 4: Injectivity of d ↦ q/d on divisors of q
private lemma div_inj_on_divisors (q : ℕ) (hq : 0 < q) :
    ∀ d₁ ∈ q.divisors, ∀ d₂ ∈ q.divisors, q / d₁ = q / d₂ → d₁ = d₂ := by
  intro d₁ hd₁ d₂ hd₂ h
  have h1 : d₁ ∣ q := (Nat.mem_divisors.mp hd₁).1
  have h2 : d₂ ∣ q := (Nat.mem_divisors.mp hd₂).1
  have hqd1pos : 0 < q / d₁ := Nat.div_pos (Nat.le_of_dvd hq h1)
    (Nat.pos_of_dvd_of_pos h1 hq)
  apply Nat.eq_of_mul_eq_mul_right hqd1pos
  calc d₁ * (q / d₁) = q := Nat.mul_div_cancel' h1
    _ = d₂ * (q / d₂) := (Nat.mul_div_cancel' h2).symm
    _ = d₂ * (q / d₁) := by rw [h]

-- HELPER 5: Reindex ∑_{d|q, (q/d)|n} μ(d)*(q/d) = ∑_{e|gcd(q,n)} μ(q/e)*e
private lemma reindex_sum (q : ℕ) (hq : 0 < q) (n : ℤ) :
    ∑ d ∈ q.divisors, (moebius d : ℂ) * (if (↑(q / d) : ℤ) ∣ n then ↑(q / d) else 0) =
    ∑ e ∈ (Nat.gcd q n.natAbs).divisors, (moebius (q / e) : ℂ) * e := by
  -- Transform each term: μ(d)*(if p then e else 0) → if p then μ(d)*e else 0
  -- then fold to filter form via ← Finset.sum_filter (to get proper Finset.filter, not sep).
  rw [Finset.sum_congr rfl (fun d _ => show (moebius d : ℂ) * (if (↑(q / d) : ℤ) ∣ n then ↑(q / d) else 0) =
      if (↑(q / d) : ℤ) ∣ n then (moebius d : ℂ) * ↑(q / d) else 0 from by split_ifs <;> ring),
    ← Finset.sum_filter]
  apply Finset.sum_nbij (fun d => q / d)
  · -- image: q/d ∈ gcd(q,n).divisors
    intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdq, _⟩, hdn⟩ := hd
    exact Nat.mem_divisors.mpr
      ⟨Nat.dvd_gcd (Nat.div_dvd_of_dvd hdq)
          (by exact_mod_cast Int.dvd_natAbs.mpr hdn),
        (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left q n.natAbs) hq).ne'⟩
  · -- injective on filtered set
    intro d₁ hd₁ d₂ hd₂ h
    have hd₁q : d₁ ∈ q.divisors := (Finset.mem_filter.mp hd₁).1
    have hd₂q : d₂ ∈ q.divisors := (Finset.mem_filter.mp hd₂).1
    exact div_inj_on_divisors q hq d₁ hd₁q d₂ hd₂q h
  · -- surjective: e|gcd(q,n) → ∃ d ∈ source with q/d = e
    intro e he
    obtain ⟨hegcd, _⟩ := Nat.mem_divisors.mp he
    have heq : e ∣ q := dvd_trans hegcd (Nat.gcd_dvd_left q n.natAbs)
    have hen : e ∣ n.natAbs := dvd_trans hegcd (Nat.gcd_dvd_right q n.natAbs)
    refine ⟨q / e, ?_, Nat.div_div_self heq hq.ne'⟩
    -- goal: q/e ∈ ↑(q.divisors.filter p) (Set coercion), convert via Finset.mem_coe
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨Nat.div_dvd_of_dvd heq, hq.ne'⟩, ?_⟩
    rw [Nat.div_div_self heq hq.ne']
    exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hen)
  · -- terms match: μ(q/(q/d)) * (q/d) = μ(d) * (q/d), via q/(q/d) = d for d|q
    intro d hd
    -- hd.1 : d ∈ q.divisors (List.Mem internally, not And) — use Nat.mem_divisors.mp
    have hdvq : d ∣ q := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    rw [Nat.div_div_self hdvq hq.ne']

-- ============================================================
-- MAIN THEOREM: Hölder formula for Ramanujan sums (Theorem #14)
-- ============================================================

/-- **Hölder/von Sterneck formula** (B6, Theorem #14): c_q(n) = ∑_{d | gcd(q,n)} μ(q/d) * d.
    Proved 2026-06-20. Steps: Möbius indicator, sum swap, exp_orthogonality_int, reindex. -/
theorem ramanujanSum_eq_moebius_sum (q : ℕ) (hq : 0 < q) (n : ℤ) :
    ramanujanSumC q n = ∑ d ∈ Nat.divisors (Nat.gcd q n.natAbs),
      (moebius (q / d) : ℂ) * d := by
  simp only [ramanujanSumC]
  -- Step 1: Möbius indicator — convert ∑_{a coprime to q} exp to ∑_a (∑_{d|gcd(q,a)} μ(d)) * exp
  have hstep1 : ∑ a ∈ (Finset.range q).filter (Nat.Coprime q),
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑a * ↑n / ↑q) =
      ∑ a ∈ Finset.range q,
        (∑ d ∈ q.divisors.filter (fun d => d ∣ a), (moebius d : ℂ)) *
        Complex.exp (2 * ↑Real.pi * Complex.I * ↑a * ↑n / ↑q) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    rw [← gcd_divisors_filter q a hq, moebius_sum_eq_ite (Nat.gcd q a)]
    -- goal: (if Coprime q a then exp else 0) = (if gcd q a = 1 then 1 else 0) * exp
    -- Nat.Coprime q a is definitionally gcd q a = 1
    split_ifs <;> ring
  rw [hstep1]
  -- Step 2: Swap sums. Distribute exp (sum_mul), unfold filter→ite (sum_filter),
  -- swap the now-independent double sum (sum_comm), then refold ite→filter (← sum_filter).
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_filter]
  -- Step 3: For each d|q, evaluate inner sum via exp_orthogonality_int
  have hstep3 : ∀ d ∈ q.divisors,
      ∑ a ∈ (Finset.range q).filter (fun a => d ∣ a),
        (moebius d : ℂ) * Complex.exp (2 * ↑Real.pi * Complex.I * ↑a * ↑n / ↑q) =
      (moebius d : ℂ) * (if (↑(q / d) : ℤ) ∣ n then ↑(q / d) else 0) := by
    intro d hd
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    rw [← Finset.mul_sum, inner_sum_eq_orthogonality q d hq hdpos hdq n]
    -- exp_orthogonality_int expects 2πI * k * a; inner sum has 2πI * b * n — commute
    simp_rw [show ∀ (b : ℕ), (2:ℂ) * ↑Real.pi * Complex.I * ↑b * ↑n =
        2 * ↑Real.pi * Complex.I * ↑n * ↑b from fun b => by ring]
    rw [exp_orthogonality_int (q / d) (Nat.div_pos (Nat.le_of_dvd hq hdq) hdpos) n]
  rw [Finset.sum_congr rfl hstep3]
  -- Step 4: Reindex d ↦ e = q/d
  exact reindex_sum q hq n

-- ============================================================
-- COROLLARY: Ramanujan sum at a prime (Theorem #15)
-- ============================================================

/-- **Ramanujan sum at a prime** (B6, Theorem #15): for a prime p,
    c_p(n) = p-1 if p | n.natAbs, and -1 otherwise.
    Direct corollary of the Hölder formula. Proved 2026-06-21. -/
theorem ramanujanSumC_prime (p : ℕ) (hp : p.Prime) (n : ℤ) :
    ramanujanSumC p n = if p ∣ n.natAbs then ((p : ℂ) - 1) else -1 := by
  rw [ramanujanSum_eq_moebius_sum p hp.pos n]
  -- Determine whether gcd(p, n.natAbs) = 1 or p (the only divisors of a prime)
  rcases hp.eq_one_or_self_of_dvd (Nat.gcd p n.natAbs) (Nat.gcd_dvd_left p n.natAbs) with h | h
  · -- Case: gcd = 1, so p ∤ n.natAbs
    have hn : ¬ p ∣ n.natAbs := by
      intro hdvd
      have hpgcd : p ∣ Nat.gcd p n.natAbs := Nat.dvd_gcd (dvd_refl p) hdvd
      rw [h] at hpgcd
      exact absurd (Nat.le_of_dvd one_pos hpgcd) (by linarith [hp.two_le])
    rw [if_neg hn, h, Nat.divisors_one, Finset.sum_singleton, Nat.div_one]
    have hμp : (moebius p : ℂ) = -1 := by
      exact_mod_cast ArithmeticFunction.moebius_apply_prime hp
    rw [hμp]; ring
  · -- Case: gcd = p, so p | n.natAbs
    have hdvd : p ∣ n.natAbs := h ▸ Nat.gcd_dvd_right p n.natAbs
    rw [if_pos hdvd, h, hp.divisors]
    rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hp.one_lt.ne)]
    rw [Finset.sum_singleton, Nat.div_one, Nat.div_self hp.pos]
    have hμp : (moebius p : ℂ) = -1 := by
      exact_mod_cast ArithmeticFunction.moebius_apply_prime hp
    have hμ1 : (moebius 1 : ℂ) = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_apply_one
    rw [hμp, hμ1]; push_cast; ring

-- ============================================================
-- THEOREM #16: Ramanujan sum at a prime power
-- ============================================================

/-- **Ramanujan sum at a prime power** (B6, Theorem #16): for a prime p and k ≥ 1,
    c_{p^k}(n) = p^{k-1}(p-1) = φ(p^k) if p^k ∣ n.natAbs,
                -p^{k-1}           if p^{k-1} ∣ n.natAbs but p^k ∤ n.natAbs,
                0                  otherwise. Direct corollary of the Hölder formula.
    Proved 2026-06-22. -/
theorem ramanujanSumC_prime_pow (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 0 < k) (n : ℤ) :
    ramanujanSumC (p ^ k) n =
    if p ^ k ∣ n.natAbs then ↑(p ^ (k - 1)) * ((↑p : ℂ) - 1)
    else if p ^ (k - 1) ∣ n.natAbs then -(↑(p ^ (k - 1)) : ℂ)
    else 0 := by
  have hpkpos : 0 < p ^ k := pow_pos hp.pos k
  rw [ramanujanSum_eq_moebius_sum (p ^ k) hpkpos n,
      gcd_divisors_filter (p ^ k) n.natAbs hpkpos, Finset.sum_filter,
      Nat.sum_divisors_prime_pow hp]
  have hpow_div : ∀ i ≤ k, p ^ k / p ^ i = p ^ (k - i) := fun i hi =>
    (show p ^ k = p ^ i * p ^ (k - i) by rw [← pow_add, Nat.add_sub_cancel' hi]) ▸
    Nat.mul_div_cancel_left _ (pow_pos hp.pos i)
  rw [show k + 1 = (k - 1) + 1 + 1 from by omega, Finset.sum_range_succ, Finset.sum_range_succ]
  have h_ik : (k - 1) + 1 = k := Nat.sub_add_cancel hk
  -- Term for i = k: μ(p^0) = μ(1) = 1
  have hk_term : (if p ^ ((k-1)+1) ∣ n.natAbs then
      (↑(moebius (p ^ k / p ^ ((k-1)+1))) : ℂ) * ↑(p ^ ((k-1)+1)) else 0) =
      if p ^ k ∣ n.natAbs then ↑(p ^ k) else 0 := by
    rw [h_ik, hpow_div k le_rfl, Nat.sub_self, pow_zero]
    simp only [moebius_apply_one, Int.cast_one, one_mul]
  -- Term for i = k-1: μ(p^1) = μ(p) = -1
  have hk1_term : (if p ^ (k-1) ∣ n.natAbs then
      (↑(moebius (p ^ k / p ^ (k-1))) : ℂ) * ↑(p ^ (k-1)) else 0) =
      if p ^ (k-1) ∣ n.natAbs then -(↑(p ^ (k-1)) : ℂ) else 0 := by
    rw [hpow_div (k-1) (Nat.sub_le k 1), show k - (k-1) = 1 from by omega, pow_one]
    have hμp : (moebius p : ℂ) = -1 := by exact_mod_cast moebius_apply_prime hp
    rw [hμp]; congr 1; ring
  -- Terms for i < k-1: μ(p^(k-i)) = 0 since k-i ≥ 2
  have hrange_zero : ∑ x ∈ Finset.range (k-1),
      (if p^x ∣ n.natAbs then (↑(moebius (p^k / p^x)) : ℂ) * ↑(p^x) else 0) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    have hi_lt : i < k - 1 := Finset.mem_range.mp hi
    rw [hpow_div i (by omega : i ≤ k)]
    have hμ0 : (moebius (p ^ (k - i)) : ℂ) = 0 := by
      exact_mod_cast (show (moebius (p ^ (k - i)) : ℤ) = 0 from by
        rw [moebius_apply_prime_pow hp (by omega : k - i ≠ 0), if_neg (by omega : k - i ≠ 1)])
    simp [hμ0]
  rw [hrange_zero, zero_add, hk1_term, hk_term]
  by_cases hpk : p ^ k ∣ n.natAbs
  · have hpk1 : p ^ (k-1) ∣ n.natAbs := dvd_trans (Nat.pow_dvd_pow p (Nat.sub_le k 1)) hpk
    rw [if_pos hpk, if_pos hpk1, if_pos hpk]
    push_cast
    have hpkC : (p:ℂ)^k = (p:ℂ)^(k-1) * (p:ℂ) := by
      conv_lhs => rw [show k = k - 1 + 1 from (Nat.sub_add_cancel hk).symm, pow_succ]
    rw [hpkC]; ring
  · rw [if_neg hpk]
    by_cases hpk1 : p ^ (k-1) ∣ n.natAbs
    · rw [if_pos hpk1, if_neg hpk]; push_cast; ring
    · simp [if_neg hpk, if_neg hpk1]

-- ============================================================
-- THEOREM #18: Ramanujan sum is even in n
-- ============================================================

/-- **Ramanujan sum is even** (B6, Theorem #18): c_q(-n) = c_q(n).
    The Hölder formula expresses ramanujanSumC q n = ∑_{d|gcd(q,n.natAbs)} μ(q/d)·d,
    which depends on n only through n.natAbs. Since (-n).natAbs = n.natAbs, the result
    is immediate. Proved 2026-06-25. -/
theorem ramanujanSumC_neg (q : ℕ) (hq : 0 < q) (n : ℤ) :
    ramanujanSumC q (-n) = ramanujanSumC q n := by
  rw [ramanujanSum_eq_moebius_sum q hq (-n), ramanujanSum_eq_moebius_sum q hq n,
      Int.natAbs_neg]

-- ============================================================
-- THEOREM #51: Ramanujan sum at coprime argument = Möbius function
-- ============================================================

/-- **Ramanujan sum at coprime argument** (B8, Theorem #51).
    When gcd(q, n.natAbs) = 1, the Hölder formula collapses to a single term:
      c_q(n) = ∑_{d | gcd(q,n)} μ(q/d)·d = μ(q/1)·1 = μ(q).
    This is the key identity linking the Ramanujan sum to the singular series
    coefficient μ(q)/φ(q) in the Hardy-Littlewood B8 major arc formula.
    Proved 2026-07-04. -/
theorem ramanujanSumC_coprime (q : ℕ) (hq : 0 < q) (n : ℤ)
    (hn : Nat.Coprime q n.natAbs) :
    ramanujanSumC q n = ↑(ArithmeticFunction.moebius q) := by
  rw [ramanujanSum_eq_moebius_sum q hq n]
  rw [show Nat.gcd q n.natAbs = 1 from hn]
  simp [Nat.divisors_one, Nat.div_one]

end GoldbachBridge
