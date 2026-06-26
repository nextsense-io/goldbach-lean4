/-
Ramanujan sum multiplicativity: c_{mn}(k) = c_m(k) · c_n(k) for gcd(m,n)=1.

Proof strategy:
1. Apply Hölder formula (ramanujanSum_eq_moebius_sum) to both sides.
2. Use gcd(mn,k) = gcd(m,k)*gcd(n,k) [Nat.Coprime.mul_gcd].
3. Use Nat.divisors_mul to split divisors of the product (Pointwise).
4. Convert sum over pointwise product to double sum via injectivity (d₁,d₂)→d₁*d₂.
5. Expand product of sums on RHS using Finset.sum_mul + simp_rw Finset.mul_sum.
6. Term equality per (d₁,d₂): μ(mn/(d₁d₂))*(d₁d₂) = (μ(m/d₁)*d₁)*(μ(n/d₂)*d₂).
   Uses: Nat.mul_div_mul_comm + isMultiplicative_moebius + ring.
-/
import GoldbachProof.RamanujanHölder
import Mathlib.Data.Finset.NatDivisors

open scoped Pointwise
open ArithmeticFunction

namespace GoldbachBridge

private lemma moebius_mul_coprime (a b : ℕ) (hcop : a.Coprime b) :
    (moebius (a * b) : ℂ) = (moebius a : ℂ) * (moebius b : ℂ) :=
  mod_cast isMultiplicative_moebius.map_mul_of_coprime hcop

/-- **Ramanujan sum is multiplicative** (B6, Theorem #21):
    For coprime m, n: c_{mn}(k) = c_m(k) · c_n(k).
    Proved 2026-06-26. -/
theorem ramanujanSumC_multiplicative (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) (k : ℤ) :
    ramanujanSumC (m * n) k = ramanujanSumC m k * ramanujanSumC n k := by
  rw [ramanujanSum_eq_moebius_sum (m * n) (Nat.mul_pos hm hn) k,
      ramanujanSum_eq_moebius_sum m hm k,
      ramanujanSum_eq_moebius_sum n hn k]
  set gm := Nat.gcd m k.natAbs
  set gn := Nat.gcd n k.natAbs
  have hgcd_eq : Nat.gcd (m * n) k.natAbs = gm * gn := hcop.mul_gcd k.natAbs
  rw [hgcd_eq]
  have hgm_m : gm ∣ m := Nat.gcd_dvd_left m k.natAbs
  have hgn_n : gn ∣ n := Nat.gcd_dvd_left n k.natAbs
  rw [Nat.divisors_mul gm gn]
  -- Injectivity: (d₁,d₂) ↦ d₁*d₂ is injective on gm.divisors ×ˢ gn.divisors
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) ↑(gm.divisors ×ˢ gn.divisors) := by
    intro ⟨d₁, d₂⟩ hp ⟨d₁', d₂'⟩ hp' heq
    dsimp only at heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Nat.mem_divisors] at hp hp'
    obtain ⟨⟨hd₁gm, hgm0⟩, ⟨hd₂gn, _⟩⟩ := hp
    obtain ⟨⟨hd₁'gm, _⟩, ⟨hd₂'gn, _⟩⟩ := hp'
    have hd₁m : d₁ ∣ m := dvd_trans hd₁gm hgm_m
    have hd₂n : d₂ ∣ n := dvd_trans hd₂gn hgn_n
    have hd₁'m : d₁' ∣ m := dvd_trans hd₁'gm hgm_m
    have hd₂'n : d₂' ∣ n := dvd_trans hd₂'gn hgn_n
    have hcop_d₁_d₂' : d₁.Coprime d₂' := (hcop.coprime_dvd_left hd₁m).coprime_dvd_right hd₂'n
    have hcop_d₁'_d₂ : d₁'.Coprime d₂ := (hcop.coprime_dvd_left hd₁'m).coprime_dvd_right hd₂n
    have hd₁_d₁' : d₁ ∣ d₁' := hcop_d₁_d₂'.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right d₁ d₂)
    have hd₁'_d₁ : d₁' ∣ d₁ := hcop_d₁'_d₂.dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right d₁' d₂')
    have heq₁ : d₁ = d₁' := Nat.dvd_antisymm hd₁_d₁' hd₁'_d₁
    have hgm_pos : 0 < gm := Nat.pos_of_ne_zero (fun h => hgm0 (by simpa using h))
    have hd₁pos : 0 < d₁ := Nat.pos_of_dvd_of_pos hd₁gm hgm_pos
    exact Prod.ext heq₁ (Nat.eq_of_mul_eq_mul_left hd₁pos (heq₁ ▸ heq))
  rw [Finset.mul_def, Finset.sum_image hinj]
  -- LHS: ∑ p ∈ gm.divisors ×ˢ gn.divisors, μ(mn/(p.1*p.2)) * (p.1*p.2)
  -- Convert to double sum
  rw [show ∑ x ∈ gm.divisors ×ˢ gn.divisors,
          (moebius (m * n / (x.1 * x.2)) : ℂ) * ↑(x.1 * x.2) =
      ∑ d₁ ∈ gm.divisors, ∑ d₂ ∈ gn.divisors,
          (moebius (m * n / (d₁ * d₂)) : ℂ) * ↑(d₁ * d₂) from
    Finset.sum_product' _ _ (fun d₁ d₂ => (moebius (m * n / (d₁ * d₂)) : ℂ) * ↑(d₁ * d₂))]
  -- RHS: expand product of sums to double sum
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  -- Term equality per (d₁, d₂)
  apply Finset.sum_congr rfl; intro d₁ hd₁
  apply Finset.sum_congr rfl; intro d₂ hd₂
  have hd₁m : d₁ ∣ m := dvd_trans (Nat.mem_divisors.mp hd₁).1 hgm_m
  have hd₂n : d₂ ∣ n := dvd_trans (Nat.mem_divisors.mp hd₂).1 hgn_n
  rw [Nat.mul_div_mul_comm hd₁m hd₂n]
  rw [moebius_mul_coprime _ _
    ((hcop.coprime_dvd_left (Nat.div_dvd_of_dvd hd₁m)).coprime_dvd_right (Nat.div_dvd_of_dvd hd₂n))]
  push_cast; ring

end GoldbachBridge
