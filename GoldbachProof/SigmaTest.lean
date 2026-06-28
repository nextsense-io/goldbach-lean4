import Mathlib.Tactic

-- Test injectivity of d ↦ q/d on divisors
example (q d₁ d₂ : ℕ) (h1 : d₁ ∣ q) (h2 : d₂ ∣ q) (hq : 0 < q) (h : q / d₁ = q / d₂) : d₁ = d₂ := by
  have := Nat.div_dvd_of_dvd h1
  have := Nat.div_dvd_of_dvd h2
  omega

-- Test exp argument ring equality
example (b n q d : ℂ) (hd : d ≠ 0) (hq : q ≠ 0) (hqd : d * q = q * d) (hqdC : (q / d) * d = q) :
    2 * Real.pi * Complex.I * (b * d) * n / q = 2 * Real.pi * Complex.I * b * n / (q / d) := by
  field_simp
  ring

-- Or with Nat types
example (q d : ℕ) (b n : ℤ) (hd : 0 < d) (hq : 0 < q) (hdq : d ∣ q) :
    (2 : ℂ) * Real.pi * Complex.I * ↑(b * d) * n / q = 
    2 * Real.pi * Complex.I * b * n / (q / d) := by
  push_cast
  have hqdC : ((q / d : ℕ) : ℂ) * d = q := by exact_mod_cast Nat.div_mul_cancel hdq
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hqd0 : ((q / d : ℕ) : ℂ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    exact (Nat.div_pos (Nat.le_of_dvd hq hdq) hd).ne'
  field_simp [hqdC]
  ring
