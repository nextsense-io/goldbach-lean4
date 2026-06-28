/-
Copyright (c) 2026 JB Berent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JB Berent
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Rayleigh quotient eigenbasis decomposition for real symmetric matrices

For a real symmetric matrix `A` with eigenvalues `hA.eigenvalues` and orthonormal
eigenbasis `hA.eigenvectorBasis`, this file proves the spectral decomposition of the
Rayleigh quotient in `dotProduct` form, together with the corresponding Parseval
identity and two immediate consequences.

## Main results

* `Matrix.IsHermitian.dotProduct_mulVec_eq_sum_eigenvalues_mul_sq`:
  `x ⬝ᵥ A *ᵥ x = ∑ i, hA.eigenvalues i * (⇑(hA.eigenvectorBasis i) ⬝ᵥ x) ^ 2`.
* `Matrix.IsHermitian.sum_sq_dotProduct_eigenvectorBasis`: the Parseval identity for the
  eigenbasis coefficients, `∑ i, (⇑(hA.eigenvectorBasis i) ⬝ᵥ x) ^ 2 = ∑ j, x j ^ 2`.
* `Matrix.IsHermitian.finrank_span_range_eigenvectorBasis`: any subfamily of `k`
  eigenvectors (as plain functions `n → ℝ`) spans a subspace of dimension `k`.
* `Matrix.IsHermitian.exists_eigenvalues_ge_sum_div_card`: some eigenvalue is at least
  the average of all matrix entries.
* `Matrix.IsHermitian.exists_eigenvalues_ge_trace_div_card`: some eigenvalue is at least
  the average eigenvalue `A.trace / card n`.

These lemmas express, in concrete `Matrix`/`dotProduct` language, facts that are
classically stated via the spectral theorem; they are the basic ingredients for
minimax (Courant-Fischer) characterizations of eigenvalues and for eigenvalue
interlacing theorems.

## Notes

The results are stated over `ℝ`. Generalizing to `RCLike 𝕜` requires replacing
`(v ⬝ᵥ x) ^ 2` with `‖⟪v, x⟫‖ ^ 2` and is left to future work.

## References

* [R. A. Horn, C. R. Johnson, *Matrix Analysis*, Chapter 4][horn-johnson-2013]

## Tags

rayleigh quotient, spectral theorem, hermitian matrix, eigenvalues, parseval
-/

open Matrix WithLp

namespace Matrix

namespace IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ} (hA : A.IsHermitian)

/-- **Rayleigh quotient eigenbasis decomposition.** For a real symmetric matrix `A` with
eigenvalues `λᵢ` and orthonormal eigenbasis `vᵢ`, the quadratic form decomposes as
`x ⬝ᵥ A *ᵥ x = ∑ i, λᵢ * (vᵢ ⬝ᵥ x) ^ 2`. -/
theorem dotProduct_mulVec_eq_sum_eigenvalues_mul_sq (x : n → ℝ) :
    x ⬝ᵥ A *ᵥ x =
      ∑ i, hA.eigenvalues i * ((⇑(hA.eigenvectorBasis i) : n → ℝ) ⬝ᵥ x) ^ 2 := by
  set ev := hA.eigenvalues
  set b := hA.eigenvectorBasis
  -- Expand `A *ᵥ x` in the eigenbasis: `A *ᵥ x = ∑ i, (λᵢ * (vᵢ ⬝ᵥ x)) • vᵢ`.
  have expand_Ax : A *ᵥ x = ∑ i, (ev i * (⇑(b i) : n → ℝ) ⬝ᵥ x) • (⇑(b i) : n → ℝ) := by
    set x' : EuclideanSpace ℝ n := (WithLp.equiv 2 (n → ℝ)).symm x
    -- Decompose `x` in the eigenbasis, transported to the plain function space.
    have hx_sum : x = ∑ i, b.repr x' i • (⇑(b i) : n → ℝ) := by
      have h := congrArg (WithLp.linearEquiv 2 ℝ (n → ℝ)) (b.sum_repr x').symm
      simp only [map_sum, LinearEquiv.map_smul] at h
      exact h
    rw [hx_sum, mulVec_sum]
    have step : ∀ i, A *ᵥ (b.repr x' i • (⇑(b i) : n → ℝ)) =
        (ev i * b.repr x' i) • (⇑(b i) : n → ℝ) := by
      intro i
      rw [mulVec_smul, hA.mulVec_eigenvectorBasis, smul_smul, mul_comm]
    simp_rw [step]
    -- The basis coefficients are exactly the dot products with the eigenvectors.
    have hrep : ∀ i, b.repr x' i = (⇑(b i) : n → ℝ) ⬝ᵥ x := by
      intro i
      rw [b.repr_apply_apply, EuclideanSpace.inner_eq_star_dotProduct]
      simp only [star_trivial]
      rw [dotProduct_comm]; rfl
    conv_rhs => simp only [← hx_sum]
    simp only [hrep]
  rw [expand_Ax, dotProduct_sum]
  simp_rw [dotProduct_smul, smul_eq_mul]
  congr 1; ext i
  rw [dotProduct_comm x (⇑(b i) : n → ℝ)]
  ring

/-- **Parseval identity for the eigenbasis.** The squared eigenbasis coefficients of a
vector sum to its squared Euclidean norm:
`∑ i, (vᵢ ⬝ᵥ x) ^ 2 = ∑ j, x j ^ 2`. -/
theorem sum_sq_dotProduct_eigenvectorBasis (x : n → ℝ) :
    ∑ i, ((⇑(hA.eigenvectorBasis i) : n → ℝ) ⬝ᵥ x) ^ 2 = ∑ j, x j ^ 2 := by
  set b := hA.eigenvectorBasis
  set x' : EuclideanSpace ℝ n := (WithLp.equiv 2 (n → ℝ)).symm x with hx'
  have h_parseval := b.sum_sq_inner_right x'
  have h_norm := EuclideanSpace.norm_sq_eq x'
  have h_inner : ∀ i, @inner ℝ _ _ (b i) x' = (⇑(b i) : n → ℝ) ⬝ᵥ x := by
    intro i
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have : x'.ofLp = x := rfl
    simp [star_trivial, this, dotProduct_comm]
  calc ∑ i, ((⇑(b i) : n → ℝ) ⬝ᵥ x) ^ 2
      = ∑ i, (@inner ℝ _ _ (b i) x') ^ 2 := by
        congr 1; ext i; rw [h_inner]
    _ = ‖x'‖ ^ 2 := h_parseval
    _ = ∑ j, ‖x'.ofLp j‖ ^ 2 := h_norm
    _ = ∑ j, x j ^ 2 := by
        congr 1; ext j
        have : x'.ofLp j = x j := rfl
        rw [this, Real.norm_eq_abs, sq_abs]

/-- Any subfamily of `k` eigenvectors of a real symmetric matrix, regarded as plain
functions `n → ℝ`, spans a subspace of dimension `k`. -/
theorem finrank_span_range_eigenvectorBasis {ι : Type*} [Fintype ι] (f : ι ↪ n) :
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range fun i : ι => (⇑(hA.eigenvectorBasis (f i)) : n → ℝ))) =
      Fintype.card ι := by
  have hli : LinearIndependent ℝ
      (fun i : ι => (⇑(hA.eigenvectorBasis (f i)) : n → ℝ)) := by
    have hort : Orthonormal ℝ fun i : ι => hA.eigenvectorBasis (f i) :=
      hA.eigenvectorBasis.orthonormal.comp _ f.injective
    exact hort.linearIndependent.map'
      (WithLp.linearEquiv 2 ℝ (n → ℝ)).toLinearMap
      (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (n → ℝ)).injective)
  exact finrank_span_eq_card hli

variable [Nonempty n]

/-- Some eigenvalue of a real symmetric matrix is at least the average of all entries.
This follows from evaluating the Rayleigh quotient at the all-ones vector. -/
theorem exists_eigenvalues_ge_sum_div_card :
    ∃ i, (∑ p, ∑ q, A p q) / Fintype.card n ≤ hA.eigenvalues i := by
  by_contra hcon
  push_neg at hcon
  set S := ∑ p, ∑ q, A p q with hS
  set ones : n → ℝ := fun _ => 1 with hones
  set c : n → ℝ := fun i => (⇑(hA.eigenvectorBasis i) : n → ℝ) ⬝ᵥ ones with hc
  have hm : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hdot : ones ⬝ᵥ A *ᵥ ones = S := by
    simp [dotProduct, Matrix.mulVec, hones, hS]
  have hdecomp := hA.dotProduct_mulVec_eq_sum_eigenvalues_mul_sq ones
  have hpars := hA.sum_sq_dotProduct_eigenvectorBasis ones
  have hpm : ∑ j, (ones j) ^ 2 = (Fintype.card n : ℝ) := by simp [hones]
  rw [hpm] at hpars
  have hex : ∃ i, 0 < c i ^ 2 := by
    by_contra hno
    push_neg at hno
    have hzero : ∑ i, c i ^ 2 = 0 :=
      le_antisymm (Finset.sum_nonpos fun i _ => hno i)
        (Finset.sum_nonneg fun i _ => sq_nonneg _)
    rw [hc] at hzero
    rw [hzero] at hpars
    linarith
  obtain ⟨i₀, hi₀⟩ := hex
  have hlt : ∑ i, hA.eigenvalues i * c i ^ 2 <
      ∑ i, (S / Fintype.card n) * c i ^ 2 :=
    Finset.sum_lt_sum
      (fun i _ => mul_le_mul_of_nonneg_right (hcon i).le (sq_nonneg _))
      ⟨i₀, Finset.mem_univ _, mul_lt_mul_of_pos_right (hcon i₀) hi₀⟩
  have hrhs : ∑ i, (S / Fintype.card n) * c i ^ 2 = S := by
    rw [← Finset.mul_sum, hc, hpars]
    field_simp
  rw [hdot] at hdecomp
  rw [hc, ← hdecomp, hrhs] at hlt
  exact lt_irrefl S hlt

/-- Some eigenvalue of a real symmetric matrix is at least the average eigenvalue
`A.trace / card n`. -/
theorem exists_eigenvalues_ge_trace_div_card :
    ∃ i, A.trace / Fintype.card n ≤ hA.eigenvalues i := by
  have htr : A.trace = ∑ i, hA.eigenvalues i := by
    simpa using hA.trace_eq_sum_eigenvalues
  have hm : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ _i : n, A.trace / (Fintype.card n : ℝ) ≤ ∑ i, hA.eigenvalues i := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm,
      div_mul_cancel₀ _ (ne_of_gt hm)]
    exact le_of_eq htr
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨i, hi⟩

end IsHermitian

end Matrix
