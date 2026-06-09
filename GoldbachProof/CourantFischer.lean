/-
  Courant-Fischer Minimax Theorem — Toward Eliminating Cauchy Interlacing Axioms
  ==============================================================================

  This file formalizes algebraic ingredients of the Courant-Fischer minimax
  characterization of eigenvalues for real symmetric matrices, with the goal
  of replacing the two axioms in CauchyInterlacing.lean:
    - cauchy_interlacing_rank1
    - cauchy_interlacing_full

  MATHEMATICAL CONTENT:
  For a real symmetric m x m matrix A with eigenvalues
  ev_1 >= ev_2 >= ... >= ev_m (decreasing, Mathlib convention):

    ev_k = max_{dim V = k} min_{x in V, ||x||=1} <x, Ax>
         = min_{dim W = m-k+1} max_{x in W, ||x||=1} <x, Ax>

  We prove all algebraic ingredients and identify the precise API gap
  connecting to Mathlib's eigenvectorBasis.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped Matrix

namespace CourantFischer

/-! ## Stage 1: Subspace Dimension Lemmas -/

/-- Two subspaces whose dimensions sum to more than the ambient dimension
    must have nontrivial intersection. -/
theorem submodule_intersection_nontrivial
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (S T : Submodule F V)
    (h : Module.finrank F S + Module.finrank F T > Module.finrank F V) :
    S ⊓ T ≠ ⊥ := by
  intro h_bot
  have h_eq := Submodule.finrank_sup_add_finrank_inf_eq S T
  have h_inf : Module.finrank F ↥(S ⊓ T) = 0 := by
    rw [h_bot]; exact finrank_bot F V
  rw [h_inf] at h_eq
  have h_sup := Submodule.finrank_le (S ⊔ T)
  omega

/-- Corollary with explicit dimension bounds. -/
theorem intersection_nontrivial_of_dims
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (S T : Submodule F V)
    {k l : ℕ}
    (hS : Module.finrank F S ≥ k)
    (hT : Module.finrank F T ≥ l)
    (h_sum : k + l > Module.finrank F V) :
    S ⊓ T ≠ ⊥ := by
  apply submodule_intersection_nontrivial
  omega

/-! ## Stage 2: Rayleigh Quotient on Diagonal Matrices -/

/-- For a unit vector, the Rayleigh quotient of a diagonal matrix is at least d_min. -/
theorem rayleigh_diagonal_ge_min
    {m : ℕ} (d : Fin m → ℝ) (d_min : ℝ) (w : Fin m → ℝ)
    (hd : ∀ i, d i ≥ d_min)
    (hw_nonneg : ∀ i, w i ≥ 0)
    (hw_sum : ∑ i : Fin m, w i = 1) :
    ∑ i : Fin m, d i * w i ≥ d_min := by
  have key : ∑ i : Fin m, d i * w i ≥ ∑ i : Fin m, d_min * w i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hd i) (hw_nonneg i)
  calc ∑ i : Fin m, d i * w i
      ≥ ∑ i : Fin m, d_min * w i := key
    _ = d_min * ∑ i : Fin m, w i := by rw [← Finset.mul_sum]
    _ = d_min * 1 := by rw [hw_sum]
    _ = d_min := mul_one d_min

/-! ## Stage 3: Algebraic Courant-Fischer Witnesses

The key algebraic content: if eigenvalues are antitone (decreasing) and
we have coefficient vectors with appropriate support, we get the bounds. -/

/-- The ">=" direction: weighted sum with support on first k indices
    is at least the k-th eigenvalue. -/
theorem cf_lower_witness
    {m : ℕ} (ev : Fin m → ℝ) (c : Fin m → ℝ)
    (k : Fin m)
    (h_anti : Antitone ev)
    (hc_nn : ∀ i, c i ≥ 0)
    (hc_sum : ∑ i : Fin m, c i = 1)
    (h_supp : ∀ i, i > k → c i = 0) :
    ∑ i : Fin m, ev i * c i ≥ ev k := by
  have h1 : ∑ i : Fin m, ev i * c i ≥ ∑ i : Fin m, ev k * c i := by
    apply Finset.sum_le_sum
    intro i _
    by_cases h : i ≤ k
    · exact mul_le_mul_of_nonneg_right (h_anti h) (hc_nn i)
    · push_neg at h; rw [h_supp i h]; simp
  calc ∑ i : Fin m, ev i * c i
      ≥ ∑ i : Fin m, ev k * c i := h1
    _ = ev k * ∑ i : Fin m, c i := by rw [← Finset.mul_sum]
    _ = ev k * 1 := by rw [hc_sum]
    _ = ev k := mul_one _

/-- The "<=" direction: weighted sum with support on indices >= k
    is at most the k-th eigenvalue. -/
theorem cf_upper_witness
    {m : ℕ} (ev : Fin m → ℝ) (c : Fin m → ℝ)
    (k : Fin m)
    (h_anti : Antitone ev)
    (hc_nn : ∀ i, c i ≥ 0)
    (hc_sum : ∑ i : Fin m, c i = 1)
    (h_supp : ∀ i, i < k → c i = 0) :
    ∑ i : Fin m, ev i * c i ≤ ev k := by
  have h1 : ∑ i : Fin m, ev i * c i ≤ ∑ i : Fin m, ev k * c i := by
    apply Finset.sum_le_sum
    intro i _
    by_cases h : k ≤ i
    · exact mul_le_mul_of_nonneg_right (h_anti h) (hc_nn i)
    · push_neg at h; rw [h_supp i h]; simp
  calc ∑ i : Fin m, ev i * c i
      ≤ ∑ i : Fin m, ev k * c i := h1
    _ = ev k * ∑ i : Fin m, c i := by rw [← Finset.mul_sum]
    _ = ev k * 1 := by rw [hc_sum]
    _ = ev k := mul_one _

/-! ## Stage 4: Rank-1 Perturbation Bound -/

/-- For x orthogonal to u with ||x|| = 1, the Rayleigh quotient of
    H = D - lam * uu^T satisfies <x, Hx> >= d_min. -/
theorem rank1_orthogonal_bound
    {m : ℕ} (d : Fin m → ℝ) (d_min lam : ℝ)
    (w : Fin m → ℝ) (inner_sq : ℝ)
    (hd : ∀ i, d i ≥ d_min)
    (hw_nn : ∀ i, w i ≥ 0)
    (hw_sum : Finset.sum Finset.univ w = 1)
    (h_orth : inner_sq = 0) :
    Finset.sum Finset.univ (fun i => d i * w i) - lam * inner_sq ≥ d_min := by
  rw [h_orth, mul_zero, sub_zero]
  have key : Finset.sum Finset.univ (fun i => d i * w i) ≥
      Finset.sum Finset.univ (fun i => d_min * w i) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hd i) (hw_nn i)
  calc Finset.sum Finset.univ (fun i => d i * w i)
      ≥ Finset.sum Finset.univ (fun i => d_min * w i) := key
    _ = d_min * Finset.sum Finset.univ w := by rw [← Finset.mul_sum]
    _ = d_min * 1 := by rw [hw_sum]
    _ = d_min := mul_one d_min

/-! ## Stage 5: Rayleigh Quotient Spectral Decomposition

Bridge from Mathlib's `Matrix.IsHermitian.eigenvectorBasis` to the algebraic
witnesses in Stages 2-4.

Key lemma: for real symmetric A with eigenbasis {vᵢ} and eigenvalues {λᵢ},
  ⟨x, Ax⟩ = ∑ᵢ λᵢ * |⟨vᵢ, x⟩|²

This follows from A = U D U^T (spectral theorem). -/

open Matrix in
/-- The Rayleigh quotient of a Hermitian matrix in its eigenbasis decomposes as
    a weighted sum of eigenvalues.

    For Hermitian A with eigenbasis {vᵢ} and eigenvalues {λᵢ}:
      x^T A x = ∑ᵢ λᵢ * (vᵢ · x)²

    Proof strategy:
    1. sum_inner_mul_inner: ⟪x, Ax⟫ = ∑ᵢ ⟪x, vᵢ⟫ * ⟪vᵢ, Ax⟫
    2. IsSymmetric: ⟪vᵢ, Ax⟫ = ⟪Avᵢ, x⟫ = λᵢ * ⟪vᵢ, x⟫
    3. Real symmetry: ⟪x, vᵢ⟫ * λᵢ * ⟪vᵢ, x⟫ = λᵢ * (vᵢ · x)²

    The proof navigates the EuclideanSpace ↔ (Fin m → ℝ) bridge through
    WithLp.linearEquiv, using Mathlib's spectral theorem and eigenbasis API. -/
theorem rayleigh_eigenbasis_decomposition
    {m : ℕ} [NeZero m]
    (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsHermitian)
    (x : Fin m → ℝ) :
    dotProduct x (A *ᵥ x) =
      ∑ i : Fin m, hA.eigenvalues i * (dotProduct (⇑(hA.eigenvectorBasis i)) x) ^ 2 := by
  -- Let U = eigenvectorUnitary, so A = U * diagonal(λ) * star(U)
  -- and star(U) * U = 1 (unitary).
  -- Key idea: express dotProduct x (A *ᵥ x) using the eigenbasis coordinates.
  -- Let c : Fin m → ℝ be the coordinates of x in the eigenbasis,
  -- i.e., c i = dotProduct (eigenvector i) x.
  -- Then dotProduct x (A *ᵥ x) = ∑ i, eigenvalue i * c i ^ 2.
  --
  -- We use the spectral theorem: A = U * D * U*, and mulVec_eigenvectorBasis.
  set U := hA.eigenvectorUnitary
  set ev := hA.eigenvalues
  set b := hA.eigenvectorBasis
  -- Step 1: Expand A *ᵥ x using eigenbasis
  -- A *ᵥ x = ∑ i, (ev i * dotProduct (b i) x) • (b i)
  -- This is the standard expansion: apply A to x written in eigenbasis.
  have expand_Ax : A *ᵥ x = ∑ i : Fin m,
      (ev i * dotProduct (⇑(b i)) x) • ⇑(b i) := by
    -- Use the spectral theorem: A = U * D * U*
    -- So A *ᵥ x = U *ᵥ (D *ᵥ (U* *ᵥ x))
    -- where (U* *ᵥ x)_j = dotProduct (col j of U) x = dotProduct (b j) x
    -- and (D *ᵥ c)_j = ev j * c j
    -- and (U *ᵥ d) = ∑ j, d j • (col j of U) = ∑ j, d j • (b j)
    --
    -- Instead, work directly: A *ᵥ x = A *ᵥ (∑ i, c_i • v_i)
    -- where c_i and v_i are the eigenbasis coordinates/vectors.
    -- We prove x = ∑ i, c_i • v_i using the orthonormal basis.
    -- Key: b.toBasis.sum_repr gives the decomposition in EuclideanSpace.
    -- Since WithLp is a type synonym, we can use funext to bridge.
    have key : ∀ (y : EuclideanSpace ℝ (Fin m)),
        (WithLp.equiv 2 (Fin m → ℝ)) y = y := fun _ => rfl
    set x' : EuclideanSpace ℝ (Fin m) := (WithLp.equiv 2 (Fin m → ℝ)).symm x
    have hx' : x = (WithLp.equiv 2 (Fin m → ℝ)) x' := rfl
    -- x' = ∑ i, b.repr x' i • b i (basis decomposition in EuclideanSpace)
    have hdecomp := b.sum_repr x'
    -- Coerce: for each term, ⇑(c • b i) = c • ⇑(b i) since WithLp preserves smul
    -- x = ∑ i, b.repr x' i • ⇑(b i)   in (Fin m → ℝ)
    -- From hdecomp: x' = ∑ i, b.repr x' i • b i
    -- Apply (WithLp.equiv) to get: x = ∑ i, b.repr x' i • ⇑(b i)
    -- But more directly: A *ᵥ x = A *ᵥ ⇑(x')
    -- Since mulVec works on (Fin m → ℝ) and ⇑(b i) : Fin m → ℝ:
    -- A *ᵥ x = ∑ i, b.repr x' i • (A *ᵥ ⇑(b i))  [by linearity]
    --        = ∑ i, b.repr x' i • (ev i • ⇑(b i))  [by eigenvector eq]
    --        = ∑ i, (ev i * b.repr x' i) • ⇑(b i)  [by smul_comm]
    -- We need: b.repr x' i = dotProduct (⇑(b i)) x
    -- Apply funext to the decomposition
    -- Use b.toBasis.sum_repr to decompose x' in eigenbasis,
    -- then convert to (Fin m → ℝ) pointwise.
    have hx_sum : x = ∑ i : Fin m, b.repr x' i • ⇑(b i) := by
      -- hdecomp : ∑ i, b.repr x' i • b i = x'  (in EuclideanSpace)
      -- Need:     x = ∑ i, b.repr x' i • (b i).ofLp  (in Fin m → ℝ)
      -- Apply ofLp (AddEquiv) to hdecomp.symm
      -- hdecomp.symm : x' = ∑ i, b.repr x' i • b i  (in EuclideanSpace)
      -- Apply the linear equiv to convert to (Fin m → ℝ)
      have h := congrArg (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)) hdecomp.symm
      simp only [map_sum, LinearEquiv.map_smul] at h
      exact h
    rw [hx_sum, mulVec_sum]
    -- After mulVec_sum: goal is about ∑ i, A *ᵥ (c_i • v_i)
    -- Step: A *ᵥ (c • v) = c • (A *ᵥ v) = c • (ev i • v) = (ev i * c) • v
    have step : ∀ i, A *ᵥ ((b.repr x') i • ⇑(b i)) =
        (ev i * (b.repr x') i) • ⇑(b i) := by
      intro i
      rw [mulVec_smul, hA.mulVec_eigenvectorBasis]
      rw [smul_smul, mul_comm]
    simp_rw [step]
    -- Need: b.repr x' i = dotProduct (⇑(b i)) x for all i
    have hrep : ∀ i, (b.repr x') i = dotProduct (⇑(b i)) x := by
      intro i
      rw [b.repr_apply_apply, EuclideanSpace.inner_eq_star_dotProduct]
      simp only [star_trivial]
      rw [dotProduct_comm]; rfl
    -- Close by rewriting x back to its sum form and repr to dotProduct
    conv_rhs => simp only [← hx_sum]
    simp only [hrep]
  -- Step 2: Take dotProduct with x
  rw [expand_Ax, dotProduct_sum]
  simp_rw [dotProduct_smul, smul_eq_mul]
  -- Now goal should be:
  -- ∑ i, (ev i * dotProduct (b i) x) * dotProduct x (b i) = ∑ i, ev i * (dotProduct (b i) x) ^ 2
  congr 1; ext i
  rw [dotProduct_comm x (⇑(b i))]
  ring

/-! ## Stage 6: Eigenvector Subspace Dimension

For Courant-Fischer, we need that the span of eigenvectors {v₀,...,v_{k-1}}
has dimension k. -/

open Matrix in
/-- The span of the first k eigenvectors has dimension k.
    This connects `submodule_intersection_nontrivial` to the eigenbasis. -/
theorem eigenvector_span_dim
    {m : ℕ} [NeZero m]
    (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsHermitian)
    (k : ℕ) (hk : k ≤ m) :
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun (i : Fin k) => (⇑(hA.eigenvectorBasis (Fin.castLE hk i)) : Fin m → ℝ)))) = k := by
  -- The eigenvectors are orthonormal, hence linearly independent.
  -- k linearly independent vectors span a k-dimensional subspace.
  have hli : LinearIndependent ℝ
      (fun (i : Fin k) => (⇑(hA.eigenvectorBasis (Fin.castLE hk i)) : Fin m → ℝ)) := by
    set b := hA.eigenvectorBasis
    have hort : Orthonormal ℝ (fun i : Fin k => b (Fin.castLE hk i)) :=
      b.orthonormal.comp _ (Fin.castLE_injective hk)
    exact hort.linearIndependent.map'
      (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).toLinearMap
      (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).injective)
  have := finrank_span_eq_card hli
  rw [Fintype.card_fin] at this
  exact this

/-! ## Stage 7: Summary and Next Steps

### All 8 theorems fully proved (0 axioms, 0 sorry):
1. `submodule_intersection_nontrivial` — dim S + dim T > dim V => S ∩ T ≠ ⊥
2. `intersection_nontrivial_of_dims` — corollary with explicit bounds
3. `rayleigh_diagonal_ge_min` — ∑ dᵢ wᵢ ≥ d_min for unit weights
4. `cf_lower_witness` — ∑ evᵢ cᵢ ≥ ev_k when supported on [0,k]
5. `cf_upper_witness` — ∑ evᵢ cᵢ ≤ ev_k when supported on [k,m]
6. `rank1_orthogonal_bound` — ⟨x,Hx⟩ ≥ d_min when x ⊥ u
7. `rayleigh_eigenbasis_decomposition` — ⟨x, Ax⟩ = ∑ λᵢ (vᵢ·x)²
8. `eigenvector_span_dim` — span{v₀,...,v_{k-1}} has dimension k

### Remaining work to eliminate Cauchy interlacing axioms:
The algebraic ingredients are complete. To replace `cauchy_interlacing_rank1`
and `cauchy_interlacing_full` in CauchyInterlacing.lean, we need:
  1. Construct H = diagonal d - λ • vecMulVec u u as a Mathlib Matrix  ✓ (Stage 8)
  2. Prove H.IsHermitian (from diagonal.IsHermitian and vecMulVec symmetry) ✓ (Stage 8)
  3. Connect hH.eigenvalues to the abstract E in the axiom
  4. Apply eigenbasis decomposition + dimension intersection to get E₁ ≥ d_min
  5. Generalize to E_k ≥ d_{k-1} for full interlacing
-/

/-! ## Stage 8: Constructing H = D - λ·u·uᵀ and Proving IsHermitian

This bridges the abstract algebra (Stages 1-7) to concrete Mathlib matrix types.
We construct the rank-1 perturbation matrix and prove it's Hermitian,
enabling access to `eigenvectorBasis` and `eigenvalues`. -/

open Matrix in
/-- The rank-1 perturbation matrix H = diagonal d - lam • vecMulVec u u -/
noncomputable def rank1PerturbationMatrix
    {m : ℕ} (d : Fin m → ℝ) (lam : ℝ) (u : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  diagonal d - lam • vecMulVec u u

open Matrix in
/-- vecMulVec u u is symmetric (Hermitian) for real vectors.
    Uses conjTranspose_vecMulVec and star_trivial for ℝ. -/
theorem vecMulVec_self_isHermitian
    {m : ℕ} (u : Fin m → ℝ) :
    (vecMulVec u u).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_vecMulVec]
  simp [star_trivial]

open Matrix in
/-- Scalar multiple of a Hermitian matrix is Hermitian (for real scalars). -/
theorem isHermitian_smul_real
    {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) (hA : A.IsHermitian) :
    (c • A).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_smul, hA.eq]
  simp [star_trivial]

open Matrix in
/-- The rank-1 perturbation H = diagonal d - lam • vecMulVec u u is Hermitian.
    Proof: diagonal is Hermitian (real entries), vecMulVec u u is Hermitian,
    scalar multiple of Hermitian is Hermitian, difference of Hermitian is Hermitian. -/
theorem rank1Perturbation_isHermitian
    {m : ℕ} (d : Fin m → ℝ) (lam : ℝ) (u : Fin m → ℝ) :
    (rank1PerturbationMatrix d lam u).IsHermitian := by
  unfold rank1PerturbationMatrix
  exact (isHermitian_diagonal d).sub (isHermitian_smul_real _ lam (vecMulVec_self_isHermitian u))

open Matrix in
/-- The Rayleigh quotient of H on a vector orthogonal to u equals
    the Rayleigh quotient of diagonal d.
    For x with dotProduct u x = 0:
      dotProduct x (H *ᵥ x) = dotProduct x ((diagonal d) *ᵥ x) -/
theorem rank1Perturbation_rayleigh_orthogonal
    {m : ℕ} (d : Fin m → ℝ) (lam : ℝ) (u x : Fin m → ℝ)
    (h_orth : dotProduct u x = 0) :
    dotProduct x (rank1PerturbationMatrix d lam u *ᵥ x) =
    dotProduct x (diagonal d *ᵥ x) := by
  unfold rank1PerturbationMatrix
  -- H *ᵥ x = (diagonal d) *ᵥ x - lam • (vecMulVec u u *ᵥ x)
  simp only [sub_mulVec, dotProduct_sub]
  -- Show vecMulVec u u *ᵥ x = (dotProduct u x) • u
  have hvec : vecMulVec u u *ᵥ x = (dotProduct u x) • u := by
    ext i
    simp only [vecMulVec, mulVec, dotProduct, of_apply,
               Pi.smul_apply, smul_eq_mul]
    -- Goal: ∑ j, u i * u j * x j = (∑ j, u j * x j) * u i
    simp_rw [mul_assoc (u i)]
    rw [← Finset.mul_sum]
    ring
  -- The smul term: (lam • M) *ᵥ x = lam • (M *ᵥ x)
  have h_smul_vec : (lam • vecMulVec u u) *ᵥ x = lam • (vecMulVec u u *ᵥ x) := by
    ext i
    simp only [mulVec, vecMulVec, of_apply, Pi.smul_apply,
               smul_eq_mul, Matrix.smul_apply, dotProduct]
    simp_rw [mul_assoc lam]
    rw [← Finset.mul_sum]
  rw [h_smul_vec, hvec, h_orth, zero_smul, smul_zero, dotProduct_zero, sub_zero]

/-! ## Stage 9: Eigenvalue Ordering Bridge and Interlacing Proof

Dream insight (Morpheus 2026-04-11): Mathlib eigenvalues are antitone (largest first).
The CauchyInterlacing axiom uses monotone E (smallest first).
Bridge: `E i := hH.eigenvalues (Fin.rev i)` converts antitone → monotone.

Then prove `cauchy_interlacing_rank1` as a theorem:
  For H = D - λ·u·uᵀ, E₁ ≥ d_min.

Strategy: The Rayleigh quotient on u⊥ is ≥ d_min (Stage 8 ingredient).
Combined with dimension intersection (Stage 1), this proves E₁ ≥ d_min
via Courant-Fischer-style reasoning formalized directly. -/

open Matrix in
/-- Eigenvalues₀ of a Hermitian matrix (antitone) composed with Fin.rev are monotone.
    eigenvalues₀ : Fin (Fintype.card n) → ℝ is provably antitone.
    For Fin m matrices, Fintype.card (Fin m) = m, so eigenvalues₀ : Fin m → ℝ.
    Composing with Fin.rev (antitone) gives monotone (smallest first). -/
theorem eigenvalues₀_rev_monotone
    {m : ℕ} [NeZero m]
    (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsHermitian) :
    Monotone (hA.eigenvalues₀ ∘ Fin.rev) :=
  hA.eigenvalues₀_antitone.comp Fin.rev_anti

open Matrix in
/-- For the rank-1 perturbation H = D - λ·u·uᵀ, the Rayleigh quotient
    on any unit vector in u⊥ is at least d_min.
    This is the Rayleigh quotient version using the eigenbasis decomposition.

    Combined with the eigenbasis decomposition (rayleigh_eigenbasis_decomposition),
    for x ∈ u⊥ with ‖x‖² = 1:
      d_min ≤ ⟨x, Hx⟩ = ∑ᵢ λᵢ(H) (vᵢ·x)²

    This means d_min is a lower bound on the Rayleigh quotient of H restricted to u⊥. -/
theorem rank1Perturbation_rayleigh_lower_bound
    {m : ℕ} (d : Fin m → ℝ) (lam : ℝ) (u x : Fin m → ℝ)
    (d_min : ℝ)
    (h_orth : dotProduct u x = 0)
    (h_d_min : ∀ i, d i ≥ d_min)
    (h_unit : ∑ i : Fin m, x i ^ 2 = 1) :
    dotProduct x (rank1PerturbationMatrix d lam u *ᵥ x) ≥ d_min := by
  rw [rank1Perturbation_rayleigh_orthogonal d lam u x h_orth]
  -- Now need: dotProduct x ((diagonal d) *ᵥ x) ≥ d_min
  -- For diagonal: dotProduct x (diagonal d *ᵥ x) = ∑ i, d i * x i ^ 2
  have h_diag : dotProduct x (diagonal d *ᵥ x) = ∑ i : Fin m, d i * (x i ^ 2) := by
    simp only [dotProduct, mulVec, dotProduct]
    congr 1; ext i
    -- Goal: x i * ∑ j, diagonal d i j * x j = d i * x i ^ 2
    -- diagonal d i j = if i = j then d i else 0
    simp only [diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  rw [h_diag]
  -- Use rayleigh_diagonal_ge_min with w i = x i ^ 2
  exact rayleigh_diagonal_ge_min d d_min (fun i => x i ^ 2) h_d_min
    (fun i => sq_nonneg _) h_unit

/-! ## Stage 9.5: Rayleigh decomposition with eigenvalues₀

Key insight (Morpheus 2026-04-15): `eigenvalues` goes through a noncomputable
`equivOfCardEq` that cannot be shown order-preserving. Instead, use `eigenvalues₀`
(provably antitone) directly. The eigenbasis decomposition sum is invariant under
reindexing, so we can express it with eigenvalues₀. -/

open Matrix in
/-- The Rayleigh eigenbasis decomposition can equivalently use `eigenvalues₀`.
    Since `eigenvalues i = eigenvalues₀ (σ i)` and `eigenvectorBasis i = basis₀ (σ i)`
    where σ = (equivOfCardEq ..).symm, the sum ∑ᵢ eigenvalues(i) * (vᵢ·x)²
    equals ∑ⱼ eigenvalues₀(j) * (v₀ⱼ·x)² by reindexing via the bijection σ. -/
theorem rayleigh_eigenbasis_decomposition_eq_eigenvalues₀
    {m : ℕ} [NeZero m]
    (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsHermitian)
    (x : Fin m → ℝ) :
    ∑ i : Fin m, hA.eigenvalues i * (dotProduct (⇑(hA.eigenvectorBasis i)) x) ^ 2 =
    ∑ j : Fin (Fintype.card (Fin m)),
      hA.eigenvalues₀ j *
        (dotProduct (⇑(((isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis
          finrank_euclideanSpace) j)) x) ^ 2 := by
  -- eigenvalues i = eigenvalues₀ (σ i) where σ = equiv.symm
  -- eigenvectorBasis i = basis₀.reindex(equiv) i = basis₀ (equiv.symm i) = basis₀ (σ i)
  -- So the sum reindexes by σ (a bijection), leaving the value unchanged.
  set σ := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin m)))).symm
    with hσ
  -- Goal: ∑ i, (eigenvalues i) * (eigenvectorBasis i · x)² = ∑ j, (eigenvalues₀ j) * (basis₀ j · x)²
  -- LHS term at i equals RHS term at (σ i) by definition of eigenvalues and eigenvectorBasis
  have hterm : ∀ i : Fin m,
      hA.eigenvalues i * (dotProduct (⇑(hA.eigenvectorBasis i)) x) ^ 2 =
      hA.eigenvalues₀ (σ i) *
        (dotProduct (⇑(((isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis
          finrank_euclideanSpace) (σ i))) x) ^ 2 := by
    intro i
    simp [Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvectorBasis, σ]
  simp_rw [hterm]
  exact Equiv.sum_comp σ (fun j =>
    hA.eigenvalues₀ j *
      (dotProduct (⇑(((isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis
        finrank_euclideanSpace) j)) x) ^ 2)

/-! ## Stage 10: Eigenvalue Lower Bound via Rayleigh on Orthogonal Complement

The key theorem: for H = D - λ·u·uᵀ, the second smallest eigenvalue ≥ d_min.

Strategy (Dream 1 insight, 2026-04-12):
  1. H is Hermitian → eigenbasis {vᵢ} with eigenvalues λᵢ (antitone via eigenvalues₀)
  2. Rayleigh decomposition: ⟨x, Hx⟩ = ∑ λᵢ (vᵢ·x)²
  3. For unit x in span{v_{m-2}, v_{m-1}} ∩ u⊥:
     - ⟨x, Hx⟩ ≤ λ_{m-2} (largest eigenvalue in the span)
     - ⟨x, Hx⟩ ≥ d_min (orthogonal to u)
  4. Dimension counting: dim(span) = 2, dim(u⊥) = m-1, so intersection ≠ {0}
  5. Therefore λ_{m-2} = eigenvalues₀(Fin.rev 1) ≥ d_min

We break this into supporting lemmas. -/

open Matrix in
/-- Rayleigh quotient upper bound: if x is a unit vector supported on a subset S of the
    eigenbasis (i.e., vᵢ·x = 0 for i ∉ S), then ⟨x, Hx⟩ ≤ max_{i ∈ S} eigenvalue(i).

    Specialized version: if only eigenvalues indexed by {j | j ≥ k} contribute,
    and eigenvalues are antitone, then ⟨x,Hx⟩ ≤ eigenvalue(k). -/
theorem rayleigh_upper_bound_tail
    {m : ℕ} [NeZero m]
    (ev : Fin m → ℝ) (c_sq : Fin m → ℝ)
    (k : Fin m)
    (h_anti : Antitone ev)
    (h_nn : ∀ i, c_sq i ≥ 0)
    (h_sum : ∑ i : Fin m, c_sq i = 1)
    (h_zero_before : ∀ i, i < k → c_sq i = 0) :
    ∑ i : Fin m, ev i * c_sq i ≤ ev k := by
  exact cf_upper_witness ev c_sq k h_anti h_nn h_sum h_zero_before

open Matrix in
/-- Key bridge lemma: if x is in the span of eigenvectors {v_k, ..., v_{m-1}},
    then the eigenbasis coefficients for indices < k are zero.

    This is a pointwise statement about the eigenbasis decomposition:
    if x = ∑_{j≥k} aⱼ vⱼ, then for i < k, dotProduct vᵢ x = 0
    (by orthonormality of the eigenbasis). -/
theorem eigenbasis_coeff_zero_outside_span
    {m : ℕ} [NeZero m]
    (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsHermitian)
    (x : Fin m → ℝ)
    (k : Fin m)
    -- x is in the span of eigenvectors k, k+1, ..., m-1
    (h_span : ∀ i : Fin m, i < k → dotProduct (⇑(hA.eigenvectorBasis i)) x = 0) :
    ∀ i : Fin m, i < k → (dotProduct (⇑(hA.eigenvectorBasis i)) x) ^ 2 = 0 := by
  intro i hi
  rw [h_span i hi, sq, mul_zero]

open Matrix in
/-- Parseval's identity for eigenbasis: the sum of squared eigenbasis coefficients
    equals the sum of squared coordinates.
    ∑ᵢ (vᵢ · x)² = ∑ⱼ xⱼ²
    where {vᵢ} is the eigenvector ONB. -/
theorem eigenbasis_parseval
    {m : ℕ} [NeZero m]
    (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsHermitian)
    (x : Fin m → ℝ) :
    ∑ i : Fin m, (dotProduct (⇑(hA.eigenvectorBasis i)) x) ^ 2 =
        ∑ j : Fin m, x j ^ 2 := by
  set b := hA.eigenvectorBasis
  set x' : EuclideanSpace ℝ (Fin m) := (WithLp.equiv 2 (Fin m → ℝ)).symm x with hx'
  -- Use Parseval for ONB: ∑ᵢ ⟪bᵢ, x'⟫² = ‖x'‖²
  have h_parseval := b.sum_sq_inner_right x'
  -- ‖x'‖² = ∑ⱼ ‖x' j‖² where x' j = x j (since ofLp (toLp x) = x pointwise)
  have h_norm := EuclideanSpace.norm_sq_eq x'
  -- Bridge 1: ⟪bᵢ, x'⟫ = dotProduct ((b i).ofLp) x = dotProduct (⇑(b i)) x
  have h_inner : ∀ i, @inner ℝ _ _ (b i) x' = dotProduct (⇑(b i)) x := by
    intro i
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have : x'.ofLp = x := rfl
    simp [star_trivial, this, dotProduct_comm]
  -- Bridge 2: ‖x'.ofLp j‖² = (x j)² for real
  have h_coord : ∀ j, ‖x'.ofLp j‖ ^ 2 = x j ^ 2 := by
    intro j
    have : x'.ofLp = x := rfl
    rw [this]
    exact sq_abs (x j) ▸ (Real.norm_eq_abs (x j)).symm ▸ rfl
  -- Combine: ∑ (dotProduct (bᵢ) x)² = ∑ (x j)²
  calc ∑ i : Fin m, (dotProduct (⇑(b i)) x) ^ 2
      = ∑ i : Fin m, (@inner ℝ _ _ (b i) x') ^ 2 := by
        congr 1; ext i; rw [h_inner]
    _ = ‖x'‖ ^ 2 := h_parseval
    _ = ∑ j : Fin m, ‖x'.ofLp j‖ ^ 2 := h_norm
    _ = ∑ j : Fin m, x j ^ 2 := by
        congr 1; ext j; exact h_coord j

open Matrix in
/-- Parseval identity via `eigenvalues₀` / underlying symmetric-eigenvector basis.
    Uses the `isHermitian_iff_isSymmetric`-derived orthonormal basis indexed by
    `Fin (Fintype.card (Fin m))`, which matches `eigenvalues₀`. -/
theorem eigenbasis₀_parseval
    {m : ℕ} [NeZero m]
    (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsHermitian)
    (x : Fin m → ℝ) :
    ∑ i : Fin (Fintype.card (Fin m)),
        (dotProduct (⇑(((isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis
          finrank_euclideanSpace) i)) x) ^ 2 =
        ∑ j : Fin m, x j ^ 2 := by
  -- The eigenvectorBasis in Spectrum is defined as `basis₀.reindex (equivOfCardEq ..)`.
  -- So `eigenvectorBasis i = basis₀ ((equivOfCardEq ..).symm i)`.
  -- The two Parseval sums differ only by a reindexing bijection.
  have h := eigenbasis_parseval A hA x
  set σ := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin m)))).symm
  -- σ : Fin m → Fin (card (Fin m))
  -- eigenvectorBasis i = basis₀.reindex(equiv) i, which at `i : Fin m` equals basis₀ (σ i)
  rw [← h]
  -- LHS: ∑ j : Fin (card (Fin m)), (basis₀ j · x)²
  -- RHS: ∑ i : Fin m, (eigenvectorBasis i · x)²
  -- Since eigenvectorBasis i = basis₀ (σ i), reindex via σ
  symm
  have heq : ∀ i : Fin m,
      (dotProduct (⇑(hA.eigenvectorBasis i)) x) ^ 2 =
      (dotProduct (⇑(((isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis
          finrank_euclideanSpace) (σ i))) x) ^ 2 := by
    intro i
    simp [Matrix.IsHermitian.eigenvectorBasis, σ]
  simp_rw [heq]
  exact Equiv.sum_comp σ (fun j =>
    (dotProduct (⇑(((isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis
      finrank_euclideanSpace) j)) x) ^ 2)

open Matrix in
/-- For a Hermitian matrix A, if x is a unit vector with eigenbasis coefficients
    zero before index k (in the `eigenvalues₀` indexing via `Fin (Fintype.card (Fin m))`),
    then ⟨x, Ax⟩ ≤ eigenvalues₀(k).

    This version uses `eigenvalues₀` (provably antitone) directly, avoiding the
    `equivOfCardEq`-induced indirection in `hA.eigenvalues`.

    Combines `rayleigh_eigenbasis_decomposition_eq_eigenvalues₀` with `cf_upper_witness`. -/
theorem rayleigh_le_eigenvalue₀_of_span
    {m : ℕ} [NeZero m]
    (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsHermitian)
    (x : Fin m → ℝ)
    (k : Fin (Fintype.card (Fin m)))
    (h_unit : ∑ i : Fin m, x i ^ 2 = 1)
    (h_span : ∀ i : Fin (Fintype.card (Fin m)), i < k →
      dotProduct (⇑(((isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis
        finrank_euclideanSpace) i)) x = 0) :
    dotProduct x (A *ᵥ x) ≤ hA.eigenvalues₀ k := by
  rw [rayleigh_eigenbasis_decomposition A hA x,
      rayleigh_eigenbasis_decomposition_eq_eigenvalues₀ A hA x]
  apply cf_upper_witness
  · -- eigenvalues₀ IS antitone (provable from Mathlib)
    exact hA.eigenvalues₀_antitone
  · intro i; exact sq_nonneg _
  · rw [eigenbasis₀_parseval A hA x, h_unit]
  · intro i hi
    rw [h_span i hi, sq, mul_zero]

/-! ## Stage 11: Dual Rayleigh Bound — Lower Bound via Tail Support

The dual of `rayleigh_le_eigenvalue₀_of_span`: if x is a unit vector whose
eigenbasis coefficients are zero AFTER index k, then ⟨x, Ax⟩ ≥ eigenvalues₀(k).

This uses `cf_lower_witness`: when a probability distribution on antitone eigenvalues
has support only on indices 0..k, the weighted sum ≥ eigenvalues₀(k). -/

open Matrix in
/-- For a Hermitian matrix A, if x is a unit vector with eigenbasis₀ coefficients
    zero after index k, then ⟨x, Ax⟩ ≥ eigenvalues₀(k).
    Dual of `rayleigh_le_eigenvalue₀_of_span`. -/
theorem rayleigh_ge_eigenvalue₀_of_head
    {m : ℕ} [NeZero m]
    (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsHermitian)
    (x : Fin m → ℝ)
    (k : Fin (Fintype.card (Fin m)))
    (h_unit : ∑ i : Fin m, x i ^ 2 = 1)
    (h_supp : ∀ i : Fin (Fintype.card (Fin m)), i > k →
      dotProduct (⇑(((isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis
        finrank_euclideanSpace) i)) x = 0) :
    dotProduct x (A *ᵥ x) ≥ hA.eigenvalues₀ k := by
  rw [rayleigh_eigenbasis_decomposition A hA x,
      rayleigh_eigenbasis_decomposition_eq_eigenvalues₀ A hA x]
  apply cf_lower_witness
  · exact hA.eigenvalues₀_antitone
  · intro i; exact sq_nonneg _
  · rw [eigenbasis₀_parseval A hA x, h_unit]
  · intro i hi
    rw [h_supp i hi, sq, mul_zero]

/-! ## Stage 12: Cauchy Interlacing for Rank-1 Perturbation — AXIOM ELIMINATION

Main theorem: for H = D - λ·u·uᵀ with λ > 0 and all dᵢ ≥ d_min,
the second-smallest eigenvalue of H is ≥ d_min.

PROOF BY CONTRADICTION (Dream 1 / Origami insight):
Suppose the second-smallest eigenvalue < d_min.
Then the two smallest eigenvalues are both < d_min.
Their eigenvectors span a 2-dim subspace, which intersects u⊥ (dim m-1)
nontrivially (2 + (m-1) > m since m ≥ 2).
Pick unit x in intersection.
- x ⊥ u → ⟨x,Hx⟩ ≥ d_min  (rank1Perturbation_rayleigh_lower_bound)
- x in span of last 2 eigenvectors → ⟨x,Hx⟩ ≤ eigenvalues₀(m-2) < d_min
Contradiction.

Note: eigenvalues₀ is antitone, so eigenvalues₀(m-2) is the SECOND-smallest. -/

open Matrix in
/-- FORMALIZATION GAP: Given u ∈ ℝᵐ and a Hermitian matrix H with eigenbasis₀,
    there exists a unit vector x that is (1) orthogonal to u and (2) supported
    on the last (m-k) eigenvectors (i.e., eigenbasis�� coefficients zero before k).

    Mathematical proof: span{v_k,...,v_{m-1}} has dimension m-k.
    u⊥ has dimension m-1. By dimension counting, (m-k) + (m-1) > m iff m-k ≥ 2,
    i.e., k ≤ m-2. When k = m-2, m-k = 2, and 2 + (m-1) = m+1 > m. ✓

    Explicit construction: decompose u = ∑ aⱼvⱼ. In span{v_{m-2}, v_{m-1}},
    take x ∝ a_{m-1}·v_{m-2} - a_{m-2}·v_{m-1} (orthogonal to u's projection).
    If a_{m-2} = a_{m-1} = 0, any basis vector in the span works.
    Normalize x to unit length.

    The gap is purely technical: connecting Submodule theory to dotProduct conditions
    on concrete (Fin m → ℝ) vectors via the EuclideanSpace bridge. -/
theorem eigenbasis_orth_vector_exists
    {m : ℕ} [NeZero m] (h_m : m ≥ 2)
    (u : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsHermitian)
    (k : Fin (Fintype.card (Fin m)))
    (hk : k.val = Fintype.card (Fin m) - 2) :
    ∃ x : Fin m → ℝ,
      dotProduct u x = 0 ∧
      ∑ i, x i ^ 2 = 1 ∧
      ∀ i : Fin (Fintype.card (Fin m)), i < k →
        dotProduct (⇑(((isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis
          finrank_euclideanSpace) i)) x = 0 := by
  -- Work in EuclideanSpace ℝ (Fin m) where orthogonal complement API lives
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  set b₀ := (isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis finrank_euclideanSpace
    with hb₀_def
  -- W = span of first k eigenvectors (in EuclideanSpace)
  set W : Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
    Submodule.span ℝ (Set.range (fun (i : Fin k.val) => b₀ ⟨i.val, by omega⟩))
    with hW_def
  -- S = span of u (lifted to EuclideanSpace)
  set u' : EuclideanSpace ℝ (Fin m) := (WithLp.equiv 2 (Fin m → ℝ)).symm u with hu'_def
  set S : Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
    Submodule.span ℝ {u'} with hS_def
  -- We need a nonzero vector in Wᗮ ∩ Sᗮ
  -- finrank W = k.val = m - 2 (first k eigvecs are orthonormal hence linearly independent)
  have hW_dim : Module.finrank ℝ W = k.val := by
    have hort : Orthonormal ℝ (fun (i : Fin k.val) => b₀ ⟨i.val, by omega⟩) := by
      apply b₀.orthonormal.comp
      intro i j hij
      have := congrArg Fin.val hij
      simp at this
      exact Fin.ext this
    have h := finrank_span_eq_card hort.linearIndependent
    simp [Fintype.card_fin] at h
    exact h
  -- finrank Wᗮ = m - k.val = m - (m-2) = 2
  have hWperp_dim : Module.finrank ℝ Wᗮ = m - k.val := by
    have h := Submodule.finrank_add_finrank_orthogonal W
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by
      rw [finrank_euclideanSpace_fin]
    omega
  -- finrank Sᗮ ≥ m - 1
  have hSperp_dim : Module.finrank ℝ Sᗮ ≥ m - 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal S
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by
      rw [finrank_euclideanSpace_fin]
    have hS_le : Module.finrank ℝ S ≤ 1 := by
      calc Module.finrank ℝ S
          = Module.finrank ℝ (Submodule.span ℝ ({u'} : Set (EuclideanSpace ℝ (Fin m)))) := rfl
        _ ≤ ({u'} : Set (EuclideanSpace ℝ (Fin m))).toFinset.card := finrank_span_le_card _
        _ = 1 := by simp
    omega
  -- Wᗮ ∩ Sᗮ is nontrivial: dim Wᗮ + dim Sᗮ ≥ 2 + (m-1) = m+1 > m
  have h_inter_ne_bot : Wᗮ ⊓ Sᗮ ≠ ⊥ := by
    apply submodule_intersection_nontrivial
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by
      rw [finrank_euclideanSpace_fin]
    rw [hWperp_dim]
    rw [hk, hcard]
    omega
  -- Extract a nonzero vector from the intersection
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_inter_ne_bot
  rw [Submodule.mem_inf] at hv_mem
  obtain ⟨hv_Wperp, hv_Sperp⟩ := hv_mem
  -- v is in Wᗮ: ⟪w, v⟫ = 0 for all w ∈ W
  -- v is in Sᗮ: ⟪u', v⟫ = 0
  -- Normalize v to get a unit vector
  set x' := (‖v‖⁻¹ • v) with hx'_def
  have hv_norm_pos : ‖v‖ > 0 := norm_pos_iff.mpr hv_ne
  have hx'_unit : ‖x'‖ = 1 := by
    rw [hx'_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hv_norm_pos)]
  -- x' is in Wᗮ (Wᗮ is a submodule, closed under smul)
  have hx'_Wperp : x' ∈ Wᗮ := Submodule.smul_mem _ _ hv_Wperp
  -- x' is in Sᗮ
  have hx'_Sperp : x' ∈ Sᗮ := Submodule.smul_mem _ _ hv_Sperp
  -- Convert to (Fin m → ℝ) via WithLp.equiv
  set x : Fin m → ℝ := (WithLp.equiv 2 (Fin m → ℝ)) x' with hx_def
  use x
  refine ⟨?_, ?_, ?_⟩
  · -- dotProduct u x = 0
    -- x' ∈ Sᗮ means ⟪s, x'⟫ = 0 for all s ∈ S = span{u'}
    -- In particular ⟪u', x'⟫ = 0
    have h_inner : @inner ℝ _ _ u' x' = 0 := by
      exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_singleton u')) hx'_Sperp
    -- Bridge: ⟪u', x'⟫ = dotProduct x (star u) = dotProduct x u (real case)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h_inner
    simp only [star_trivial] at h_inner
    -- h_inner : dotProduct (ofLp x') (ofLp u') = 0... no wait
    -- inner_eq_star_dotProduct : ⟪u', x'⟫ = ofLp x' ⬝ᵥ star (ofLp u')
    -- For real: star = id, so = dotProduct (ofLp x') (ofLp u')
    -- ofLp x' = x, ofLp u' = u
    -- So h_inner : dotProduct x u = 0
    -- We need dotProduct u x = 0, which is dotProduct_comm
    rw [dotProduct_comm]
    exact h_inner
  · -- ∑ i, x i ^ 2 = 1
    -- ‖x'‖ = 1 means ‖x'‖² = 1, and ‖x'‖² = ∑ i, ‖x' i‖² = ∑ i, (x i)²
    have h_norm_sq := EuclideanSpace.norm_sq_eq x'
    rw [hx'_unit, one_pow] at h_norm_sq
    -- h_norm_sq : 1 = ∑ i, ‖x' i‖²
    -- x' i = x i (since WithLp.equiv is identity on elements)
    -- ‖x' i‖² = (x i)² for reals
    have h_eq : ∑ i, ‖x' i‖ ^ 2 = ∑ i, x i ^ 2 := by
      congr 1; ext i
      have : x' i = x i := rfl
      rw [this, Real.norm_eq_abs, sq_abs]
    linarith
  · -- eigenbasis coefficients zero before k
    intro i hi
    -- b₀ i ∈ W (it's one of the spanning vectors, since i < k)
    have hbi_mem : b₀ i ∈ W := by
      apply Submodule.subset_span
      exact ⟨⟨i.val, by omega⟩, by simp⟩
    -- x' ∈ Wᗮ, so ⟪b₀ i, x'⟫ = 0
    have h_inner : @inner ℝ _ _ (b₀ i) x' = 0 :=
      Submodule.inner_right_of_mem_orthogonal hbi_mem hx'_Wperp
    -- Bridge: ⟪b₀ i, x'⟫ = dotProduct (ofLp x') (ofLp (b₀ i))
    -- For real: inner = dotProduct (via inner_eq_star_dotProduct + star_trivial)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h_inner
    simp only [star_trivial] at h_inner
    -- h_inner : dotProduct (ofLp x') (ofLp (b₀ i)) = 0
    -- ofLp x' = x, ofLp (b₀ i) = ⇑(b₀ i)
    rw [dotProduct_comm] at h_inner
    exact h_inner

-- Now the main interlacing theorem uses any Hermitian matrix with the right bound.

open Matrix in
/-- The second-smallest eigenvalue of H = D - λ·u·uᵀ is ≥ d_min.
    eigenvalues₀ is antitone, and Fintype.card (Fin m) = m, so
    eigenvalues₀(m-2) is the second-smallest eigenvalue.

    Proof by contradiction:
    Assume eigenvalues₀(m-2) < d_min. Then eigenvalues₀(m-1) ≤ eigenvalues₀(m-2) < d_min.
    By rayleigh_le_eigenvalue₀_of_span: any unit x orthogonal to eigenvectors 0..m-3
    (i.e., in span{v_{m-2}, v_{m-1}}) satisfies ⟨x,Hx⟩ ≤ eigenvalues₀(m-2) < d_min.
    But u⊥ (dim m-1) intersects this 2-dim span nontrivially (2+(m-1) > m for m ≥ 2).
    For any unit x in the intersection: ⟨x,Hx⟩ ≥ d_min AND ⟨x,Hx⟩ < d_min. Contradiction.

    The intersection existence is formalized via submodule_intersection_nontrivial. -/
theorem rank1_interlacing_second_eigenvalue
    {m : ℕ} [NeZero m] (h_m : m ≥ 2)
    (d : Fin m → ℝ) (lam : ℝ) (u : Fin m → ℝ)
    (d_min : ℝ)
    (_h_d_min : ∀ i, d i ≥ d_min)
    (h_orth_bound : ∀ (x : Fin m → ℝ),
      dotProduct u x = 0 → (∑ i, x i ^ 2 = 1) →
      dotProduct x (rank1PerturbationMatrix d lam u *ᵥ x) ≥ d_min) :
    let hH := rank1Perturbation_isHermitian d lam u
    hH.eigenvalues₀ ⟨Fintype.card (Fin m) - 2,
      Nat.sub_lt (Fintype.card_pos) (by omega)⟩ ≥ d_min := by
  -- Proof by contradiction
  by_contra h_neg
  push_neg at h_neg
  set hH := rank1Perturbation_isHermitian d lam u
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  set k : Fin (Fintype.card (Fin m)) :=
    ⟨Fintype.card (Fin m) - 2, Nat.sub_lt (Fintype.card_pos) (by omega)⟩
  -- h_neg : hH.eigenvalues₀ k < d_min
  -- KEY STEP: There exists a unit vector x such that:
  -- (1) dotProduct u x = 0 (x ∈ u⊥)
  -- (2) ∑ i, x i ^ 2 = 1 (x is unit)
  -- (3) eigenbasis₀ coefficients zero before k (x ∈ span{v_{m-2}, v_{m-1}})
  -- This follows from dimension counting: span{v_{m-2},v_{m-1}} has dim 2,
  -- u⊥ has dim m-1, and 2 + (m-1) > m when m ≥ 2.
  -- Explicit construction: if u = ∑ aⱼvⱼ, take x = (a_{m-1}·v_{m-2} - a_{m-2}·v_{m-1})/‖·‖.
  -- SORRY: formalizing the vector construction and connecting eigenbasis coordinates
  -- to dotProduct-based orthogonality requires bridging EuclideanSpace ↔ (Fin m → ℝ).
  suffices ∃ x : Fin m → ℝ,
      dotProduct u x = 0 ∧
      ∑ i, x i ^ 2 = 1 ∧
      ∀ i : Fin (Fintype.card (Fin m)), i < k →
        dotProduct (⇑(((isHermitian_iff_isSymmetric.1 hH).eigenvectorBasis
          finrank_euclideanSpace) i)) x = 0 by
    obtain ⟨x, hx_orth, hx_unit, hx_span⟩ := this
    -- Upper bound: ⟨x, Hx⟩ ≤ eigenvalues₀(k) < d_min
    have h_upper := rayleigh_le_eigenvalue₀_of_span
      (rank1PerturbationMatrix d lam u) hH x k hx_unit hx_span
    -- Lower bound: ⟨x, Hx⟩ ≥ d_min
    have h_lower := h_orth_bound x hx_orth hx_unit
    -- Contradiction: d_min ≤ ⟨x, Hx⟩ ≤ eigenvalues₀(k) < d_min
    linarith
  -- REMAINING: construct the witness vector.
  -- This requires bridging from Submodule dimension counting to concrete vectors.
  -- The mathematical content is: in ℝᵐ, if V₁ has dim 2 and V₂ has dim m-1,
  -- then V₁ ∩ V₂ has dim ≥ 1 (since 2 + (m-1) > m when m ≥ 2).
  -- Formalization gap: extracting a concrete (Fin m → ℝ) from the submodule
  -- intersection and verifying it satisfies the dotProduct conditions.
  exact eigenbasis_orth_vector_exists h_m u (rank1PerturbationMatrix d lam u) hH k
    (by simp [k])

/-! ## Generalized Interlacing: eigenvalues₀(k) ≥ d_min for all k ≤ m-2

Generalization of `rank1_interlacing_second_eigenvalue` from k = m-2 to all k ≤ m-2.
Since eigenvalues₀ is antitone, eigenvalues₀(k) for k ≤ m-2 are all ≥ the
second-smallest eigenvalue, so if eigenvalues₀(m-2) ≥ d_min then all earlier
indices are ≥ d_min as well.

This provides the foundation for eliminating `cauchy_interlacing_full`. -/

open Matrix in
/-- Generalized vector existence: for any k ≤ m-2, there exists a unit vector x
    orthogonal to u with eigenbasis₀ coefficients zero before index k.

    This generalizes `eigenbasis_orth_vector_exists` from k = m-2 to k ≤ m-2.
    The tail span has dimension m - k ≥ 2, and (m-k) + (m-1) > m ensures
    the tail span intersects u⊥ nontrivially. -/
theorem eigenbasis_orth_vector_exists_general
    {m : ℕ} [NeZero m] (h_m : m ≥ 2)
    (u : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsHermitian)
    (k : Fin (Fintype.card (Fin m)))
    (hk : k.val ≤ Fintype.card (Fin m) - 2) :
    ∃ x : Fin m → ℝ,
      dotProduct u x = 0 ∧
      ∑ i, x i ^ 2 = 1 ∧
      ∀ i : Fin (Fintype.card (Fin m)), i < k →
        dotProduct (⇑(((isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis
          finrank_euclideanSpace) i)) x = 0 := by
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  set b₀ := (isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis finrank_euclideanSpace
    with hb₀_def
  set W : Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
    Submodule.span ℝ (Set.range (fun (i : Fin k.val) => b₀ ⟨i.val, by omega⟩))
    with hW_def
  set u' : EuclideanSpace ℝ (Fin m) := (WithLp.equiv 2 (Fin m → ℝ)).symm u with hu'_def
  set S : Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
    Submodule.span ℝ {u'} with hS_def
  have hW_dim : Module.finrank ℝ W = k.val := by
    have hort : Orthonormal ℝ (fun (i : Fin k.val) => b₀ ⟨i.val, by omega⟩) := by
      apply b₀.orthonormal.comp
      intro i j hij
      have := congrArg Fin.val hij
      simp at this
      exact Fin.ext this
    have h := finrank_span_eq_card hort.linearIndependent
    simp [Fintype.card_fin] at h
    exact h
  have hWperp_dim : Module.finrank ℝ Wᗮ = m - k.val := by
    have h := Submodule.finrank_add_finrank_orthogonal W
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by
      rw [finrank_euclideanSpace_fin]
    omega
  have hSperp_dim : Module.finrank ℝ Sᗮ ≥ m - 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal S
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by
      rw [finrank_euclideanSpace_fin]
    have hS_le : Module.finrank ℝ S ≤ 1 := by
      calc Module.finrank ℝ S
          = Module.finrank ℝ (Submodule.span ℝ ({u'} : Set (EuclideanSpace ℝ (Fin m)))) := rfl
        _ ≤ ({u'} : Set (EuclideanSpace ℝ (Fin m))).toFinset.card := finrank_span_le_card _
        _ = 1 := by simp
    omega
  have h_inter_ne_bot : Wᗮ ⊓ Sᗮ ≠ ⊥ := by
    apply submodule_intersection_nontrivial
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by
      rw [finrank_euclideanSpace_fin]
    rw [hWperp_dim]
    omega
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_inter_ne_bot
  rw [Submodule.mem_inf] at hv_mem
  obtain ⟨hv_Wperp, hv_Sperp⟩ := hv_mem
  set x' := (‖v‖⁻¹ • v) with hx'_def
  have hv_norm_pos : ‖v‖ > 0 := norm_pos_iff.mpr hv_ne
  have hx'_unit : ‖x'‖ = 1 := by
    rw [hx'_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hv_norm_pos)]
  have hx'_Wperp : x' ∈ Wᗮ := Submodule.smul_mem _ _ hv_Wperp
  have hx'_Sperp : x' ∈ Sᗮ := Submodule.smul_mem _ _ hv_Sperp
  set x : Fin m → ℝ := (WithLp.equiv 2 (Fin m → ℝ)) x' with hx_def
  use x
  refine ⟨?_, ?_, ?_⟩
  · have h_inner : @inner ℝ _ _ u' x' = 0 := by
      exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_singleton u')) hx'_Sperp
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h_inner
    simp only [star_trivial] at h_inner
    rw [dotProduct_comm]
    exact h_inner
  · have h_norm_sq := EuclideanSpace.norm_sq_eq x'
    rw [hx'_unit, one_pow] at h_norm_sq
    have h_eq : ∑ i, ‖x' i‖ ^ 2 = ∑ i, x i ^ 2 := by
      congr 1; ext i
      have : x' i = x i := rfl
      rw [this, Real.norm_eq_abs, sq_abs]
    linarith
  · intro i hi
    have hbi_mem : b₀ i ∈ W := by
      apply Submodule.subset_span
      exact ⟨⟨i.val, by omega⟩, by simp⟩
    have h_inner : @inner ℝ _ _ (b₀ i) x' = 0 :=
      Submodule.inner_right_of_mem_orthogonal hbi_mem hx'_Wperp
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h_inner
    simp only [star_trivial] at h_inner
    rw [dotProduct_comm] at h_inner
    exact h_inner

open Matrix in
/-- Generalized interlacing: for H = D - λ·u·uᵀ with all dᵢ ≥ d_min,
    eigenvalues₀(k) ≥ d_min for all k ≤ m-2.

    This generalizes `rank1_interlacing_second_eigenvalue` from k = m-2 to all k ≤ m-2.
    Proof by contradiction using `eigenbasis_orth_vector_exists_general`:
    if eigenvalues₀(k) < d_min, construct x ∈ u⊥ with ⟨x,Hx⟩ ≤ eigenvalues₀(k) < d_min,
    but also ⟨x,Hx⟩ ≥ d_min — contradiction. -/
theorem rank1_interlacing_general
    {m : ℕ} [NeZero m] (h_m : m ≥ 2)
    (d : Fin m → ℝ) (lam : ℝ) (u : Fin m → ℝ)
    (d_min : ℝ)
    (_h_d_min : ∀ i, d i ≥ d_min)
    (h_orth_bound : ∀ (x : Fin m → ℝ),
      dotProduct u x = 0 → (∑ i, x i ^ 2 = 1) →
      dotProduct x (rank1PerturbationMatrix d lam u *ᵥ x) ≥ d_min)
    (k : Fin (Fintype.card (Fin m)))
    (hk : k.val ≤ Fintype.card (Fin m) - 2) :
    let hH := rank1Perturbation_isHermitian d lam u
    hH.eigenvalues₀ k ≥ d_min := by
  by_contra h_neg
  push_neg at h_neg
  set hH := rank1Perturbation_isHermitian d lam u
  suffices ∃ x : Fin m → ℝ,
      dotProduct u x = 0 ∧
      ∑ i, x i ^ 2 = 1 ∧
      ∀ i : Fin (Fintype.card (Fin m)), i < k →
        dotProduct (⇑(((isHermitian_iff_isSymmetric.1 hH).eigenvectorBasis
          finrank_euclideanSpace) i)) x = 0 by
    obtain ⟨x, hx_orth, hx_unit, hx_span⟩ := this
    have h_upper := rayleigh_le_eigenvalue₀_of_span
      (rank1PerturbationMatrix d lam u) hH x k hx_unit hx_span
    have h_lower := h_orth_bound x hx_orth hx_unit
    linarith
  exact eigenbasis_orth_vector_exists_general h_m u (rank1PerturbationMatrix d lam u) hH k hk

-- NOTE: The full Cauchy interlacing E_k ≥ d_sorted(k-1) for ALL k requires a
-- triple intersection argument (H-eigenvector span ∩ u⊥ ∩ standard basis span)
-- whose dimension count yields 0, making it non-trivial to formalize purely via
-- dimension counting. This would require either the secular equation approach
-- or a more sophisticated Courant-Fischer argument.
--
-- However, rank1_interlacing_general above proves eigenvalues₀(k) ≥ d_min for
-- ALL k ≤ m-2, which is sufficient for the Goldbach proof pipeline (which only
-- needs E₁ ≥ d_min via the k=1 case).

end CourantFischer
