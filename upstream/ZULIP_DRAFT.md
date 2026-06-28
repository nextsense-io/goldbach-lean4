# Zulip draft — #mathlib4 (or #Is there code for X? for the existence check)

**Topic: Courant-Fischer / eigenvalue interlacing for Hermitian matrices**

---

Hi all! As part of a Lean 4 formalization project on the Goldbach conjecture
(machine-checked reduction of Goldbach to an explicit analytic hypothesis,
code at https://github.com/nextsense-io/goldbach-lean4), we built a ~1100-line,
axiom-free, sorry-free development of Rayleigh-quotient / eigenvalue-interlacing
material for real symmetric matrices on top of `Matrix.IsHermitian.eigenvalues₀` /
`eigenvectorBasis`. As far as we can tell, the Courant-Fischer minimax
characterization and eigenvalue interlacing are not in Mathlib (only
`eigenvalues₀_antitone` and the Rayleigh material in
`Analysis/InnerProductSpace/Rayleigh.lean` exist). We'd like to upstream it in
small pieces and would appreciate naming/placement guidance before opening PR #1.

**PR #1 (drafted, compiles against current master, ~190 lines), namespace
`Matrix.IsHermitian`, over `ℝ` with arbitrary `[Fintype n] [DecidableEq n]` index:**

- `dotProduct_mulVec_eq_sum_eigenvalues_mul_sq`:
  `x ⬝ᵥ A *ᵥ x = ∑ i, hA.eigenvalues i * (⇑(hA.eigenvectorBasis i) ⬝ᵥ x) ^ 2`
  (spectral decomposition of the quadratic form, stated in `dotProduct` language)
- `sum_sq_dotProduct_eigenvectorBasis`: Parseval for the eigenbasis coefficients,
  `∑ i, (vᵢ ⬝ᵥ x) ^ 2 = ∑ j, x j ^ 2`
- `finrank_span_range_eigenvectorBasis`: any subfamily of `k` eigenvectors (as
  functions `n → ℝ`) spans a `k`-dimensional subspace
- corollaries `exists_eigenvalues_ge_sum_div_card` (some eigenvalue ≥ average entry)
  and `exists_eigenvalues_ge_trace_div_card` (some eigenvalue ≥ `trace / card n`)

**Planned follow-ups (all already proved in our repo, will be PR'd in order):**

- PR #2: the "easy directions" of Courant-Fischer via `eigenvalues₀`: a unit vector
  whose eigenbasis coefficients vanish before (resp. after) index `k` has Rayleigh
  quotient `≤` (resp. `≥`) `eigenvalues₀ k`.
- PR #3: existence of a unit vector orthogonal to a given `u` and to the first `k`
  eigenvectors (dimension counting via `finrank_add_finrank_le_of_disjoint`), and the
  resulting rank-1 interlacing: if `⟨x, Ax⟩ ≥ c` for every unit `x ⊥ u`, then
  `eigenvalues₀ k ≥ c` for all `k ≤ card n - 2`; corollary for
  `diagonal d - λ • vecMulVec u u`.
- Later (new work): full Courant-Fischer minimax equality and classical Cauchy
  interlacing for principal submatrices.

**Questions:**

1. Placement: new file `Mathlib/Analysis/Matrix/RayleighDecomposition.lean`, or
   should PR #1 just extend `Mathlib/Analysis/Matrix/Spectrum.lean`?
2. Naming: is `dotProduct_mulVec_eq_sum_eigenvalues_mul_sq` acceptable, or is there
   a preferred idiom for `x ⬝ᵥ A *ᵥ x` statements?
3. Generality: we state everything over `ℝ` with `(vᵢ ⬝ᵥ x)^2`. Would you rather
   have `RCLike 𝕜` with `‖⟪vᵢ, x⟫‖^2` from the start, or is ℝ-first acceptable
   with the generalization as a follow-up?
4. Is there any in-flight work on interlacing/min-max we should coordinate with?

Thanks! Happy to adjust everything to reviewer taste — the goal is for this to be
usable infrastructure, not project-specific code.

---

*Status: DRAFT ONLY — not posted. Post after JB approval. Posting account: TBD
(needs a leanprover.zulipchat.com account under a real name per Zulip policy).*
