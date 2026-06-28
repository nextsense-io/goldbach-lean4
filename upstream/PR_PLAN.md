# Mathlib Upstream Plan — Courant-Fischer / Rank-1 Interlacing

*Cipher, 2026-06-10. Track 1a of GOLDBACH-STRATEGY-2026-06.md.*

Source: `GoldbachProof/CourantFischer.lean` (26 theorems + 1 def, 0 axioms, 0 sorry,
Lean 4.28 + Mathlib master). Verified Jun 2026: eigenvalue interlacing and the
Courant-Fischer minimax characterization are **absent from Mathlib**
(`Mathlib/Analysis/Matrix/Spectrum.lean` has `eigenvalues₀`/`eigenvectorBasis` and
antitonicity, nothing minimax).

**Key audit finding: NO theorem in CourantFischer.lean depends on any Goldbach-specific
definition.** The whole file is general linear algebra over `Matrix (Fin m) (Fin m) ℝ`.
The only refactoring needed for upstreaming is (a) `Fin m` → arbitrary `[Fintype n]`
index, (b) Mathlib naming/namespacing, (c) replacing the bespoke
`rank1PerturbationMatrix` def with hypothesis-style statements (see PR #3).

---

## PR #1 — Rayleigh quotient eigenbasis decomposition  ✅ DRAFTED & BUILDS

File: `upstream/Mathlib_PR1_RayleighDecomposition.lean` (~190 lines).
Builds clean against Mathlib master via `lake build UpstreamPR1` (0 errors, 0 warnings).
Target Mathlib location: new file `Mathlib/Analysis/Matrix/RayleighDecomposition.lean`
(or appended to `Mathlib/Analysis/Matrix/Spectrum.lean` — ask on Zulip).

Namespace `Matrix.IsHermitian`, field `ℝ`, index generalized `Fin m` → `{n} [Fintype n]
[DecidableEq n]` (the `NeZero` assumption of the originals was dropped; only the two
average corollaries need `[Nonempty n]`).

| Upstream name (proposed) | Origin theorem | Statement |
|---|---|---|
| `dotProduct_mulVec_eq_sum_eigenvalues_mul_sq` | `rayleigh_eigenbasis_decomposition` | `x ⬝ᵥ A *ᵥ x = ∑ i, λᵢ * (vᵢ ⬝ᵥ x)²` |
| `sum_sq_dotProduct_eigenvectorBasis` | `eigenbasis_parseval` | `∑ i, (vᵢ ⬝ᵥ x)² = ∑ j, x j²` (Parseval) |
| `finrank_span_range_eigenvectorBasis` | `eigenvector_span_dim` | span of any `k` eigenvectors (via `ι ↪ n`) has finrank `card ι` |
| `exists_eigenvalues_ge_sum_div_card` | `exists_eigenvalue_ge_avg_total` | some `λᵢ ≥ (∑∑ A p q)/card n` |
| `exists_eigenvalues_ge_trace_div_card` | `exists_eigenvalue_ge_avg_trace` | some `λᵢ ≥ trace/card n` |

Pre-submission TODO (mechanical):
- Convert header to the new Mathlib module system (`module` + `public import`) when
  placing inside the Mathlib tree (the draft uses plain `import` so it can be compiled
  from a downstream package).
- Consider `⟪·, ·⟫_ℝ` notation instead of `@inner ℝ _ _` in two proof-internal `have`s.
- Reviewers may ask for the `RCLike 𝕜` version (`‖⟪vᵢ, x⟫‖²` instead of `(vᵢ ⬝ᵥ x)²`);
  flagged in the module docstring as future work. Keep ℝ unless they insist.

## PR #2 — `eigenvalues₀` Rayleigh bounds (one-sided Courant-Fischer)

~200 lines, depends on PR #1. Target: same file or
`Mathlib/Analysis/Matrix/CourantFischer.lean`.

| Origin theorem | Content |
|---|---|
| `cf_lower_witness` / `cf_upper_witness` | weighted sums against an antitone sequence with head/tail support (pure `Finset` algebra; possibly `Finset.*` namespace, possibly partially redundant — search before PR) |
| `rayleigh_eigenbasis_decomposition_eq_eigenvalues₀` | reindex decomposition from `eigenvalues` to sorted `eigenvalues₀` via `Fintype.equivOfCardEq` |
| `eigenbasis₀_parseval` | Parseval in the `eigenvalues₀` indexing |
| `eigenvalues₀_rev_monotone` | `eigenvalues₀ ∘ Fin.rev` is monotone (one-liner) |
| `rayleigh_le_eigenvalue₀_of_span` | unit `x` with eigenbasis coeffs 0 before `k` ⇒ `⟨x,Ax⟩ ≤ eigenvalues₀ k` |
| `rayleigh_ge_eigenvalue₀_of_head` | dual: coeffs 0 after `k` ⇒ `⟨x,Ax⟩ ≥ eigenvalues₀ k` |

These two bounds are exactly the "easy directions" of Courant-Fischer and are the
reusable core for any interlacing argument.

## PR #3 — Orthogonal-complement witness + rank-1 interlacing

~250-300 lines, depends on PR #2. Refactor before upstreaming:

- **Drop `submodule_intersection_nontrivial`** — Mathlib already has the contrapositive:
  `finrank_add_finrank_le_of_disjoint` (`Mathlib/LinearAlgebra/FiniteDimensional/
  Lemmas.lean`). Rewrite the witness proofs to use it (or PR the `S ⊓ T ≠ ⊥` form as a
  2-line corollary there).
- **Drop the `rank1PerturbationMatrix` def.** State the main theorem for an *arbitrary*
  Hermitian `A` with a Rayleigh hypothesis on `u⊥`, then derive the
  `diagonal d - λ • vecMulVec u u` case as a corollary. Mathlib will not want a named
  def for a 5-symbol expression.

| Origin theorem | Upstream fate |
|---|---|
| `eigenbasis_orth_vector_exists_general` | main witness lemma: unit `x ⊥ u` with eigenbasis coeffs 0 before `k`, any `k ≤ card n − 2` |
| `rank1_interlacing_general` | restated: if `⟨x,Ax⟩ ≥ c` for all unit `x ⊥ u`, then `eigenvalues₀ k ≥ c` for `k ≤ card n − 2` |
| `vecMulVec_self_isHermitian` | generalize to `(vecMulVec u (star u)).IsHermitian` over `StarMul`; tiny addition to `Mathlib/LinearAlgebra/Matrix/Hermitian.lean` |
| `rank1Perturbation_isHermitian`, `rank1Perturbation_rayleigh_orthogonal`, `rank1Perturbation_rayleigh_lower_bound` | folded into the rank-1 corollary |
| `eigenbasis_orth_vector_exists`, `rank1_interlacing_second_eigenvalue` | NOT upstreamed (strictly subsumed by the `_general` versions) |

## PR #4 (future, not yet formalized) — full Courant-Fischer & Cauchy interlacing

Roadmap items, contingent on PR #1-3 review feedback:
- Full minimax: `eigenvalues₀ k = ⨆_{dim V = k+1} ⨅_{x ∈ V, ‖x‖=1} ⟨x,Ax⟩` (both
  directions; the ≤/≥ halves come from PR #2 machinery).
- Classical Cauchy interlacing for principal submatrices (`A.submatrix` is already
  Hermitian-stable in Mathlib). Requires the triple-intersection dimension argument
  noted at the bottom of CourantFischer.lean — genuinely new work.

## Not upstreamed (trivial / redundant — stay local)

- `intersection_nontrivial_of_dims` (trivial corollary)
- `rayleigh_diagonal_ge_min`, `rank1_orthogonal_bound`, `rayleigh_upper_bound_tail`
  (special cases / aliases of `cf_*_witness`)
- `eigenbasis_coeff_zero_outside_span` (one-line)
- `isHermitian_smul_real` (check `IsHermitian` + `star c = c` smul lemma in current
  Mathlib; add only if genuinely missing)

## Process

1. Post `ZULIP_DRAFT.md` to `#mathlib4` (naming + placement guidance) — **awaiting JB
   go-ahead before posting**.
2. Incorporate feedback, fork mathlib4, open PR #1 (needs Mathlib contributor access /
   `awaiting-author` workflow; first-time contributors ask on Zulip for write access to
   push a branch).
3. PRs #2, #3 sequentially after #1 merges (each cites the Goldbach formalization repo
   `github.com/nextsense-io/goldbach-lean4` as origin).
