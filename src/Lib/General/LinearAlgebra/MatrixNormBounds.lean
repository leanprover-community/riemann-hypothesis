module

import TauCeti.Analysis.Normed.Module.Bases.Auerbach
public import Lib.GLn.SchurModule.GramMatrix
import Lib.GLn.SchurModule.WeylKernel

/-!
# Auerbach's lemma, ultrametric matrix bounds and Gram norms

This file collects norm estimates for linear maps and matrices.

## Main definitions and results

* `New.exists_auerbach`: linear forms indexed by a compact space that vanish together only at `0`,
  with images in a normed field depending continuously on the index, contain the coordinate forms
  of a basis on whose vectors all forms of the family take values of image norm at most `1`.
* `New.norm_mulVec_le_of_nonneg`, `New.norm_mulVec_le`: over an ultrametric seminormed ring, a
  matrix whose entries have norm at most `c ≥ 0` multiplies the sup norm of a vector by at most `c`,
  whatever its size.
* `New.sqrt_weylNormSq_le_of_dual`: a bound on the Gram norm of Weyl modules by duality.
* `New.sqrt_weylNormSq_sum_le`: the triangle inequality for the Gram norm of Weyl modules.

## Relation to the literature

Known result: Auerbach's lemma, here for a compact family of linear forms.
-/

@[expose] public section

/-! ## Auerbach's lemma for a compact family of linear forms -/

section Auerbach

open Module Basis

/-- Auerbach's lemma. Let `ℓ a` (`a` in a compact topological space `A`) be linear forms on a
finite-dimensional `K`-space `U` whose only common zero is `0`. Let `φ : K →+* L` map to a normed
field, and let `a ↦ φ (ℓ a v)` be continuous for every `v`. Then there are indices `S k` and a
basis `z` such that the coordinates of `z` are the forms `ℓ (S k)` and `‖φ (ℓ a (z k))‖ ≤ 1` for
all `a`, `k`. The result depends on the basis `b` only through its index type `ι`. The topology
`topA` of `A` is implicit: it is found from the continuity hypothesis. -/
lemma New.exists_auerbach {K U A L ι : Type*} [Field K] [AddCommGroup U] [Module K U]
    [Module.Finite K U] {topA : TopologicalSpace A} [CompactSpace A] [NormedField L]
    (b : Basis ι K U) (ℓ : A → Dual K U) (h_sep : ∀ v : U, (∀ a : A, ℓ a v = 0) → v = 0)
    (φ : K →+* L) (hℓ_cont : ∀ v : U, Continuous fun a : A ↦ φ (ℓ a v)) :
    ∃ (S : ι → A) (z : Basis ι K U),
      (∀ k : ι, z.coord k = ℓ (S k)) ∧ ∀ (a : A) (k : ι), ‖φ (ℓ a (z k))‖ ≤ 1 := by
  classical
  have : Finite ι := Module.Finite.finite_basis b
  let := Fintype.ofFinite ι
  obtain ⟨a, z₀, h_dual, h_bound⟩ := φ.exists_auerbachBasis ℓ hℓ_cont h_sep
  let e : Fin (Module.finrank K U) ≃ ι :=
    (Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm).symm
  refine ⟨a ∘ e.symm, z₀.reindex e, fun k ↦ ?_, fun x k ↦ ?_⟩
  · refine (z₀.reindex e).ext fun j ↦ ?_
    simp [h_dual, Finsupp.single_apply, eq_comm]
  · simpa using h_bound x (e.symm k)

end Auerbach

/-! ## Sup norm bound for matrix–vector products over ultrametric rings -/

/-- Over an ultrametric seminormed ring, a matrix whose entries have norm at most `c ≥ 0` multiplies
the sup norm of a vector by at most `c`, whatever the size of the matrix. -/
lemma New.norm_mulVec_le_of_nonneg {K l m : Type*} [SeminormedRing K] [IsUltrametricDist K]
    [Fintype l] [Fintype m] {M : Matrix l m K} {c : ℝ} (hc : 0 ≤ c)
    (hM : ∀ (i : l) (j : m), ‖M i j‖ ≤ c) (x : m → K) :
    ‖M.mulVec x‖ ≤ c * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
  -- In an ultrametric ring a sum is bounded by its largest term.
  rw [M.mulVec_apply_eq_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ ↦ ?_
  exact (norm_mul_le _ _).trans (mul_le_mul (hM i j) (norm_le_pi_norm x j) (norm_nonneg _) hc)

/-- If all entries of a matrix `M` over an ultrametric seminormed ring have norm at most `c`, then
`‖M.mulVec x‖ ≤ c * ‖x‖` in the sup norm. This is the form of `New.norm_mulVec_le_of_nonneg` for
explicit constants: the hypothesis `0 ≤ c` comes last and is proved by `simp` when omitted. -/
lemma New.norm_mulVec_le {K l m : Type*} [SeminormedRing K] [IsUltrametricDist K] [Fintype l]
    [Fintype m] {M : Matrix l m K} {c : ℝ} (hM : ∀ (i : l) (j : m), ‖M i j‖ ≤ c) (x : m → K)
    (hc : 0 ≤ c := by simp) :
    ‖M.mulVec x‖ ≤ c * ‖x‖ :=
  New.norm_mulVec_le_of_nonneg hc hM x

/-!
## Duality for Gram norms

For an automorphism `σ` of `ℂ`, we bound the values at `σ ∘ v` of the Gram norm
`ξ ↦ √(weylNormSq ξ)`, where `New.weylNormSq ξ` is the real part of `ξ* G ξ` for the integer Gram
matrix `G`. The coordinates are indexed by `New.WeylIndex n κ`: families, one for each `τ : T`, of
basis tableaux with entries indexed by `n` and column multiplicities `κ τ`.
-/

namespace New

open Matrix «GL»

variable {T n : Type} [Fintype T] [DecidableEq T] [Fintype n] [DecidableEq n] {κ : T → ℕ → ℕ}
  (σ : ℂ ≃+* ℂ)

/-- Duality for the Gram norm `ξ ↦ √(weylNormSq ξ)` after an automorphism `σ` of `ℂ`, on vectors
indexed by `WeylIndex n κ` (families of basis tableaux): here `weylNormSq ξ` is `Re (ξ* G ξ)` for
the positive definite integer Gram matrix `G = weylGram n κ` of the Weyl-module basis given by these
tableaux (entries in `n`, column multiplicities `κ τ` for each `τ : T`). If `‖σ (c ⬝ᵥ v)‖ ≤ C` for
every vector `c` with `‖σ (c ⬝ᵥ w)‖ ≤ √(weylNormSq (σ ∘ w))` for all `w`, then the Gram norm of
`σ ∘ v` is at most `C`. -/
lemma sqrt_weylNormSq_le_of_dual {v : WeylIndex n κ → ℂ} {C : ℝ}
    (h_dual : ∀ c : WeylIndex n κ → ℂ,
      (∀ w : WeylIndex n κ → ℂ, ‖σ (c ⬝ᵥ w)‖ ≤ √(weylNormSq (σ ∘ w))) → ‖σ (c ⬝ᵥ v)‖ ≤ C) :
    √(weylNormSq (σ ∘ v)) ≤ C := by
  -- Test with the functional `w ↦ ⟨σ v, σ w⟩ / N` pulled back through `σ`, where `⟨·, ·⟩` is the
  -- Gram pairing and `N = √⟨σ v, σ v⟩`.
  set N : ℝ := √(weylNormSq (σ ∘ v)) with hN
  let c : WeylIndex n κ → ℂ := σ.symm ∘ ((N : ℂ)⁻¹ • star (σ ∘ v) ᵥ* weylGramOver)
  have hc (w : WeylIndex n κ → ℂ) :
      ‖σ (c ⬝ᵥ w)‖ = ‖star (σ ∘ v) ⬝ᵥ weylGramOver *ᵥ (σ ∘ w)‖ / N := by
    have h_pull (x y : WeylIndex n κ → ℂ) : σ (σ.symm ∘ x ⬝ᵥ y) = x ⬝ᵥ σ ∘ y := by simp [dotProduct]
    simp [c, h_pull, ← dotProduct_mulVec, inv_mul_eq_div, hN, abs_of_nonneg]
  -- Cauchy–Schwarz for the positive definite Gram matrix: `c` has norm at most one.
  have h_norm (w : WeylIndex n κ → ℂ) : ‖σ (c ⬝ᵥ w)‖ ≤ √(weylNormSq (σ ∘ w)) := by
    rw [hc w]
    refine div_le_of_le_mul₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) ?_
    have h_sq : ‖star (σ ∘ v) ⬝ᵥ weylGramOver *ᵥ (σ ∘ w)‖ ^ 2 ≤
        weylNormSq (σ ∘ w) * weylNormSq (σ ∘ v) :=
      posDef_cauchy_schwarz weylGramOver_posDef (σ ∘ v) (σ ∘ w)
    simpa [weylNormSq_nonneg, hN] using Real.abs_le_sqrt h_sq
  -- At `w = v` the value is `N ^ 2 / N = N`.
  refine le_of_eq_of_le ?_ (h_dual c h_norm)
  simp [hc, ← coe_weylNormSq, abs_of_nonneg (weylNormSq_nonneg _), hN]

/-- Triangle inequality for the Gram norm `ξ ↦ √(weylNormSq ξ)` on vectors indexed by
`WeylIndex n κ` (families of basis tableaux, entries in `n`, column multiplicities `κ τ`), where
`weylNormSq ξ = Re (ξ* G ξ)` for the positive definite integer Gram matrix `G = weylGram n κ`, after
an automorphism `σ` of `ℂ`: the Gram norm of `σ` applied to a finite sum of vectors is at most the
sum of their Gram norms after `σ`. -/
lemma sqrt_weylNormSq_sum_le {α : Type*} (s : Finset α) (f : α → WeylIndex n κ → ℂ) :
    √(weylNormSq (σ ∘ ∑ a ∈ s, f a)) ≤ ∑ a ∈ s, √(weylNormSq (σ ∘ f a)) := by
  -- By duality it suffices to bound a functional `c` of norm at most one on the sum.
  refine sqrt_weylNormSq_le_of_dual σ fun c hc ↦ ?_
  calc ‖σ (c ⬝ᵥ ∑ a ∈ s, f a)‖ = ‖∑ a ∈ s, σ (c ⬝ᵥ f a)‖ := by rw [dotProduct_sum, map_sum]
    _ ≤ ∑ a ∈ s, √(weylNormSq (σ ∘ f a)) := norm_sum_le_of_le s fun a _ ↦ hc (f a)

end New
