module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Lib.GLn.SchurModule.GramMatrix

/-!
# Branching from GL(n+1) to GL(n) × GL(1): the branching vector and the norm bound

This file treats the branching from `GL(n + 1)` to `GL(n) × GL(1)` for the representations of
`∏ τ, GL (N τ)`. The rows `N τ` are the rows `n τ` together with one new row, given by `ι τ`. A
weight `κ` is given by the numbers `κ τ h` of columns of height `h` at the place `τ`. This file
defines the branching vector and shows that a hook number times a product of two kernels is the
polynomial of an integral vector, through the multiplication matrix `New.GL.comulMatrix`. It
proves the norm bound for an equivariant matrix from the fact that the matrix times its adjoint
commutes with the smaller group, so is a scalar.

## Main definitions and results

* `New.GL.branchVector`: the product of the leading minors to the powers `γ`, with the new row
  first, so that every column of positive height contains it, and to the powers `κ`, with the new
  row last, so that no column contains it.
* `New.GL.weylNormSq_mulVec_le_of_equivariant`: the norm bound for an equivariant matrix whose
  transpose sends the extremal vector to a multiple of the branching vector.

Notions from other files:
* `New.MatrixPoly`: Polynomials over `R` in an array of variables `X (a, i)`, with rows `a : m` and
  columns `i : ℕ`.
* `New.rankAt`: The number of elements of the finite row type n_τ at the place τ;
  `New.GL.rowEquivFin n τ : n τ ≃ Fin (rankAt n τ)` is the fixed numbering of these rows, and a
  row's position is its number.
* `New.permArray`: For maps e_τ from rows to natural numbers, the array over R whose entry at row
  (τ,a), column i is 1 if e_τ(a)=i and 0 otherwise.
* `New.toPoly`: The linear map from coordinate vectors ξ to polynomials, ξ ↦ Σ_i (Gξ)_i b_i, with G
  the Gram matrix `New.weylGram` (`New.weylGramOver` is its image over another ring) and b_i the
  basis `New.nablaBasis` of products of minors; `New.GL.nablaCombination` is ξ ↦ Σ_i ξ_i b_i.
* `New.weylEval`: For an array y, the evaluation vector `ev_y` with entries b_i(y); its polynomial
  under `New.toPoly` is `New.weylKernel n κ y`.

## Relation to the literature

Known; see `Lib.GLn.Branching.IntegralMap` for sources.
-/

@[expose] public section

noncomputable section

/-!
## The branching vector and integrality of products of minors

A weight `κ` is given by the numbers `κ τ h` of columns of height `h` at the place `τ`.
`New.weylKernel n κ (permArray e)` is the product over `h < rankAt n τ` of the minors on the first
`h` rows in the order `e` and the first `h` columns, to the powers `κ τ h`; `New.rowSubst z f` is
`y ↦ f (z y)`; `New.toPoly n κ` sends a coordinate vector `ξ` to `∑ i, (G ξ) i • b i`, with `G` the
Gram matrix and `b` the basis of minor products.
-/

section BranchingVector

open Finset Matrix

namespace New.GL

variable {Φ : Type} (R : Type) [CommRing R] [Fintype Φ] {n N : Φ → Type}
  [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, Fintype (N τ)]
  (ι : ∀ τ : Φ, n τ ⊕ Unit ≃ N τ) {κ₀ γ κ' : Φ → ℕ → ℕ}

open scoped Classical in
/-- The numbering of the rows `N τ` by `0, …, rankAt N τ - 1` that gives the added row the number
`i τ` and keeps the rows of `n τ` in their fixed order. -/
def newRowOrder (i : ∀ τ : Φ, Fin (rankAt n τ + 1)) (τ : Φ) : N τ ≃ Fin (rankAt N τ) :=
  -- Insert the new row at position `i τ` into the fixed numbering `rowEquivFin n τ`, then invert.
  finCongr (rankAt_eq_succ ι τ)
    |>.trans (finSuccEquiv' (i τ))
    |>.trans (rowEquivFin n τ).symm.optionCongr
    |>.trans (Equiv.optionEquivSumPUnit (n τ))
    |>.trans (ι τ)
    |>.symm

/-- The product over `τ` and `h < rankAt N τ` of the leading `h × h` minors to the power `γ τ h`
with the added row first, and to the power `κ τ h` with it last. -/
def branchVector (γ κ : Φ → ℕ → ℕ) : MatrixPoly ((τ : Φ) × N τ) R :=
  weylKernel N γ (permArray fun (τ : Φ) (i : N τ) ↦ (newRowOrder ι 0 τ i : ℕ)) *
    weylKernel (R := R) N κ (permArray fun (τ : Φ) (i : N τ) ↦ (newRowOrder ι ⊤ τ i : ℕ))

/-- Multiplying the new row by `s τ` (substituting the matrix `blockScalar ι 1 s`, that is
`diag(1, s τ)` at each `τ`) multiplies `branchVector R ι γ κ'` by the product over `τ` of `s τ` to
the power `diagramWeight (rankAt N) γ (τ, 0)`, the number of columns of `γ` of height
`1, …, rankAt n τ`. -/
lemma rowSubst_branchVector (s : Φ → R) :
    rowSubst (blockScalar ι 1 s) (branchVector R ι γ κ') =
      (∏ τ : Φ, s τ ^ diagramWeight (rankAt N) γ (τ, 0)) • branchVector R ι γ κ' := by
  classical
  -- `blockScalar ι 1 s` is diagonal, so it multiplies each kernel by a power of `s`. The new row is
  -- first in the order for `γ`, so it lies in all columns of positive height; it is last in the
  -- order for `κ'`, so it lies in none.
  have h_triangular (e : ∀ τ : Φ, N τ ≃ Fin (rankAt N τ)) (τ : Φ) :
      (blockScalar (R := R) ι 1 s τ)ᵀ.BlockTriangular (e τ) := by
    have h_diagonal : blockScalar (R := R) ι 1 s τ =
        diagonal (Sum.elim (fun _ : n τ ↦ (1 : R)) (fun _ : Unit ↦ s τ) ∘ (ι τ).symm) := by
      rw [blockScalar, Pi.one_apply, ← diagonal_one, fromBlocks_diagonal, reindex_apply,
        submatrix_diagonal_equiv]
    rw [h_diagonal, diagonal_transpose]
    exact blockTriangular_diagonal _
  rw [branchVector, map_mul, rowSubst_weylKernel_permArray _ _ (h_triangular _),
    rowSubst_weylKernel_permArray _ _ (h_triangular _)]
  simp [newRowOrder, blockScalar, rankAt_eq_succ ι, reindex_equiv (ι _), diagramWeight_apply,
    Nat.Ioo_eq_range']

/-! ### The product of the two kernels through the multiplication matrix -/

open scoped Kronecker

variable {R} {κ β α : Φ → ℕ → ℕ}

omit [∀ τ, DecidableEq (n τ)] in
/-- If `β τ h ≤ γ τ h` for every height `h < rankAt n τ`, the kernel of `β` divides the kernel of
`γ` at every array `y`: both are products of the same minors, to the powers `β τ h` and `γ τ h`. -/
lemma weylKernel_dvd_weylKernel (y : ((τ : Φ) × n τ) × ℕ → R)
    (h_le : ∀ τ : Φ, ∀ h < rankAt n τ, β τ h ≤ γ τ h) :
    weylKernel n β y ∣ weylKernel n γ y := by
  simp only [weylKernel, rowSubst_highestPoly]
  exact prod_dvd_prod_of_dvd _ _ fun τ _ ↦ prod_dvd_prod_of_dvd _ _ fun h h_mem ↦
    pow_dvd_pow _ (h_le τ h (mem_range.mp h_mem))

/-- Let the polynomial of the integral vector `ζ` be a multiple of the product of the kernel of `γ`
at the row order `e` and the kernel of `κ'` at the row order `e'`. Then `ζ` is a weight vector:
the matrix `schur κ` of the diagonal matrices with entries `x τ a` multiplies it by the product of
the `x τ a` to the powers `λ_γ(τ, e τ a) + λ_κ'(τ, e' τ a)`, with `λ = New.diagramWeight`. -/
lemma schur_diagonal_mulVec_eq_smul_of_toPoly_eq [DecidableEq Φ]
    (e e' : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ)) {ζ : WeylIndexFamily n κ → ℤ} {c : ℤ}
    (hζ : toPoly n κ ζ =
      c • (weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) *
        weylKernel n κ' (permArray fun (τ : Φ) (a : n τ) ↦ (e' τ a : ℕ))))
    (x : ∀ τ : Φ, n τ → ℤ) :
    schur κ (fun τ : Φ ↦ diagonal (x τ)) *ᵥ ζ =
      (∏ τ : Φ, ∏ a : n τ, x τ a ^ (diagramWeight (rankAt n) γ (τ, e τ a) +
        diagramWeight (rankAt n) κ' (τ, e' τ a))) • ζ := by
  -- A diagonal matrix is triangular for every row order, so it scales both kernels.
  have h_triangular (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ)) (τ : Φ) :
      (diagonal (x τ))ᵀ.BlockTriangular (e τ) := by
    rw [diagonal_transpose]
    exact blockTriangular_diagonal _
  have h_subst : toPoly n κ (schur κ (fun τ : Φ ↦ diagonal (x τ)) *ᵥ ζ) =
      rowSubst (fun τ : Φ ↦ diagonal (x τ)) (toPoly n κ ζ) := by
    simp [toPoly_schur FitsRanks.refl, detPow]
  refine toPoly_injective ?_
  rw [h_subst, map_smul, hζ, map_smul, map_mul,
    rowSubst_weylKernel_permArray _ _ (h_triangular e),
    rowSubst_weylKernel_permArray _ _ (h_triangular e'), smul_mul_smul_comm, smul_comm c]
  simp only [diagonal_apply_eq, pow_add, prod_mul_distrib]

/-- Let `ζ` be an integral weight vector of weight `w` for `κ + κ'`: the matrix `schur (κ + κ')`
of the diagonal matrices with entries `x τ a` multiplies it by the product of the `x τ a ^ w τ a`.
If the multiplication matrix `comulMatrix ℤ n κ κ'` sends `ζ` to a vector with a nonzero entry at
`(i, i')`, the numbers of entries equal to `a` in the fillings `i` and `i'` add up to `w τ a`. -/
lemma tableauWeight_add_eq_of_comulMatrix_mulVec_ne_zero [DecidableEq Φ]
    {ζ : WeylIndexFamily n (κ + κ') → ℤ} {w : ∀ τ : Φ, n τ → ℕ}
    (h_weight : ∀ x : ∀ τ : Φ, n τ → ℤ, schur (κ + κ') (fun τ : Φ ↦ diagonal (x τ)) *ᵥ ζ =
      (∏ τ : Φ, ∏ a : n τ, x τ a ^ w τ a) • ζ)
    {i : WeylIndexFamily n κ} {i' : WeylIndexFamily n κ'}
    (h_ne : (comulMatrix ℤ n κ κ' *ᵥ ζ) (i, i') ≠ 0) (τ : Φ) (a : n τ) :
    tableauWeight i τ a + tableauWeight i' τ a = w τ a := by
  -- Multiply the row `(τ, a)` by `2` and leave the others: a product of powers of the entries is
  -- then a power of `2`.
  let x (σ : Φ) (b : n σ) : ℤ := if (⟨σ, b⟩ : Σ σ : Φ, n σ) = ⟨τ, a⟩ then 2 else 1
  have h_prod (w : ∀ σ : Φ, n σ → ℕ) : ∏ σ : Φ, ∏ b : n σ, x σ b ^ w σ b = 2 ^ w τ a :=
    calc ∏ σ : Φ, ∏ b : n σ, x σ b ^ w σ b
      _ = ∏ p : Σ σ : Φ, n σ, x p.1 p.2 ^ w p.1 p.2 :=
        (Fintype.prod_sigma fun p : Σ σ : Φ, n σ ↦ x p.1 p.2 ^ w p.1 p.2).symm
      _ = 2 ^ w τ a := by
        have h_other (p : Σ σ : Φ, n σ) (hp : p ≠ ⟨τ, a⟩) : x p.1 p.2 ^ w p.1 p.2 = 1 := by
          simp only [x, ite_eq_right hp, one_pow]
        rw [Fintype.prod_eq_single ⟨τ, a⟩ h_other]
        simp only [x, ite_true]
  -- The entry at `(i, i')` of both sides of the equivariance of the multiplication matrix.
  have h_left : ((schur κ (fun σ : Φ ↦ diagonal (x σ)) ⊗ₖ schur κ' fun σ : Φ ↦ diagonal (x σ)) *ᵥ
        comulMatrix ℤ n κ κ' *ᵥ ζ) (i, i') =
      2 ^ (tableauWeight i τ a + tableauWeight i' τ a) * (comulMatrix ℤ n κ κ' *ᵥ ζ) (i, i') := by
    simp only [schur_diagonal, h_prod, diagonal_kronecker_diagonal, mulVec_diagonal, pow_add]
  have h_right : (comulMatrix ℤ n κ κ' *ᵥ schur (κ + κ') (fun σ : Φ ↦ diagonal (x σ)) *ᵥ ζ)
        (i, i') = 2 ^ w τ a * (comulMatrix ℤ n κ κ' *ᵥ ζ) (i, i') := by
    rw [h_weight, h_prod, mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have h_eq : (2 : ℤ) ^ (tableauWeight i τ a + tableauWeight i' τ a) *
        (comulMatrix ℤ n κ κ' *ᵥ ζ) (i, i') =
      2 ^ w τ a * (comulMatrix ℤ n κ κ' *ᵥ ζ) (i, i') := by
    rw [← h_left, ← h_right, mulVec_mulVec, mulVec_mulVec, comulMatrix_equivariant]
  exact pow_right_injective₀ (by norm_num : (0 : ℤ) < 2) (by norm_num) (mul_right_cancel₀ h_ne h_eq)

/-- Let `v` be an integral vector for `κ` whose nonzero coordinates `v i` lie at fillings `i` in
which every row `(τ, a)` occurs at least `λ(τ, e τ a)` times, with `λ = New.diagramWeight`. Then
`v` is a multiple of the evaluation vector `weylEval n κ y` at the permutation array `y` of the row
order `e`, with factor the pairing of `v` with that vector under the matrix `weylGramOver`. -/
lemma eq_smul_weylEval_of_diagramWeight_le [DecidableEq Φ] (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (v : WeylIndexFamily n κ → ℤ)
    (h_wt : ∀ i : WeylIndexFamily n κ, v i ≠ 0 → ∀ (τ : Φ) (a : n τ),
      diagramWeight (rankAt n) κ (τ, e τ a) ≤ tableauWeight i τ a) :
    v = (v ⬝ᵥ weylGramOver *ᵥ weylEval n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ))) •
      weylEval n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) := by
  -- Pairing with the polynomial of `v` under `fockPairing` is a linear form with the values
  -- `hookNumber κ (rankAt n) * v i` on the basis; apply
  -- `map_nablaBasis_eq_map_weylKernel_mul_weylEval` to it and cancel the hook number.
  funext i
  have h_form := map_nablaBasis_eq_map_weylKernel_mul_weylEval e i (fockPairing ℤ (toPoly n κ v))
    fun h_ne τ a ↦ h_wt i (by
      rw [fockPairing_toPoly_nablaBasis] at h_ne
      exact right_ne_zero_of_mul h_ne) τ a
  rw [fockPairing_toPoly_nablaBasis, ← toPoly_weylEval, fockPairing_toPoly_toPoly, mul_assoc]
    at h_form
  exact mul_left_cancel₀ (Int.cast_ne_zero.mpr hookNumber_pos.ne') h_form

/-- Let the polynomial of the integral vector `ζ` for `β + α` be a multiple of the product of the
kernel of `γ` at the row order `e` and the kernel of `κ'` at the row order `e'`. Suppose that for
every row `(τ, a)` with `λ_β(τ, e τ a) ≠ 0` the sum `λ_β(τ, e τ a) + λ_α(τ, 0)` is at most
`λ_γ(τ, e τ a) + λ_κ'(τ, e' τ a)`, with `λ = New.diagramWeight`. Then the multiplication matrix
`comulMatrix ℤ n β α` sends `ζ` to a pure tensor whose factor for `β` is the evaluation vector at
the permutation array of `e`. -/
lemma exists_comulMatrix_mulVec_eq_vec [DecidableEq Φ] (e e' : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    {ζ : WeylIndexFamily n (β + α) → ℤ} {c : ℤ}
    (hζ : toPoly n (β + α) ζ =
      c • (weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) *
        weylKernel n κ' (permArray fun (τ : Φ) (a : n τ) ↦ (e' τ a : ℕ))))
    (h_wt : ∀ (τ : Φ) (a : n τ), diagramWeight (rankAt n) β (τ, e τ a) ≠ 0 →
      diagramWeight (rankAt n) β (τ, e τ a) + diagramWeight (rankAt n) α (τ, 0) ≤
        diagramWeight (rankAt n) γ (τ, e τ a) + diagramWeight (rankAt n) κ' (τ, e' τ a)) :
    ∃ a : WeylIndexFamily n α → ℤ, comulMatrix ℤ n β α *ᵥ ζ =
      (vecMulVec a (weylEval n β (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)))).vec := by
  -- For each filling `i'` for `α`, the entries at `(·, i')` form a vector `v i'` for `β`.
  let v (i' : WeylIndexFamily n α) (i : WeylIndexFamily n β) : ℤ :=
    (comulMatrix ℤ n β α *ᵥ ζ) (i, i')
  -- At a nonzero entry the weights of `i` and `i'` add up to the weight of `ζ`, and a row occurs
  -- in `i'` at most `λ_α(τ, 0)` times; so it occurs in `i` at least `λ_β(τ, e τ a)` times.
  have h_low (i' : WeylIndexFamily n α) (i : WeylIndexFamily n β) (h_ne : v i' i ≠ 0) (τ : Φ)
      (a : n τ) : diagramWeight (rankAt n) β (τ, e τ a) ≤ tableauWeight i τ a := by
    obtain h_zero | h_pos := Nat.eq_zero_or_pos (diagramWeight (rankAt n) β (τ, e τ a))
    · rw [h_zero]
      exact Nat.zero_le _
    have h_sum : tableauWeight i τ a + tableauWeight i' τ a =
        diagramWeight (rankAt n) γ (τ, e τ a) + diagramWeight (rankAt n) κ' (τ, e' τ a) :=
      tableauWeight_add_eq_of_comulMatrix_mulVec_ne_zero
        (schur_diagonal_mulVec_eq_smul_of_toPoly_eq e e' hζ) h_ne τ a
    have h_single : tableauWeight i' τ a ≤ diagramWeight (rankAt n) α (τ, 0) := by
      simpa using (sum_tableauWeight_le i' τ {a}).1
    have h_count := h_wt τ a h_pos.ne'
    omega
  refine ⟨fun i' ↦ v i' ⬝ᵥ weylGramOver *ᵥ
    weylEval n β (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)), funext fun ⟨i, i'⟩ ↦ ?_⟩
  exact congrFun (eq_smul_weylEval_of_diagramWeight_le e (v i') (h_low i')) i

/-- Over an infinite domain, if the multiplication matrix `comulMatrix R n κ κ'` sends the vector
`ζ` for `κ + κ'` to the pure tensor of `ξ` and `η`, the polynomial `toPoly n (κ + κ') ζ` is the
product of the polynomials of `ξ` and `η`. -/
lemma toPoly_eq_mul_of_comulMatrix_mulVec_eq [IsDomain R] [Infinite R] [DecidableEq Φ]
    {ζ : WeylIndexFamily n (κ + κ') → R} {ξ : WeylIndexFamily n κ → R}
    {η : WeylIndexFamily n κ' → R}
    (h_tensor : comulMatrix R n κ κ' *ᵥ ζ = (vecMulVec η ξ).vec) :
    toPoly n (κ + κ') ζ = toPoly n κ ξ * toPoly n κ' η := by
  -- The multiplication matrix is an isometry, so its transpose sends `G ξ ⊗ G η` to `G ζ`.
  have h_coord : (vecMulVec (weylGramOver *ᵥ η) (weylGramOver *ᵥ ξ)).vec ᵥ* comulMatrix R n κ κ' =
      weylGramOver *ᵥ ζ :=
    calc (vecMulVec (weylGramOver *ᵥ η) (weylGramOver *ᵥ ξ)).vec ᵥ* comulMatrix R n κ κ'
      _ = (comulMatrix R n κ κ')ᵀ *ᵥ ((weylGram n κ).map (Int.cast : ℤ → R) ⊗ₖ
            (weylGram n κ').map (Int.cast : ℤ → R)) *ᵥ (vecMulVec η ξ).vec := by
        simp only [kronecker_mulVec_vec, mul_vecMulVec, vecMulVec_mul, vecMul_transpose,
          mulVec_transpose]
      _ = weylGramOver *ᵥ ζ := by
        rw [← h_tensor, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, comulMatrix_isometry]
  exact (vecMul_comulMatrix_eq_iff.mp h_coord).symm

omit [∀ τ, DecidableEq (n τ)] in
/-- Let `e` be a row order in which every row stands at most one place before its place in
`rowEquivFin`. Let `κ'` have no column of height below `q`, let `β` have none of height `q` or
more and `α` none of a height `h` with `0 < h < q`, and let `β τ h + α τ h = κ' τ h + γ τ h` for
`0 < h < rankAt n τ`. For a row `(τ, a)` with `λ_β(τ, e τ a) ≠ 0`, the sum
`λ_β(τ, e τ a) + λ_α(τ, 0)` is at most `λ_γ(τ, e τ a)` plus `λ_κ'` at the place of the row in
`rowEquivFin`, with `λ = New.diagramWeight`. -/
lemma diagramWeight_add_le_of_ne_zero {q : ℕ} (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (he : ∀ (τ : Φ) (a : n τ), (rowEquivFin n τ a : ℕ) ≤ e τ a + 1)
    (hq : ∀ τ : Φ, ∀ i < q, κ' τ i = 0)
    (hβ : ∀ (τ : Φ) (h : ℕ), q ≤ h → β τ h = 0)
    (hα : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), h < q → α τ h = 0)
    (h_sum : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), (β + α) τ h = (κ' + γ) τ h)
    (τ : Φ) (a : n τ) (h_ne : diagramWeight (rankAt n) β (τ, e τ a) ≠ 0) :
    diagramWeight (rankAt n) β (τ, e τ a) + diagramWeight (rankAt n) α (τ, 0) ≤
      diagramWeight (rankAt n) γ (τ, e τ a) +
        diagramWeight (rankAt n) κ' (τ, rowEquivFin n τ a) := by
  simp only [diagramWeight_apply] at h_ne ⊢
  -- Some column of `β` is higher than `e τ a`, so `e τ a + 1 < q`, and the row stands before
  -- the place `q` in `rowEquivFin`.
  obtain ⟨h₀, h₀_mem, h₀_ne⟩ := exists_ne_zero_of_sum_ne_zero h_ne
  have h_lt : (e τ a : ℕ) + 1 < q := by
    by_contra! h_ge
    exact h₀_ne (hβ τ h₀ (h_ge.trans (mem_Ioo.mp h₀_mem).1))
  -- The columns of `α` of positive height are higher than `e τ a`.
  have h_α : ∑ h ∈ Ioo 0 (rankAt n τ), α τ h ≤ ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), α τ h := by
    refine sum_le_sum_of_ne_zero fun h h_mem h_ne ↦ ?_
    refine mem_Ioo.mpr ⟨lt_of_not_ge fun h_le ↦ h_ne (hα τ h h_mem ?_), (mem_Ioo.mp h_mem).2⟩
    omega
  -- So are the columns of `κ'` beyond the place of the row in `rowEquivFin`.
  have h_κ' : ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), κ' τ h ≤
      ∑ h ∈ Ioo (rowEquivFin n τ a : ℕ) (rankAt n τ), κ' τ h := by
    refine sum_le_sum_of_ne_zero fun h h_mem h_ne ↦ ?_
    refine mem_Ioo.mpr ⟨lt_of_not_ge fun h_le ↦ h_ne (hq τ h ?_), (mem_Ioo.mp h_mem).2⟩
    have h_place := he τ a
    omega
  have h_split : ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), β τ h +
        ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), α τ h =
      ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), κ' τ h + ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), γ τ h := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun h h_mem ↦ h_sum τ h (mem_Ioo.mpr ⟨?_, (mem_Ioo.mp h_mem).2⟩)
    exact (Nat.zero_le _).trans_lt (mem_Ioo.mp h_mem).1
  calc ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), β τ h + ∑ h ∈ Ioo 0 (rankAt n τ), α τ h
    _ ≤ ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), β τ h +
        ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), α τ h := Nat.add_le_add_left h_α _
    _ = ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), γ τ h +
        ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), κ' τ h := h_split.trans (add_comm _ _)
    _ ≤ ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), γ τ h +
        ∑ h ∈ Ioo (rowEquivFin n τ a : ℕ) (rankAt n τ), κ' τ h := Nat.add_le_add_left h_κ' _

/-- Let `e` be a row order in which every row stands at most one place before its place in
`rowEquivFin`. Let `κ'` have no column of height below `q`, and let `κ₀ τ h = κ' τ h + γ τ h` for
`0 < h < rankAt n τ`. Then some integer `c` with `0 < c` (a hook number) satisfies two claims.
(a) `c ≤ (L ^ L) ^ 3` for every bound `L` of the number of boxes of `κ₀` in the columns of height
`h` with `q ≤ h < rankAt n τ`. (b) `c` times the kernel of `γ` at the permutation array of `e`,
times the kernel of `κ'` at that of `rowEquivFin`, equals `toPoly n κ₀ η` for some
`η : WeylIndexFamily n κ₀ → ℤ`. -/
lemma exists_smul_weylKernel_mul_weylKernel_eq_toPoly [DecidableEq Φ] {q : ℕ}
    (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (he : ∀ (τ : Φ) (a : n τ), (rowEquivFin n τ a : ℕ) ≤ e τ a + 1)
    (hq : ∀ τ : Φ, ∀ i < q, κ' τ i = 0)
    (hκ₀ : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = (κ' + γ) τ h) :
    ∃ c : ℤ, 0 < c ∧
      (∀ L : ℕ, ∑ τ : Φ, ∑ h ∈ Ico q (rankAt n τ), h * κ₀ τ h ≤ L → c ≤ (L ^ L) ^ 3) ∧
      ∃ η : WeylIndexFamily n κ₀ → ℤ,
        c • (weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) *
            weylKernel n κ' (permArray fun (τ : Φ) (a : n τ) ↦ (rowEquivFin n τ a : ℕ)) :
              MatrixPoly (Σ τ : Φ, n τ) ℤ) =
          toPoly n κ₀ η := by
  -- Split `κ₀ = β + α`: `β` holds the columns of `γ` of height below `q`, and `α` the others.
  let β : Φ → ℕ → ℕ := fun τ h ↦ if h ∈ Ioo 0 (min q (rankAt n τ)) then γ τ h else 0
  have hβ_le : β ≤ κ₀ := fun τ h ↦ by
    by_cases h_mem : h ∈ Ioo 0 (min q (rankAt n τ))
    · have h_split := hκ₀ τ h (mem_Ioo.mpr ⟨(mem_Ioo.mp h_mem).1,
        (mem_Ioo.mp h_mem).2.trans_le (min_le_right _ _)⟩)
      simp only [β, ite_eq_left h_mem, h_split, Pi.add_apply, le_add_iff_nonneg_left, zero_le]
    · simp only [β, ite_eq_right h_mem, zero_le]
  obtain ⟨α, rfl⟩ := exists_add_of_le hβ_le
  have hβ (τ : Φ) (h : ℕ) (h_le : q ≤ h) : β τ h = 0 :=
    ite_eq_right fun h_mem ↦ h_le.not_gt ((mem_Ioo.mp h_mem).2.trans_le (min_le_left _ _))
  have hα (τ : Φ) (h : ℕ) (h_mem : h ∈ Ioo 0 (rankAt n τ)) (h_lt : h < q) : α τ h = 0 := by
    have h_split : β τ h + α τ h = κ' τ h + γ τ h := hκ₀ τ h h_mem
    have h_low : β τ h = γ τ h :=
      ite_eq_left (mem_Ioo.mpr ⟨(mem_Ioo.mp h_mem).1, lt_min h_lt (mem_Ioo.mp h_mem).2⟩)
    have h_zero := hq τ h h_lt
    omega
  set K_γ : MatrixPoly (Σ τ : Φ, n τ) ℤ :=
    weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ))
  set K_κ' : MatrixPoly (Σ τ : Φ, n τ) ℤ :=
    weylKernel n κ' (permArray fun (τ : Φ) (a : n τ) ↦ (rowEquivFin n τ a : ℕ))
  let K_β : MatrixPoly (Σ τ : Φ, n τ) ℤ :=
    weylKernel n β (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ))
  -- The kernel of `β` divides that of `γ`, and is not zero.
  obtain ⟨F, hF⟩ : K_β ∣ K_γ := weylKernel_dvd_weylKernel _ fun τ h _ ↦ by
    by_cases h_mem : h ∈ Ioo 0 (min q (rankAt n τ))
    · simp only [β, ite_eq_left h_mem, le_refl]
    · simp only [β, ite_eq_right h_mem, zero_le]
  have hK_ne : K_β ≠ 0 := fun h_zero ↦ by
    simpa [K_β, h_zero] using eval_weylKernel_permArray (R := ℤ) (κ := β) e
  -- The product of the kernels has the weight of `β + α`, so the hook number of `β + α` times it
  -- is the polynomial of an integral vector `ζ`.
  have h_weight : diagramWeight (rankAt n) (β + α) =
      diagramWeight (rankAt n) γ + diagramWeight (rankAt n) κ' := by
    ext ⟨τ, i⟩
    rw [Finsupp.add_apply, diagramWeight_apply, diagramWeight_apply, diagramWeight_apply,
      ← sum_add_distrib]
    refine sum_congr rfl fun h h_mem ↦ (hκ₀ τ h (mem_Ioo.mpr ⟨?_, (mem_Ioo.mp h_mem).2⟩)).trans
      (add_comm _ _)
    exact (Nat.zero_le _).trans_lt (mem_Ioo.mp h_mem).1
  have h_mem : K_γ * K_κ' ∈ nablaFamily ℤ n (β + α) := by
    rw [nablaFamily, h_weight]
    exact SetLike.mul_mem_graded (weylKernel_mem_nablaFamily _) (weylKernel_mem_nablaFamily _)
  obtain ⟨ζ, hζ⟩ := exists_toPoly_eq_hookNumber_smul h_mem
  -- The multiplication matrix sends `ζ` to a pure tensor `a ⊗ ev`, with `ev` the evaluation
  -- vector for `β`, whose polynomial is the kernel of `β`. Divide by that kernel.
  obtain ⟨a, ha⟩ := exists_comulMatrix_mulVec_eq_vec e (rowEquivFin n) hζ
    (diagramWeight_add_le_of_ne_zero e he hq hβ hα hκ₀)
  have h_quot : toPoly n α a = hookNumber (β + α) (rankAt n) • (F * K_κ') := by
    have h_eval : toPoly n β (weylEval n β (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ))) =
        K_β := toPoly_weylEval _
    refine mul_left_cancel₀ hK_ne ?_
    rw [← h_eval, ← toPoly_eq_mul_of_comulMatrix_mulVec_eq ha, hζ, hF, h_eval, mul_assoc,
      mul_smul_comm]
  -- Pair with the basis for `α`: the hook number of `α` times `a` is the hook number of `β + α`
  -- times an integral vector `a₀`.
  let a₀ : WeylIndexFamily n α → ℤ := fun j ↦ fockPairing ℤ (F * K_κ') (nablaBasis ℤ n α j)
  have h_coeff : hookNumber α (rankAt n) • a = hookNumber (β + α) (rankAt n) • a₀ := by
    funext j
    simpa [a₀, -zsmul_eq_mul] using congrArg (fun P ↦ fockPairing ℤ P (nablaBasis ℤ n α j)) h_quot
  -- An integer left inverse `M` of the multiplication matrix recovers `ζ` from the tensor.
  obtain ⟨M, hM⟩ := hasLeftInv_comulMatrix (n := n) (κ := β) (κ' := α)
  let η : WeylIndexFamily n (β + α) → ℤ := M *ᵥ (vecMulVec a₀
    (weylEval n β (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)))).vec
  have h_η : hookNumber (β + α) (rankAt n) • η = hookNumber α (rankAt n) • ζ := by
    rw [← one_mulVec ζ, ← hM, ← mulVec_mulVec, ha, ← mulVec_smul, ← mulVec_smul, ← vec_smul,
      ← vec_smul, ← smul_vecMulVec, ← smul_vecMulVec, h_coeff]
  refine ⟨hookNumber α (rankAt n), hookNumber_pos, fun L hL ↦ ?_, η, ?_⟩
  · -- A column of `α` of positive height below `q` does not occur.
    have h_boxes (τ : Φ) : ∑ h ∈ range (rankAt n τ), h * α τ h ≤
        ∑ h ∈ Ico q (rankAt n τ), h * (β + α) τ h :=
      calc ∑ h ∈ range (rankAt n τ), h * α τ h
        _ ≤ ∑ h ∈ Ico q (rankAt n τ), h * α τ h := by
          refine sum_le_sum_of_ne_zero fun h h_mem h_ne ↦ ?_
          have h_pos : 0 < h := Nat.pos_of_ne_zero (left_ne_zero_of_mul h_ne)
          have h_rank : h < rankAt n τ := mem_range.mp h_mem
          refine mem_Ico.mpr ⟨le_of_not_gt fun h_lt ↦ right_ne_zero_of_mul h_ne ?_, h_rank⟩
          exact hα τ h (mem_Ioo.mpr ⟨h_pos, h_rank⟩) h_lt
        _ ≤ ∑ h ∈ Ico q (rankAt n τ), h * (β + α) τ h :=
          sum_le_sum fun h _ ↦ Nat.mul_le_mul_left h (Nat.le_add_left _ _)
    exact hookNumber_le ((sum_le_sum fun τ _ ↦ h_boxes τ).trans hL)
  · refine smul_right_injective _ (hookNumber_pos (κ := β + α) (N := rankAt n)).ne' ?_
    change hookNumber (β + α) (rankAt n) • hookNumber α (rankAt n) • (K_γ * K_κ') =
      hookNumber (β + α) (rankAt n) • toPoly n (β + α) η
    rw [← map_smul, h_η, map_smul, hζ, smul_comm]

/-- Let `κ'` have no column of height below `q`, and let `κ₀ τ h = κ' τ h + γ τ h` for
`0 < h < rankAt n τ`. Here `weylKernel n κ y` is the polynomial `f(yᵀx)` in `x`, with `f` the
product of leading minors for `κ`, and `toPoly n κ₀ η` is `Σ_i (Gη)_i b_i` for a Weyl vector `η`
(Gram matrix `G`, basis minor products `b_i`). Then some integer `c` with `0 < c` (a hook number)
satisfies two claims. (a) `c ≤ (L ^ L) ^ 3` for every bound `L` of the number of boxes of `κ₀` in
the columns of height `h` with `q ≤ h < rankAt n τ`. (b) `c` times `weylKernel n γ` at the
permutation array of `rowEquivFin` shifted cyclically by one, times `weylKernel n κ'` at that of
`rowEquivFin`, equals `toPoly n κ₀ η` for some `η : WeylIndexFamily n κ₀ → ℤ`. -/
lemma exists_smul_weylKernel_mul_eq_toPoly [DecidableEq Φ] {q : ℕ}
    (hq : ∀ τ : Φ, ∀ i < q, κ' τ i = 0)
    (hκ₀ : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = (κ' + γ) τ h) :
    ∃ c : ℤ, 0 < c ∧
      (∀ L : ℕ, ∑ τ : Φ, ∑ h ∈ Ico q (rankAt n τ), h * κ₀ τ h ≤ L → c ≤ (L ^ L) ^ 3) ∧
      ∃ η : WeylIndexFamily n κ₀ → ℤ,
        c • (weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦
              ((finRotate (rankAt n τ)).symm (rowEquivFin n τ a) : ℕ)) *
            weylKernel n κ' (permArray fun (τ : Φ) (a : n τ) ↦ (rowEquivFin n τ a : ℕ)) :
              MatrixPoly (Σ τ : Φ, n τ) ℤ) =
          toPoly n κ₀ η := by
  -- The cyclic shift moves every row but the first one place back, so
  -- `exists_smul_weylKernel_mul_weylKernel_eq_toPoly` applies to the shifted row order.
  have h_rotate (M : ℕ) (i : Fin M) : (finRotate M i : ℕ) ≤ i + 1 := by
    cases M with
    | zero => exact i.elim0
    | succ M =>
      rw [coe_finRotate]
      split_ifs <;> omega
  refine exists_smul_weylKernel_mul_weylKernel_eq_toPoly
    (fun τ : Φ ↦ (rowEquivFin n τ).trans (finRotate (rankAt n τ)).symm) (fun τ a ↦ ?_) hq hκ₀
  obtain ⟨i, hi⟩ := (finRotate (rankAt n τ)).surjective (rowEquivFin n τ a)
  rw [Equiv.trans_apply, ← hi, Equiv.symm_apply_apply]
  exact h_rotate _ i

end New.GL

end BranchingVector

/-!
## The norm of a branching map

Let `T` be the matrix of a branching map over `ℂ` and `C` its adjoint for the forms of the two
matrices `weylGramOver`. By equivariance `T * C` commutes with every `schur κ₀ g`, so it is a scalar
(`New.mem_range_scalar_of_commute_schur`). This scalar is the squared norm of the image under `C`
of the evaluation vector at the permutation array, and the hypothesis on the top vector bounds it.
The norm bound follows from the inequality `New.GL.posDef_cauchy_schwarz`.
-/

section NormBound

open Matrix ComplexOrder

namespace New.GL

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n N : Φ → Type} [∀ τ : Φ, Fintype (n τ)]
  [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, Fintype (N τ)] [∀ τ : Φ, DecidableEq (N τ)]
  (ι : ∀ τ : Φ, n τ ⊕ Unit ≃ N τ) {κ₀ γ κ' : Φ → ℕ → ℕ}

/-- Let `B` be an integral matrix with
`B * schur (γ + κ') (diag(g, 1)) = (∏ τ, det (g τ) ^ κ' τ (rankAt n τ)) • (schur κ₀ g * B)`
for all complex `g`, with `diag(g, 1)` built by `blockScalar ι`. Let `v` be the Gram matrix
`weylGramOver` times `weylEval` at the permutation array of `rowEquivFin`, and assume also that the
row vector `v ᵥ* B` has the polynomial `c • branchVector ℂ ι γ κ'` under `nablaCombination`
(ξ ↦ Σ ξ_i b_i over the basis products of minors). Then
`weylNormSq (B *ᵥ ξ) ≤ c ^ 2 * weylNormSq ξ` for every complex vector `ξ`. -/
lemma weylNormSq_mulVec_le_of_equivariant {c : ℤ}
    {B : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) ℤ}
    (B_top : nablaCombination (γ + κ') ((weylGramOver *ᵥ weylEval n κ₀
        (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) ᵥ*
          B.map (Int.cast : ℤ → ℂ)) =
      (c : ℂ) • branchVector ℂ ι γ κ')
    (B_block : ∀ g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ,
      B.map (Int.cast : ℤ → ℂ) * schur (γ + κ') (blockScalar ι g 1) =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * B.map (Int.cast : ℤ → ℂ)))
    (ξ : WeylIndexFamily N (γ + κ') → ℂ) :
    weylNormSq (B.map (Int.cast : ℤ → ℂ) *ᵥ ξ) ≤ (c : ℝ) ^ 2 * weylNormSq ξ := by
  -- Let `G₀`, `G` be the two matrices `weylGramOver` and `T` the matrix `B` over `ℂ`. The adjoint
  -- `C` of `T` for their forms is given by `G * C = Tᵀ * G₀`. By equivariance `T * C` commutes with
  -- every `schur κ₀ g`, so it is a scalar `m`. Then `‖C x‖² = m ‖x‖²`, and `m = ‖C v‖² ≤ c ^ 2` for
  -- the evaluation vector `v` of norm 1. The inequality `posDef_cauchy_schwarz` for `ξ` and
  -- `C (T ξ)` gives the bound.
  obtain ⟨T, hT⟩ : ∃ T : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) ℂ,
      T = B.map (Int.cast : ℤ → ℂ) := ⟨_, rfl⟩
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily n κ₀) ℂ,
      G₀ = weylGramOver := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Matrix (WeylIndexFamily N (γ + κ')) (WeylIndexFamily N (γ + κ')) ℂ,
      G = weylGramOver := ⟨_, rfl⟩
  simp only [← hT] at B_block ⊢
  rw [← hT, ← hG₀] at B_top
  have hT_real : Tᴴ = Tᵀ := by
    rw [hT]
    ext i j
    simp
  have hG_posDef : G.PosDef := hG ▸ weylGramOver_posDef
  have hG₀_herm : G₀ᴴ = G₀ := by rw [hG₀, weylGramOver_posDef.isHermitian.eq]
  have hG_det : IsUnit G.det := (isUnit_iff_isUnit_det G).1 hG_posDef.isUnit
  have h_coe (x : WeylIndexFamily N (γ + κ') → ℂ) : (weylNormSq x : ℂ) = star x ⬝ᵥ G *ᵥ x := by
    rw [hG, coe_weylNormSq]
  have h_coe₀ (x : WeylIndexFamily n κ₀ → ℂ) : (weylNormSq x : ℂ) = star x ⬝ᵥ G₀ *ᵥ x := by
    rw [hG₀, coe_weylNormSq]
  obtain ⟨C, hGC⟩ : ∃ C : Matrix (WeylIndexFamily N (γ + κ')) (WeylIndexFamily n κ₀) ℂ,
      G * C = Tᵀ * G₀ :=
    ⟨G⁻¹ * (Tᵀ * G₀), mul_nonsing_inv_cancel_left _ _ hG_det⟩
  have hCG : Cᴴ * G = G₀ * T := by
    have h := congrArg conjTranspose hGC
    rwa [← hT_real, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      hG_posDef.isHermitian.eq, hG₀_herm] at h
  -- `schur (γ + κ') (diag(g, 1)) * C = det • (C * schur κ₀ g)`: the adjoint of the equivariance.
  have h_adj (g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) :
      schur (γ + κ') (blockScalar ι g 1) * C =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (C * schur κ₀ g) := by
    have h_tr : (fun τ : Φ ↦ (blockScalar ι g 1 τ)ᵀ) = blockScalar ι (fun τ : Φ ↦ (g τ)ᵀ) 1 := by
      funext τ
      simp [blockScalar, fromBlocks_transpose]
    have h_cancel : G * (schur (γ + κ') (blockScalar ι g 1) * C) =
        G * ((∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (C * schur κ₀ g)) := by
      calc G * (schur (γ + κ') (blockScalar ι g 1) * C)
        _ = (T * schur (γ + κ') (blockScalar ι (fun τ : Φ ↦ (g τ)ᵀ) 1))ᵀ * G₀ := by
          rw [← Matrix.mul_assoc, hG, weylGramOver_mul_schur, ← hG, h_tr, Matrix.mul_assoc, hGC,
            ← Matrix.mul_assoc, transpose_mul]
        _ = (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (Tᵀ * (G₀ * schur κ₀ g)) := by
          rw [B_block, hG₀, weylGramOver_mul_schur]
          simp only [transpose_smul, transpose_mul, Matrix.smul_mul, Matrix.mul_assoc,
            det_transpose]
        _ = G * ((∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (C * schur κ₀ g)) := by
          rw [← Matrix.mul_assoc, ← hGC, Matrix.mul_smul, Matrix.mul_assoc]
    calc schur (γ + κ') (blockScalar ι g 1) * C
      _ = G⁻¹ * (G * (schur (γ + κ') (blockScalar ι g 1) * C)) :=
        (nonsing_inv_mul_cancel_left _ _ hG_det).symm
      _ = (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (C * schur κ₀ g) := by
        rw [h_cancel, nonsing_inv_mul_cancel_left _ _ hG_det]
  obtain ⟨m, hm⟩ := mem_range_scalar_of_commute_schur (T := T * C) fun g hg ↦ by
    have h_det : (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun τ _ ↦ pow_ne_zero _ (det_ne_zero_of_left_inverse (hg τ))
    have h_left : T * ((∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (C * schur κ₀ g)) =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * T) * C := by
      rw [← h_adj g, ← Matrix.mul_assoc, B_block]
    have h_smul : (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (T * C * schur κ₀ g) =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * (T * C)) := by
      rw [Matrix.mul_assoc T C, ← Matrix.mul_smul T, h_left, Matrix.smul_mul, Matrix.mul_assoc]
    exact smul_right_injective _ h_det h_smul
  have hTC : T * C = m • (1 : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily n κ₀) ℂ) := by
    rw [← hm, scalar_apply, smul_one_eq_diagonal]
  have h_CGC : Cᴴ * (G * C) = m • G₀ := by
    rw [← Matrix.mul_assoc, hCG, Matrix.mul_assoc, hTC, Matrix.mul_smul, Matrix.mul_one]
  have h_C (x : WeylIndexFamily n κ₀ → ℂ) : (weylNormSq (C *ᵥ x) : ℂ) = m * weylNormSq x := by
    rw [h_coe, h_coe₀, star_mulVec_dotProduct]
    simp only [mulVec_mulVec, h_CGC, smul_mulVec, dotProduct_smul, smul_eq_mul]
  -- The scalar is the squared norm of `C v`, which is at most `c ^ 2`.
  have h_toPoly : toPoly N (γ + κ') (C *ᵥ weylEval n κ₀
        (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) =
      toPoly N γ ((c : ℂ) • weylEval N γ
          (permArray fun (τ : Φ) (i : N τ) ↦ (newRowOrder ι 0 τ i : ℕ))) *
        toPoly N κ' (weylEval N κ'
          (permArray fun (τ : Φ) (i : N τ) ↦ (newRowOrder ι ⊤ τ i : ℕ))) := by
    rw [map_smul, toPoly_weylEval, toPoly_weylEval, ← nablaCombination_weylGramOver_mulVec, ← hG,
      mulVec_mulVec, hGC, ← mulVec_mulVec, mulVec_transpose, B_top, branchVector, smul_mul_assoc]
  have h_m : (m : ℂ) = (weylNormSq (C *ᵥ weylEval n κ₀
      (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) : ℝ) := by
    rw [h_C, weylNormSq_weylEval_permArray (rowEquivFin n), Complex.ofReal_one, mul_one]
  have h_m_le : weylNormSq (C *ᵥ weylEval n κ₀
      (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) ≤ (c : ℝ) ^ 2 := by
    refine (weylNormSq_le_mul_of_toPoly_eq h_toPoly).trans_eq ?_
    rw [weylNormSq_smul, weylNormSq_weylEval_permArray (newRowOrder ι 0),
      weylNormSq_weylEval_permArray (newRowOrder ι ⊤), mul_one, mul_one, Complex.norm_intCast,
      sq_abs]
  -- The pairing of `ξ` and `C (T ξ)` is `‖T ξ‖²`.
  have h_GCT : G * (C * T) = Tᵀ * (G₀ * T) := by
    rw [← Matrix.mul_assoc, hGC, Matrix.mul_assoc]
  have h_pair : star ξ ⬝ᵥ G *ᵥ (C *ᵥ (T *ᵥ ξ)) = (weylNormSq (T *ᵥ ξ) : ℂ) := by
    rw [h_coe₀, star_mulVec_dotProduct, hT_real]
    simp only [mulVec_mulVec, h_GCT]
  have h_norm : weylNormSq (C *ᵥ (T *ᵥ ξ)) = weylNormSq (C *ᵥ weylEval n κ₀
      (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) * weylNormSq (T *ᵥ ξ) := by
    have h := h_C (T *ᵥ ξ)
    rw [h_m] at h
    exact_mod_cast h
  have h_cs : weylNormSq (T *ᵥ ξ) ^ 2 ≤ weylNormSq (C *ᵥ (T *ᵥ ξ)) * weylNormSq ξ := by
    have h := posDef_cauchy_schwarz hG_posDef ξ (C *ᵥ (T *ᵥ ξ))
    rwa [h_pair, ← h_coe, ← h_coe, Complex.ofReal_re, Complex.ofReal_re, Complex.norm_real,
      Real.norm_eq_abs, sq_abs] at h
  rcases (weylNormSq_nonneg (T *ᵥ ξ)).eq_or_lt with h_zero | h_pos
  · rw [← h_zero]
    exact mul_nonneg (sq_nonneg _) (weylNormSq_nonneg ξ)
  · refine le_trans (le_of_mul_le_mul_right ?_ h_pos)
      (mul_le_mul_of_nonneg_right h_m_le (weylNormSq_nonneg ξ))
    rw [h_norm] at h_cs
    linarith

end New.GL

end NormBound

end
