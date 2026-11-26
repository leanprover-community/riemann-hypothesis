module

public import Lib.GLn.Branching.NormBound

/-!
# Branching from GL(n+1) to GL(n) × GL(1): integral equivariant branching maps

This file constructs the integral branching map from `GL(n + 1)` to `GL(n) × GL(1)` from its
value at one point, proves its norm bound, and shows that it spans the maps that are equivariant
for the unitary block group. Vectors are coordinates indexed by `New.WeylIndexFamily n κ`
(standard fillings), and `New.schur κ z` is the matrix of `z` in these coordinates. `New.weylRep κ
e` is its twist by `det ^ e` on invertible matrices, `New.weylNormSq` is the squared norm for the
Gram matrix, and `New.GL.blockScalar ι g s` is the matrix `diag(g, s)`.

## Main definitions and results

* `New.SpansBranchingMaps`: a matrix spans the maps that are equivariant for the unitary block
  group.
* `New.GL.exists_int_branching_of_weylKernel`: an integral equivariant matrix from its value at one
  point.
* `New.exists_branching_matrix`: the branching map, its norm bound and its uniqueness.

Notions from other files:
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
* `New.GL.branchVector`: the product of the leading minors to the powers `γ` with the new row first
  and to the powers `κ'` with the new row last.

## Relation to the literature

Branching from GL(n+1) to GL(n) with multiplicity one. Here the branching map is given for one
interlacing pair as an integer matrix that is equivariant over every field of characteristic 0 and
satisfies an explicit norm bound, and every unitarily equivariant map is a multiple of it. That it
is non-zero is not part of the statement. Source: Goodman, Wallach 2009, Theorem 8.1.1;
Zhelobenko, Compact Lie Groups and their Representations, 1973, ch. X; Molev, Gelfand-Tsetlin bases
for classical Lie algebras, arXiv math/0211289.
-/

@[expose] public section

noncomputable section

section Branching

open MvPolynomial Finset Fintype Matrix ComplexOrder Norms.L2Operator RingHom

namespace New.GL

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ]
  {n N : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, Fintype (N τ)]
  [∀ τ : Φ, DecidableEq (N τ)] (ι : ∀ τ : Φ, n τ ⊕ Unit ≃ N τ) {κ κ₀ γ κ' : Φ → ℕ → ℕ}

/-- `New.SpansBranchingMaps ι e₀ e A` says that `A` spans the complex maps that are equivariant for
the unitary points of the block group: let `T` be a complex matrix such that, for every tuple `g`
of unitary matrices (`(g τ)ᴴ * g τ = 1`), some `x` with blocks `x τ = diag(g τ, 1)` along `ι`
satisfies `T * ρ_{κ,e}(x) = ρ_{κ₀,e₀}(g) * T`; then `T` is a multiple of `A`. Here `ρ_{κ,e}` is
`New.weylRep κ e`, the Schur matrix times the powers `e τ` of the determinants, and
`New.GL.blockScalar ι g 1` is the block matrix `diag(g τ, 1)`. -/
def _root_.New.SpansBranchingMaps (e₀ e : Φ → ℤ)
    (A : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N κ) ℂ) : Prop :=
  ∀ T : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N κ) ℂ,
    (∀ g : ∀ τ : Φ, GL (n τ) ℂ, (∀ τ : Φ, (g τ).valᴴ * (g τ).val = 1) →
      ∃ x : (τ : Φ) → GL (N τ) ℂ,
        (∀ τ : Φ, (x τ).val = blockScalar ι (fun τ : Φ ↦ (g τ).val) 1 τ) ∧
        T * weylRep κ e x = weylRep κ₀ e₀ g * T) →
    ∃ a : ℂ, T = a • A

/-- There is a complex vector `v` whose images `schur κ (diag(g, 1)) *ᵥ v`, for `g` ranging over
tuples of lower triangular matrices on the rows `n τ`, span the whole space: a row vector `r`
killing all of them is zero. Here `schur κ` is the Schur matrix, acting on the vectors indexed by
`WeylIndexFamily N κ`, `diag(g, 1)` is `blockScalar ι g 1`, and "lower triangular" is written
`(g τ)ᵀ.BlockTriangular (rowEquivFin n τ)` for the fixed numbering `rowEquivFin n τ` of the rows.

This cyclic vector gives multiplicity at most one in the branching rule from GL (n + 1) to GL n
(`New.GL.spansBranchingMaps_of_equivariant`). -/
lemma exists_cyclic_lower_triangular (κ : Φ → ℕ → ℕ) :
    ∃ v : WeylIndexFamily N κ → ℂ, ∀ r : WeylIndexFamily N κ → ℂ,
      (∀ g : (τ : Φ) → Matrix (n τ) (n τ) ℂ, (∀ τ : Φ, (g τ)ᵀ.BlockTriangular (rowEquivFin n τ)) →
        r ⬝ᵥ schur κ (blockScalar ι g 1) *ᵥ v = 0) →
      r = 0 := by
  -- Let `u` be the identity matrix with new row `(1, …, 1)` and `v` the evaluation vector at the
  -- permutation array `permArray E` of the row order `E` (new row last); the cyclic vector is
  -- `schur κ u *ᵥ v`.
  -- The map `M ↦ (u + M - u * U M) * (1 + U M)` is a submersion at `0`, and the polynomial
  -- function `z ↦ r ⬝ᵥ schur κ z *ᵥ v` vanishes on its image, hence everywhere.
  -- Below, `(1 - u • U) M` is `M - u * U M`.
  let E : ∀ τ : Φ, N τ ≃ Fin (rankAt N τ) := newRowOrder ι ⊤
  let u (τ : Φ) : Matrix (N τ) (N τ) ℂ := of fun a c ↦ if a = ι τ (.inr ()) ∨ a = c then 1 else 0
  let v : WeylIndexFamily N κ → ℂ := weylEval N κ (permArray fun (τ : Φ) (a : N τ) ↦ (E τ a : ℕ))
  -- `U M` is upper triangular for the order `E`, equals `M` above the diagonal, and its column
  -- sums are the new row of `M`.
  let U₀ (M : ∀ τ : Φ, Matrix (N τ) (N τ) ℂ) (τ : Φ) : Matrix (N τ) (N τ) ℂ := of fun a c ↦
    (if E τ a < E τ c then M τ a c else 0) +
      if a = c then M τ (ι τ (.inr ())) c - ∑ d with E τ d < E τ c, M τ d c else 0
  have hU₀_linear : IsLinearMap ℂ U₀ := by
    constructor
    · simp only [Pi.add_apply, Matrix.add_apply, sum_add_distrib, funext_iff, of_add_of,
      EmbeddingLike.apply_eq_iff_eq, U₀]
      intro x y τ a c
      split_ifs <;> ring
    · simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, ← mul_sum, funext_iff, smul_of,
      EmbeddingLike.apply_eq_iff_eq, U₀]
      intro c x τ a c'
      split_ifs <;> ring
  let U : (∀ τ : Φ, Matrix (N τ) (N τ) ℂ) →L[ℂ] ∀ τ : Φ, Matrix (N τ) (N τ) ℂ :=
    (hU₀_linear.mk' U₀).toContinuousLinearMap
  refine ⟨schur κ u *ᵥ v, fun r hr ↦ ?_⟩
  -- The new row of `u * U M` is that of `M` and its other rows are those of `U M`; so the first
  -- factor has new row `(1, …, 1)` and zeros above the diagonal in the other rows.
  have h_factor (M : ∀ τ : Φ, Matrix (N τ) (N τ) ℂ) :
      ∃ g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ, (∀ τ : Φ, (g τ)ᵀ.BlockTriangular (rowEquivFin n τ)) ∧
        u + (1 - u • U) M = blockScalar ι g 1 * u := by
    refine ⟨fun τ ↦ ((1 + M - U M) τ).submatrix (ι τ ∘ .inl) (ι τ ∘ .inl), ?_⟩
    simp only [BlockTriangular, newRowOrder, Pi.top_apply, Fin.top_eq_last, Equiv.optionCongr_symm,
      Equiv.symm_trans, Equiv.symm_symm, finCongr_symm, Equiv.trans_apply, Equiv.optionCongr_apply,
      finCongr_apply, Fin.cast_lt_cast, sum_filter, reindex_equiv (ι _), Equiv.symm_apply_apply,
      sum_sum_type, Equiv.optionEquivSumPUnit_symm_inl, Option.map_some, finSuccEquiv'_symm_some,
      Fin.succAbove_last, univ_unique, PUnit.default_eq_unit, Equiv.optionEquivSumPUnit_symm_inr,
      Option.map_none, finSuccEquiv'_symm_none, sum_singleton, LinearMap.coe_toContinuousLinearMap',
      IsLinearMap.mk'_apply, Pi.sub_apply, Pi.add_apply, Pi.one_apply, transpose_apply,
      submatrix_apply, Function.comp_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, of_apply, Fin.castSucc_lt_castSucc_iff,
      sub_eq_zero, sub_apply, one_apply_eq_self, smul_apply, smul_eq_mul, blockScalar.eq_unfold,
      reindex_apply, diagonal_one, funext_iff, Pi.mul_apply, ← ext_iff, Matrix.mul_apply, ite_mul,
      one_mul, zero_mul, or_self, sum_ite_irrel, sum_add_distrib, sum_const_zero, mul_ite, mul_one,
      mul_zero, reduceCtorEq, false_or, true_or, ↓reduceIte, Sum.forall, add_zero,
      Finset.sum_ite_eq', mem_univ, Fin.castSucc_lt_last, lt_self_iff_false, zero_add,
      Finset.sum_ite_eq, fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.zero_apply, sub_self,
      implies_true, and_true, or_false, fromBlocks_apply₂₁, fromBlocks_apply₂₂, add_eq_left,
      add_sub_cancel, U, U₀, E, u]
    refine ⟨fun τ i j hlt ↦ ?_, fun x ↦ ⟨fun a a₁ ↦ (add_sub_assoc _ _ _).symm,
      fun b a ↦ ?_⟩⟩
    · have hne : j ≠ i := fun h ↦ by subst h; exact lt_irrefl _ hlt
      simp only [hne, ↓reduceIte, zero_add, hlt, add_zero]
    · cases b
      ring
  -- The upper triangular second factor only scales `v`.
  have h_eigen (M : ∀ τ : Φ, Matrix (N τ) (N τ) ℂ) : schur κ (fun τ : Φ ↦ 1 + U M τ) *ᵥ v =
      (∏ τ : Φ, ∏ a : N τ, (1 + U M) τ a a ^ diagramWeight (rankAt N) κ (τ, E τ a)) • v := by
    have h_upper (τ : Φ) : (1 + U M τ)ᵀᵀ.BlockTriangular (E τ) := by
      simp only [BlockTriangular, LinearMap.coe_toContinuousLinearMap', IsLinearMap.mk'_apply,
        transpose_add, transpose_one, transpose_of, transpose_apply, Matrix.add_apply,
        Matrix.one_apply, of_apply, U, U₀]
      intro i j hlt
      have hne : j ≠ i := fun h ↦ by subst h; exact lt_irrefl _ hlt
      have hnot : ¬ E τ i < E τ j := not_lt_of_gt hlt
      simp only [Function.swap, hne, hne.symm, hnot, ↓reduceIte, add_zero]
    -- Both sides are coordinates of the kernel at `permArray E`, substituted by `1 + U M`.
    exact toPoly_injective (by simpa [v] using rowSubst_weylKernel_permArray E _ h_upper)
  let P : MvPolynomial ((τ : Φ) × N τ × N τ) ℂ := C ∘ r ⬝ᵥ schur κ (genericMatrixAt ℂ N) *ᵥ C ∘ v
  have hP (z : ∀ τ : Φ, Matrix (N τ) (N τ) ℂ) : evalMatrix z P = r ⬝ᵥ schur κ z *ᵥ v := by
    simp [P, Function.comp_def, map_dotProduct, map_mulVec]
  have h_vanish (M : ∀ τ : Φ, Matrix (N τ) (N τ) ℂ) :
      evalMatrix ((u + (1 - u • U) M) * (1 + U M)) P = 0 := by
    obtain ⟨g, hg, hM⟩ := h_factor M
    rw [hM, hP]
    simp [Pi.mul_def, hr g hg, schur_mul_left, h_eigen, ← mulVec_mulVec, mulVec_smul]
  have h_zero (z : ∀ τ : Φ, Matrix (N τ) (N τ) ℂ) : r ⬝ᵥ schur κ z *ᵥ v = 0 := by
    rw [← hP]
    refine eq_zero_of_submersion analyticOnNhd_evalMatrix
      (((1 - u • U).hasStrictFDerivAt.const_add u).fun_mul' (U.hasStrictFDerivAt.const_add 1))
      (a := 0) ?_ (.of_forall h_vanish) z
    -- Product rule; as `U 0 = 0`, the derivative at `0` is `u * U M + (M - u * U M) = M`.
    simp [Module.End.one_eq_id]
  -- The vectors `schur κ g *ᵥ v` span (`ext_schur_weylEval`), and `r` is orthogonal to all of them.
  refine (dotProductEquiv ℂ (WeylIndexFamily N κ)).injective (ext_schur_weylEval E fun g ↦ ?_)
  simpa [v] using h_zero fun τ : Φ ↦ (g τ).val

/-- The kernel of the branching map: for arrays `x` (rows `n`) and `y` (rows `N`) over a commutative
ring `S`, the value of `branchVector S ι γ κ'` at `diag(xᵀ, 1) y`, where `xᵀ` is the transposed
square part of `x` in the row order `rowEquivFin`. -/
private def branchKernel (γ κ' : Φ → ℕ → ℕ) {S : Type} [CommRing S] (x : Sigma n × ℕ → S)
    (y : Sigma N × ℕ → S) : S :=
  eval y (rowSubst (blockScalar ι (fun τ : Φ ↦ (squarePart (rowEquivFin n) x τ)ᵀ) 1)
    (branchVector S ι γ κ'))

variable (n) in
/-- The linear map `θ ↦ toPoly n κ₀ θ * detPow S n d` with `d τ = κ' τ (rankAt n τ)`: the
polynomial of the coordinate vector `θ` times the powers `d τ` of the determinants. -/
private def detPowToPoly (κ₀ κ' : Φ → ℕ → ℕ) (S : Type) [CommRing S] :
    (WeylIndexFamily n κ₀ → S) →ₗ[S] MatrixPoly (Sigma n) S :=
  .mulRight S (detPow S n fun τ : Φ ↦ κ' τ (rankAt n τ)) ∘ₗ toPoly n κ₀

omit [DecidableEq Φ] [∀ τ : Φ, DecidableEq (N τ)] [∀ τ : Φ, DecidableEq (n τ)] in
/-- A ring homomorphism `φ` commutes with `branchKernel`: it sends the kernel at `x` and `y` to
the kernel at `φ ∘ x` and `φ ∘ y`. -/
private lemma map_branchKernel {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T)
    (x : Sigma n × ℕ → S) (y : Sigma N × ℕ → S) :
    φ (branchKernel ι γ κ' x y) =
      branchKernel ι γ κ' (fun p : Sigma n × ℕ ↦ φ (x p)) fun p : Sigma N × ℕ ↦ φ (y p) := by
  simp only [branchKernel, blockScalar.eq_unfold, reindex_apply, squarePart, transpose_of,
    Pi.one_apply, diagonal_one, branchVector, weylKernel, permArray, map_mul, eval_rowSubst,
    submatrix_apply, reindex_equiv (ι _), Equiv.symm_apply_apply, sum_sum_type, univ_unique,
    PUnit.default_eq_unit, sum_singleton, of_apply, ite_mul, one_mul, zero_mul, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, Matrix.zero_apply, add_zero, fromBlocks_apply₂₁, sum_const_zero,
    fromBlocks_apply₂₂, one_apply_eq, zero_add, apply_ite, map_eval, Function.comp_def, map_add,
    map_sum, map_zero, map_highestPoly]

omit [DecidableEq Φ] [∀ τ : Φ, DecidableEq (N τ)] [∀ τ : Φ, DecidableEq (n τ)] in
/-- In `y`, `branchKernel` is a semi-invariant of the upper triangular group: replacing `y` by
`borelMul Sigma.fst b y` multiplies it by the diagonal entries of `b` to the powers given by the
weights of `γ` and `κ'`. -/
private lemma branchKernel_borelMul {S : Type} [CommRing S] (b : Φ × ℕ × ℕ → S)
    (x : Sigma n × ℕ → S) (y : Sigma N × ℕ → S) :
    branchKernel ι γ κ' x (borelMul Sigma.fst b y) =
      ((diagramWeight (rankAt N) γ + diagramWeight (rankAt N) κ').prod
        fun (p : Φ × ℕ) (k : ℕ) ↦ b (p.1, p.2, p.2) ^ k) * branchKernel ι γ κ' x y := by
  -- `branchVector` is a product of two kernels, each a semi-invariant; so is its substitution.
  have h_mem : branchVector S ι γ κ' ∈
      nabla S Sigma.fst (diagramWeight (rankAt N) γ + diagramWeight (rankAt N) κ') :=
    SetLike.mul_mem_graded (weylKernel_mem_nablaFamily _) (weylKernel_mem_nablaFamily _)
  simpa only [aeval_eq_eval, branchKernel] using mem_nabla.mp (rowSubst_mem_nabla _ h_mem) S b y

omit [DecidableEq Φ] [∀ τ : Φ, DecidableEq (N τ)] in
/-- Let `y'` be the array `diag(g, s) y` and `x'` the array `gᵀ x`. The kernel at `x` and `y'` is
the kernel at `x'` and `y` times the product of the powers
`s τ ^ diagramWeight (rankAt N) γ (τ, 0)`. -/
private lemma branchKernel_blockScalar {S : Type} [CommRing S] (g : ∀ τ : Φ, Matrix (n τ) (n τ) S)
    (s : Φ → S) (x : Sigma n × ℕ → S) (y : Sigma N × ℕ → S) :
    branchKernel ι γ κ' x (fun p : Sigma N × ℕ ↦
        ∑ a : N p.1.fst, blockScalar ι g s p.1.fst p.1.snd a * y (⟨p.1.fst, a⟩, p.2)) =
      (∏ τ : Φ, s τ ^ diagramWeight (rankAt N) γ (τ, 0)) *
        branchKernel ι γ κ' (fun p : Sigma n × ℕ ↦
          ∑ a : n p.1.fst, (g p.1.fst)ᵀ p.1.snd a * x (⟨p.1.fst, a⟩, p.2)) y := by
  -- With `a` the transposed square part of `x`, that of `gᵀ x` is `a g`. Now
  -- `diag(a, 1) diag(g, s) = diag(1, s) diag(a g, 1)`, and `diag(1, s)` scales `branchVector`.
  let a (τ : Φ) : Matrix (n τ) (n τ) S := (squarePart (rowEquivFin n) x τ)ᵀ
  have h_square : (fun τ : Φ ↦ (squarePart (rowEquivFin n) (fun p : Sigma n × ℕ ↦
      ∑ b : n p.1.fst, (g p.1.fst)ᵀ p.1.snd b * x (⟨p.1.fst, b⟩, p.2)) τ)ᵀ) =
        fun τ : Φ ↦ a τ * g τ := by
    ext τ i j
    simp [a, squarePart, Matrix.mul_apply, mul_comm]
  have h_block : (fun τ : Φ ↦ blockScalar ι a 1 τ * blockScalar ι g s τ) =
      fun τ : Φ ↦ blockScalar ι 1 s τ * blockScalar ι (fun σ : Φ ↦ a σ * g σ) 1 τ := by
    funext τ
    simp [blockScalar, fromBlocks_multiply]
  rw [branchKernel, branchKernel, h_square, ← eval_rowSubst, rowSubst_rowSubst, h_block,
    ← rowSubst_rowSubst, rowSubst_branchVector, map_smul, smul_eval]

/-- Up to the factor `∏ τ, det (g τ) ^ κ' τ (rankAt n τ)`, the Schur matrix of `g` acts on
`detPowToPoly n κ₀ κ' S θ` as the substitution `x ↦ gᵀ x`. -/
private lemma detPowToPoly_smul_schur_mulVec {S : Type} [CommRing S] [IsDomain S] [CharZero S]
    (g : ∀ τ : Φ, Matrix (n τ) (n τ) S) (θ : WeylIndexFamily n κ₀ → S) :
    detPowToPoly n κ₀ κ' S ((∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • schur κ₀ g *ᵥ θ) =
      rowSubst (fun τ : Φ ↦ (g τ)ᵀ) (detPowToPoly n κ₀ κ' S θ) := by
  -- By `toPoly_schur` the Schur matrix becomes the substitution (with no power of `det`, as the
  -- ranks agree), and by `rowSubst_detPow` the substitution scales `detPow` by
  -- `∏ τ, det (g τ) ^ κ' τ (rankAt n τ)`.
  simp [detPowToPoly, toPoly_schur, rowSubst_detPow, det_transpose]

omit [∀ τ : Φ, DecidableEq (N τ)] in
/-- Let `c` times the product of the two kernels in `hη` be `toPoly n κ₀ η`, and let `y` have new
row `(t, 0, 0, …)` and block `g` on the rows `n τ`. Expanding the minors along the new row,
`branchKernel ι γ κ' x y` is a power of `t` times the product of those two kernels and of
`det ^ d`, with `d τ = κ' τ (rankAt n τ)`, all at `gᵀ x`. So `c` times it is `detPowToPoly` of
a coordinate vector: `η` moved by `g` and scaled. -/
private lemma exists_eval_detPowToPoly_eq_mul_branchKernel {c : ℤ} {η : WeylIndexFamily n κ₀ → ℤ}
    (hη : c • (weylKernel n (fun (τ : Φ) (h : ℕ) ↦ γ τ (h + 1)) (permArray fun (τ : Φ) (a : n τ) ↦
          ((finRotate (Fintype.card (n τ))).symm (rowEquivFin n τ a) : ℕ)) *
        weylKernel n κ' (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) =
      toPoly n κ₀ η)
    (y : Sigma N × ℕ → MatrixPoly (Sigma N) ℤ)
    (hy : ∀ (τ : Φ) (j : ℕ), y (⟨τ, ι τ (.inr ())⟩, j + 1) = 0) :
    ∃ θ : WeylIndexFamily n κ₀ → MatrixPoly (Sigma N) ℤ, ∀ x : Sigma n × ℕ → MatrixPoly (Sigma N) ℤ,
      eval x (detPowToPoly n κ₀ κ' (MatrixPoly (Sigma N) ℤ) θ) = c * branchKernel ι γ κ' x y := by
  let g (τ : Φ) : Matrix (n τ) (n τ) (MatrixPoly (Sigma N) ℤ) :=
    of fun a b ↦ y (⟨τ, ι τ (.inl a)⟩, rowEquivFin n τ b)
  refine ⟨(∏ τ, ∏ h ∈ range (rankAt n τ), y (⟨τ, ι τ (.inr ())⟩, 0) ^ γ τ (h + 1)) •
    (∏ τ, (g τ).det ^ κ' τ (rankAt n τ)) • schur κ₀ g *ᵥ C ∘ η, fun x ↦ ?_⟩
  rw [map_smul, detPowToPoly_smul_schur_mulVec, detPowToPoly, LinearMap.comp_apply]
  -- Expand both sides into minors. The flags `↓←` and `-finRotate_symm_apply` keep `toPoly` and
  -- `finRotate.symm` in the form that `hη` has, for `← hη`.
  simp only [transpose_of, detPow, minor, ↓← map_toPoly, ← hη, weylKernel, rowSubst_highestPoly,
    zsmul_eq_mul, map_mul, map_intCast, map_prod, map_pow, map_det, mapMatrix_apply, Matrix.map,
    of_apply, map_sum, map_X, LinearMap.mulRight_apply, mul_assoc, smul_eval, eval_rowSubst,
    mul_comm _ (x _), eval_X, branchKernel, blockScalar.eq_unfold, reindex_apply, squarePart,
    Pi.one_apply, diagonal_one, branchVector, rankAt_eq_succ ι, prod_range_succ' (_ ^ γ _ ·),
    det_fin_zero, one_pow, mul_one, prod_range_succ, prod_mul_distrib, submatrix_apply, g]
  simp only [permArray, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul,
    newRowOrder, Pi.zero_apply, Equiv.optionCongr_symm, Equiv.symm_trans, Equiv.symm_symm,
    finCongr_symm, Equiv.trans_apply, Equiv.optionCongr_apply, finCongr_apply, Fin.val_cast,
    reindex_equiv (ι _), Equiv.symm_apply_apply, sum_sum_type, univ_unique, PUnit.default_eq_unit,
    sum_singleton, Equiv.optionEquivSumPUnit_symm_inl, Option.map_some, finSuccEquiv'_symm_some,
    Fin.zero_succAbove, Fin.val_succ, fromBlocks_apply₁₁, of_apply, fromBlocks_apply₁₂,
    Matrix.zero_apply, add_zero, Equiv.optionEquivSumPUnit_symm_inr, Option.map_none,
    finSuccEquiv'_symm_none, Fin.coe_ofNat_eq_mod, Nat.zero_mod, fromBlocks_apply₂₁, sum_const_zero,
    fromBlocks_apply₂₂, one_apply_eq, zero_add, sum_ite_irrel, det_succ_row_zero,
    Nat.succ_eq_add_one, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, submatrix,
    Nat.add_right_cancel_iff, Nat.right_eq_add, mul_assoc, Fin.sum_univ_succ, pow_zero, hy,
    mul_zero, mul_pow, prod_mul_distrib, Pi.top_apply, Fin.top_eq_last, Fin.succAbove_last,
    Fin.val_castSucc, Fin.val_last]
  rw [mul_left_comm]
  -- The minors on both sides agree up to transposition and the numbering of the rows: `congr!`
  -- pairs the factors, and each pair is closed by the same call. The hypotheses are cleared because
  -- `grind` below would also read them.
  clear g hη hy
  conv_rhs => simp +singlePass [← det_transpose, -finRotate_symm_apply]
  congr! <;> simp +instances (disch := grind) [ite_eq_right, ← Fin.eq_mk_iff_val_eq,
    Nat.mod_eq_of_lt, Fin.add_def, -finRotate_symm_apply, ← Equiv.eq_symm_apply,
    Function.swap]

/-- Let `c • (weylKernel n γ₁ P₁ * weylKernel n κ' P) = toPoly n κ₀ η` for an integer `c` and an
integer vector `η`, where `γ₁ τ h = γ τ (h + 1)`, `P` is the permutation array of the row order
`rowEquivFin` and `P₁` that of `rowEquivFin` shifted cyclically by one. (`New.weylKernel` is the
product of the leading minors to the powers given by the weight; `New.toPoly n κ₀` sends a
coordinate vector to its polynomial.) Then there is an integral matrix `B` with two properties. (a)
Applied on the right to `weylGramOver *ᵥ weylEval n κ₀ P`, the coordinates of `weylKernel n κ₀ P`,
it gives a vector ξ whose polynomial `nablaCombination (γ + κ')` ξ = Σ ξ_i b_i (b_i the basis minor
products) is `c • branchVector ℂ ι γ κ'`; the latter is the product of leading h×h minors to the
powers γ τ h with the added row first and κ' τ h with it last. (b) Over every field of
characteristic zero, `B * schur (γ + κ') (diag(g, s)) = χ • (schur κ₀ g * B)` with `χ = ∏ τ, s τ ^
diagramWeight (rankAt N) γ (τ, 0) * det (g τ) ^ κ' τ (rankAt n τ)`. Here `schur` is the Schur matrix
on the Weyl module and `diag(g, s)` is `blockScalar ι g s`. -/
lemma exists_int_branching_of_weylKernel {c : ℤ} {η : WeylIndexFamily n κ₀ → ℤ}
    (hη : c • (weylKernel n (fun (τ : Φ) (h : ℕ) ↦ γ τ (h + 1)) (permArray fun (τ : Φ) (a : n τ) ↦
          ((finRotate (Fintype.card (n τ))).symm (rowEquivFin n τ a) : ℕ)) *
        weylKernel n κ' (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) =
      toPoly n κ₀ η) :
    ∃ B : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) ℤ,
      -- (a)
      nablaCombination (γ + κ') ((weylGramOver *ᵥ weylEval n κ₀
          (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) ᵥ*
            B.map (Int.cast : ℤ → ℂ)) =
        (c : ℂ) • branchVector ℂ ι γ κ' ∧
      -- (b)
      ∀ (R : Type) [Field R] [CharZero R] (g : (τ : Φ) → Matrix (n τ) (n τ) R) (s : Φ → R),
        B.map (Int.cast : ℤ → R) * schur (γ + κ') (blockScalar ι g s) =
          (∏ τ : Φ, s τ ^ diagramWeight (rankAt N) γ (τ, 0) * (g τ).det ^ κ' τ (rankAt n τ)) •
            (schur κ₀ g * B.map (Int.cast : ℤ → R)) := by
  -- Say that `θ` represents `m` times the kernel at `y` if `detPowToPoly n κ₀ κ' S θ` has the
  -- values `m * branchKernel ι γ κ' x y`. We move `η` to the generic point, read off `B` from the
  -- coefficients of the kernel, and get both claims from one fact: `B ev_y` represents `c` times
  -- the kernel at `y`.
  -- Column operations on the generic point `X`, with `X₀ τ` and `X_j τ` its entries in the new row
  -- and columns `0` and `j`: column `0` is multiplied by `X₀ τ`, and column `j > 0` becomes
  -- `X₀ τ * column j - X_j τ * column 0`. They clear the new row beyond its first entry and
  -- multiply the kernel by a monomial `y ^ μ`.
  let β : Φ × ℕ × ℕ → MatrixPoly (Sigma N) ℤ := fun (τ, i, j) ↦
    (if i = j then 1 else if i = 0 then -1 else 0) * X (⟨τ, ι τ (.inr ())⟩, j - i)
  have h_new_row (τ : Φ) (j : ℕ) : borelMul Sigma.fst β X (⟨τ, ι τ (.inr ())⟩, j + 1) = 0 := by
    simp only [borelMul, ite_mul, one_mul, neg_mul, zero_mul, mul_ite, mul_neg, mul_comm,
      sum_range_succ', Nat.add_right_cancel_iff, Nat.reduceSubDiff, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, ↓reduceIte, Finset.sum_ite_eq', Finset.mem_range,
      lt_add_iff_pos_right, Order.lt_one_iff, tsub_self, Nat.right_eq_add, tsub_zero,
      add_neg_cancel, β]
  obtain ⟨θ, μ, hθ⟩ : ∃ (θ : WeylIndexFamily n κ₀ → MatrixPoly (Sigma N) ℤ) (μ : Sigma N × ℕ →₀ ℕ),
      ∀ x : Sigma n × ℕ → MatrixPoly (Sigma N) ℤ,
        eval x (detPowToPoly n κ₀ κ' (MatrixPoly (Sigma N) ℤ) θ) =
          monomial μ 1 * (branchKernel ι γ κ' x X * (c : MatrixPoly (Sigma N) ℤ)) := by
    obtain ⟨θ, hθ⟩ := exists_eval_detPowToPoly_eq_mul_branchKernel ι hη _ h_new_row
    -- `μ` is the exponent of the monomial that `branchKernel_borelMul` gives for `β`; it is found
    -- by unification in the `simpa`, so it is left as a hole.
    exact ⟨θ, _, by simpa only [ite_mul, one_mul, neg_mul, zero_mul, branchKernel_borelMul,
      Finsupp.prod, ↓reduceIte, tsub_self, Finsupp.coe_add, Pi.add_apply, X_pow_eq_monomial,
      Finsupp.single_add, ← monomial_sum_one, sum_add_distrib, Int.cast_comm, mul_assoc,
      β] using hθ⟩
  -- `c` times the kernel at generic `x` and `y` is a polynomial in `y` over `ℤ[x]`. As a
  -- semi-invariant it is a combination of the basis `nablaBasis`, with coordinates `f`. The weight
  -- is written with the zero sum that `nabla_le_span_nablaBasis_mul_detPow 0` expects.
  have h_semi : c • branchKernel ι γ κ' (C ∘ (X : Sigma n × ℕ → MatrixPoly (Sigma n) ℤ)) X ∈
      nabla (MatrixPoly (Sigma n) ℤ) Sigma.fst (diagramWeight (rankAt N) (γ + κ') +
        ∑ τ : Φ, (0 : Φ → ℕ) τ • ∑ i ∈ range (rankAt N τ), Finsupp.single (τ, i) 1) := by
    simp only [diagramWeight_add, Pi.zero_apply, zero_nsmul, sum_const_zero, add_zero, zsmul_eq_mul,
      mem_nabla, aeval_def, eval₂_mul, ← coe_eval₂Hom, map_intCast, map_branchKernel,
      Function.comp_apply, eval₂Hom_C, eval₂Hom_X', branchKernel_borelMul, mul_left_comm,
      implies_true]
  obtain ⟨f, hf⟩ := LinearMap.mem_range.mp (nabla_le_span_nablaBasis_mul_detPow 0 h_semi)
  -- Compare the coefficients of `y ^ (μ + δ)` in `hθ`: the coefficient of `y ^ δ` in that
  -- polynomial lies in the range of `detPowToPoly n κ₀ κ' ℤ`. By `coord_mem_of_coeff_mem` so do the
  -- coordinates `f j`; their preimages `B j` are the columns of the matrix.
  have h_coeff (δ : Sigma N × ℕ →₀ ℕ) :
      (c • branchKernel ι γ κ' (C ∘ (X : Sigma n × ℕ → MatrixPoly (Sigma n) ℤ)) X).coeff δ ∈
        (detPowToPoly n κ₀ κ' ℤ).range.toAddSubgroup := by
    refine ⟨fun i ↦ (θ i).coeff (μ + δ), MvPolynomial.funext fun x ↦ ?_⟩
    have h_shift : (eval (C ∘ x) (detPowToPoly n κ₀ κ' (MatrixPoly (Sigma N) ℤ) θ)).coeff (μ + δ) =
        (branchKernel ι γ κ' (fun p : Sigma n × ℕ ↦ (x p : MatrixPoly (Sigma N) ℤ)) X *
          (c : MatrixPoly (Sigma N) ℤ)).coeff δ := by
      rw [hθ, coeff_monomial_mul, one_mul]
      -- On `ℤ` the map `C` is the cast by definition.
      rfl
    simpa only [detPowToPoly, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
      map_mul, eval_toPoly, dotProduct, weylEval, mulVec, map_apply, Int.cast_eq,
      mul_comm (eval x _), AddMonoidAlgebra.coeff_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eval,
      ← coeff_map, map_branchKernel, map_C, eval_X, eq_intCast, map_X, ← map_detPow C,
      ← map_nablaBasis C, eval_map, ← eval₂_comp, ← zsmul_eq_mul, ← Int.cast_comm,
      AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply, Int.zsmul_eq_mul]
      using h_shift
  have h_coord : ∀ j : WeylIndexFamily N (γ + κ'), ∃ b : WeylIndexFamily n κ₀ → ℤ,
      detPowToPoly n κ₀ κ' ℤ b = f j :=
    coord_mem_of_coeff_mem _ _ hf h_coeff
  choose B hB using h_coord
  -- Specialise `hf` at points `x` and `y` over any ring.
  have hB_kernel {T : Type} [CommRing T] (y : Sigma N × ℕ → T) (x : Sigma n × ℕ → T) :
      eval x (detPowToPoly n κ₀ κ' T ((of B)ᵀ.map (↑) *ᵥ weylEval N (γ + κ') y)) =
        c * branchKernel ι γ κ' x y := by
    simpa only [detPowToPoly, transpose_of, mulVec_eq_sum, weylEval, op_smul_eq_smul, map_sum,
      map_smul, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply, smul_eq_C_mul,
      map_mul, eval_C, eval_toPoly, dotProduct, transpose_apply, map_apply, of_apply,
      MulOpposite.op_intCast, Finset.sum_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_intCast, mul_comm (eval y _), AlgHom.toRingHom_eq_coe, detPow_zero, mul_one,
      linearCombination_apply, ← hB, C_mul, ← eval_map, map_C, coe_coe, aeval_def,
      algebraMap_int_eq, map_toPoly, Int.coe_castRingHom, map_intCast, map_detPow, map_nablaBasis,
      zsmul_eq_mul, map_branchKernel, map_X, eval_X] using congrArg (eval₂ (aeval x).toRingHom y) hf
  refine ⟨(of B)ᵀ, MvPolynomial.funext fun y ↦ ?_, ?_⟩
  · -- For `x` the identity matrix, `det x = 1` and the kernel is `branchVector` evaluated at `y`.
    simpa only [transpose_of, map.eq_1 (of _), of_apply, vecMul_mulVec, ← transpose_map,
      weylGram_isSymm.eq, linearCombination_apply, map_sum, smul_eval, ← weylEval.eq_1,
      ← dotProduct.eq_1, detPowToPoly, detPow, minor, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulRight_apply, map_mul, eval_toPoly, mulVec_mulVec, dotProduct_mulVec, map_prod,
      map_pow, map_det, mapMatrix_apply, eval_X, permArray, Equiv.apply_symm_apply, Fin.val_inj,
      ← diagonal.eq_1, diagonal_one, det_one, one_pow, prod_const_one, mul_one, branchKernel,
      blockScalar.eq_unfold, reindex_apply, squarePart, EmbeddingLike.apply_eq_iff_eq,
      transpose_one, Pi.one_apply, fromBlocks_one, submatrix_one_equiv, rowSubst_one]
      using hB_kernel y (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))
  intro S _ _ g s
  -- It suffices to compare the two sides on the vectors `ev_y`, and there after applying
  -- `detPowToPoly n κ₀ κ' S`, which is injective because the product of the powers
  -- `det ^ κ' τ (rankAt n τ)` is not a zero divisor.
  refine toLin'.injective (ext_weylEval 0 (fun y _ _ ↦ ?_) Set.infinite_univ)
  refine toPoly_injective
    ((isRegular_detPow (R := S) (n := n) (e := fun τ : Φ ↦ κ' τ (rankAt n τ))).right ?_)
  change detPowToPoly n κ₀ κ' S _ = detPowToPoly n κ₀ κ' S _
  refine MvPolynomial.funext fun x ↦ ?_
  -- By `hB_kernel` the left side is `c` times the kernel at `x` and `diag(g, s) y`, and the right
  -- side is a power of `s` times `c` times the kernel at `gᵀ x` and `y`.
  simp only [toLin'_mul, LinearMap.coe_comp, Function.comp_apply, toLin'_apply, FitsRanks.refl,
    schurDetExp_self, schur_mulVec_weylEval_of_schurDetExp_eq_zero, hB_kernel,
    branchKernel_blockScalar ι g s x y, transpose_apply, prod_mul_distrib, mul_smul, map_smul,
    LinearMap.smul_apply, detPowToPoly_smul_schur_mulVec g, smul_eval, eval_rowSubst,
    mul_left_comm]

/-- Let `v` be the Gram matrix `weylGramOver` times the evaluation vector at the permutation array
of `rowEquivFin`. Let `B` be an integral matrix such that `nablaCombination` (ξ ↦ Σ ξ_i b_i over the
basis products of minors) sends the row vector `v ᵥ* B` to `c • branchVector ℂ ι γ κ'` with `c ≠ 0`.
Here `branchVector` is the product of the leading minors to the powers `γ`, with the added row
first, and of those to the powers `κ'`, with the added row last. Let `B` also be equivariant over
`ℂ`: `B * schur (γ + κ') (diag(g, 1)) = (∏ τ, det (g τ) ^ κ' τ (rankAt n τ)) • (schur κ₀ g * B)`
for all `g`, where `diag(g, 1)` is `blockScalar ι g 1`. If `e₀ τ = e τ + κ' τ (rankAt n τ)`, then
every complex matrix intertwining weights `(γ + κ', e)` and `(κ₀, e₀)` on the unitary points of the
block group is a multiple of `B` (`New.SpansBranchingMaps`). -/
lemma spansBranchingMaps_of_equivariant {c : ℤ} (hc : c ≠ 0) {e e₀ : Φ → ℤ}
    (he₀ : ∀ τ : Φ, e₀ τ = e τ + κ' τ (rankAt n τ))
    {B : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) ℤ}
    (B_top : nablaCombination (γ + κ') ((weylGramOver *ᵥ weylEval n κ₀
        (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) ᵥ*
          B.map (Int.cast : ℤ → ℂ)) =
      (c : ℂ) • branchVector ℂ ι γ κ')
    (B_block : ∀ g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ,
      B.map (Int.cast : ℤ → ℂ) * schur (γ + κ') (blockScalar ι g 1) =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * B.map (Int.cast : ℤ → ℂ))) :
    SpansBranchingMaps ι e₀ e (B.map (Int.cast : ℤ → ℂ)) := by
  -- `D g T` is the defect of equivariance of `T` at `g`. An equivariant `T` is determined by the
  -- number `x ᵥ* T ⬝ᵥ v`, with `x` the coordinates of `weylKernel n κ₀ (permArray (rowEquivFin n))`
  -- in the basis `nablaBasis` and `v` the cyclic vector.
  intro T hT
  set G₀ : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily n κ₀) ℂ := weylGramOver
  set x : WeylIndexFamily n κ₀ → ℂ :=
    G₀ *ᵥ weylEval n κ₀ (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))
  let d (g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) : ℂ := ∏ τ, (g τ).det ^ κ' τ (rankAt n τ)
  obtain ⟨v, v_cyclic⟩ : ∃ v : WeylIndexFamily N (γ + κ') → ℂ, ∀ r : WeylIndexFamily N (γ + κ') → ℂ,
      (∀ g : (τ : Φ) → Matrix (n τ) (n τ) ℂ, (∀ τ : Φ, (g τ)ᵀ.BlockTriangular (rowEquivFin n τ)) →
        r ⬝ᵥ schur (γ + κ') (blockScalar ι g 1) *ᵥ v = 0) →
      r = 0 :=
    exists_cyclic_lower_triangular ι (γ + κ')
  let D {R : Type} [CommRing R] (g : (τ : Φ) → Matrix (n τ) (n τ) R) :
      Module.End R (Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) R) :=
    mulRightLinearMap _ R (schur (γ + κ') (blockScalar (R := R) ι g 1)) -
      (∏ τ, (g τ).det ^ κ' τ (rankAt n τ)) • mulLeftLinearMap _ R (schur κ₀ g)
  have eq_zero (T' : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) ℂ)
      (hT' : ∀ g : (τ : Φ) → Matrix (n τ) (n τ) ℂ, D g T' = 0) (h_value_zero : x ᵥ* T' ⬝ᵥ v = 0) :
      T' = 0 := by
    have h_row (g : (τ : Φ) → Matrix (n τ) (n τ) ℂ) :
        x ᵥ* T' ᵥ* schur (γ + κ') (blockScalar ι g 1) = d g • x ᵥ* schur κ₀ g ᵥ* T' := by
      simpa only [D, d, vecMul_vecMul, Pi.add_apply, LinearMap.sub_apply, mulRightLinearMap_apply,
        LinearMap.smul_apply, mulLeftLinearMap_apply, vecMul_sub, vecMul_smul, vecMul_zero,
        sub_eq_zero] using congrArg (x ᵥ* ·) (hT' g)
    -- `x` is an eigenvector of the lower triangular group, under which `v` is cyclic.
    have x_mul_T : x ᵥ* T' = 0 := by
      refine v_cyclic _ fun g hg ↦ ?_
      -- The eigenvalue is the scalar of `rowSubst_weylKernel_permArray`; it is found by
      -- unification, so it is left as a hole.
      obtain ⟨a, ha⟩ : ∃ a : ℂ, x ᵥ* schur κ₀ g = a • x :=
        ⟨_, by simpa [vecMul_schur_eq_iff, x, G₀, nablaCombination_weylGramOver_mulVec] using
          rowSubst_weylKernel_permArray _ _ hg⟩
      simp only [dotProduct_mulVec, h_row, ha, smul_vecMul, smul_dotProduct, h_value_zero,
        smul_eq_mul, mul_zero]
    -- By `h_row`, `T'` kills all `x ᵥ* schur κ₀ g` with `g` invertible, and these span.
    have T_mul_gram : T'ᵀ * G₀ = 0 := by
      refine toLin'.injective (ext_schur_weylEval (rowEquivFin n) fun g ↦ ?_)
      simpa only [d, G₀, toLin'_mul, LinearMap.coe_comp, Function.comp_apply, toLin'_apply,
        mulVec_mulVec _ weylGramOver, weylGramOver_mul_schur, ← mulVec_mulVec, mulVec_transpose,
        vecMul_vecMul, map_zero, LinearMap.zero_apply, det_transpose, x_mul_T, zero_vecMul,
        isUnit_iff_ne_zero, ne_eq, prod_eq_zero_iff, mem_univ, pow_eq_zero_iff',
        GeneralLinearGroup.det_ne_zero, false_and, and_false, exists_false, not_false_eq_true,
        IsUnit.smul_eq_zero] using (h_row fun τ ↦ (g τ).valᵀ).symm
    have G₀_invertible : Invertible G₀ := weylGramOver_posDef.isUnit.invertible (a := G₀)
    simpa using congrArg (fun M ↦ M * ⅟G₀) T_mul_gram
  -- `T` is equivariant for unitary `g`, hence for all `g` by Zariski density: an entry of the
  -- defect is a polynomial in `g`, and at a unitary `g` the factor `det ^ e` cancels from `hT`.
  have T_equiv (g : (τ : Φ) → Matrix (n τ) (n τ) ℂ) : D g T = 0 := by
    ext i j
    have h_eval (z : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) :
        evalMatrix z (D (genericMatrixAt ℂ n) (T.map C) i j) = D z T i j := by
      simp only [Pi.add_apply, blockScalar.eq_unfold, reindex_apply, Pi.one_apply, diagonal_one,
        LinearMap.sub_apply, mulRightLinearMap_apply, LinearMap.smul_apply, mulLeftLinearMap_apply,
        Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_matrix_mul, Matrix.map_map,
        Function.comp_def, eval_C, map_id', FitsRanks.refl, ← schur_map, ← submatrix_map,
        fromBlocks_map, genericMatrixAt_map_evalMatrix, map_zero, Matrix.map_zero, map_one,
        Matrix.map_one, map_mul, map_prod, map_pow, map_det, mapMatrix_apply, D]
    have h_unitary (z : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) (hz : ∀ τ : Φ, (z τ)ᴴ * z τ = 1) :
        D z T i j = 0 := by
      obtain ⟨y, hy, h_equiv⟩ := hT (fun τ ↦ ⟨z τ, (z τ)ᴴ, mul_eq_one_symm (hz τ), hz τ⟩) hz
      simpa only [D, Pi.add_apply, blockScalar.eq_unfold, reindex_apply, Pi.one_apply, diagonal_one,
        LinearMap.sub_apply, mulRightLinearMap_apply, LinearMap.smul_apply, mulLeftLinearMap_apply,
        Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_eq_zero, weylRep, Units.smul_def,
        Units.coe_prod, Units.val_zpow_eq_zpow_val, GeneralLinearGroup.val_det_apply,
        MonoidHom.coe_mk, OneHom.coe_mk, hy, det_submatrix_equiv_self, det_fromBlocks_one₂₂,
        Matrix.mul_zero, sub_zero, Matrix.mul_smul, he₀, _root_.zpow_add, zpow_natCast,
        prod_mul_distrib, Units.val_mul, Units.val_pow_eq_pow_val, smul_mul, mul_assoc,
        mul_eq_mul_left_iff, prod_eq_zero_iff, mem_univ, ne_eq, det_ne_zero_of_left_inverse (hz _),
        not_false_eq_true, zpow_ne_zero, and_false, exists_false, or_false]
        using congrFun₂ h_equiv i j
    rw [← h_eval]
    exact zariski_dense_unitary g _ fun z hz ↦ (h_eval z).trans (h_unitary z hz)
  have B_defect (g : (τ : Φ) → Matrix (n τ) (n τ) ℂ) : D g (B.map (Int.cast : ℤ → ℂ)) = 0 :=
    sub_eq_zero.mpr (B_block g)
  -- `B ≠ 0` because `c • branchVector ℂ ι γ κ' ≠ 0`, so `x ᵥ* B ⬝ᵥ v ≠ 0`.
  have h_kernel_ne (κ : Φ → ℕ → ℕ) (e : ∀ τ : Φ, N τ ≃ Fin (rankAt N τ)) :
      weylKernel (R := ℂ) N κ (permArray fun (τ : Φ) (a : N τ) ↦ (e τ a : ℕ)) ≠ 0 :=
    ne_zero_of_map (ne_zero_of_eq_one (eval_weylKernel_permArray e))
  have value_ne : x ᵥ* B.map (↑) ⬝ᵥ v ≠ 0 := by
    intro h
    simpa [eq_zero _ B_defect h, branchVector, hc, h_kernel_ne] using B_top.symm
  -- `T - a • B` is equivariant and `x ᵥ* (T - a • B) ⬝ᵥ v = 0`, so it is zero.
  set a : ℂ := x ᵥ* T ⬝ᵥ v / x ᵥ* B.map (↑) ⬝ᵥ v with ha
  refine ⟨a, sub_eq_zero.mp (eq_zero _ (fun g ↦ ?_) ?_)⟩
  · show D g (T - a • B.map Int.cast) = 0
    simp [T_equiv, B_defect]
  · show x ᵥ* (T - a • B.map Int.cast) ⬝ᵥ v = 0
    simp [ha, value_ne, vecMul_sub, vecMul_smul]

/-- Branching from `GL (n + 1)` to `GL n`. Write `κ = γ + κ'`: of the `κ τ h` columns of height `h`,
`γ τ h` lose a box and `κ' τ h` keep theirs, and `κ₀ τ h = κ' τ h + γ τ (h + 1)` for
`0 < h < rankAt n τ`. Columns of height `rankAt n τ` that keep their box become powers of `det`:
`e₀ τ = e τ + κ' τ (rankAt n τ)`. Let all columns of height below `q` lose a box. Write
`ρ = weylRep κ e` and `ρ₀ = weylRep κ₀ e₀`. Then some integral matrix `br` has three properties. (a)
Over every field of characteristic zero, `br ρ(diag(g, s)) = (∏ τ, s τ ^ (diagramWeight (rankAt N) γ
(τ, 0) + e τ)) ρ₀(g) br`. (b) Its operator norm for the Gram norms is at most `L ^ (3 L)` if `L`
bounds the number of boxes of `κ₀` in columns of height `h` with `q ≤ h < rankAt n τ`; the bound is
stated for squared norms. (c) It spans the maps over `ℂ` that are equivariant for the unitary block
group.

Part of the multiplicity-one branching rule from GL (n + 1) to GL n: for a given interlacing pair,
an integral equivariant matrix exists and the multiplicity is at most one. -/
lemma _root_.New.exists_branching_matrix (κ₀ : Φ → ℕ → ℕ) (q : ℕ) (e e₀ : Φ → ℤ) (hκ : γ + κ' = κ)
    (hκ₀ : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = κ' τ h + γ τ (h + 1))
    (hq : ∀ τ : Φ, ∀ i < q, κ' τ i = 0) (he₀ : ∀ τ : Φ, e₀ τ = e τ + κ' τ (rankAt n τ)) :
    ∃ br : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N κ) ℤ,
      -- (a)
      (∀ (R : Type) [Field R] [CharZero R] (g : (τ : Φ) → GL (n τ) R) (s : Φ → Rˣ)
        (x : (τ : Φ) → GL (N τ) R),
        (∀ τ : Φ, (x τ).val = blockScalar ι (fun τ : Φ ↦ (g τ).val) (fun τ : Φ ↦ (s τ).val) τ) →
        br.map (Int.cast : ℤ → R) * weylRep κ e x =
          (∏ τ : Φ, s τ ^ (diagramWeight (rankAt N) γ (τ, 0) + e τ)) •
            (weylRep κ₀ e₀ g * br.map (Int.cast : ℤ → R))) ∧
      -- (b)
      (∀ L : ℕ, ∑ τ : Φ, ∑ h ∈ Ico q (rankAt n τ), h * κ₀ τ h ≤ L →
        ∀ ξ : WeylIndexFamily N κ → ℂ,
          weylNormSq (br.map (Int.cast : ℤ → ℂ) *ᵥ ξ) ≤ ((L ^ L) ^ 3) ^ 2 * weylNormSq ξ) ∧
      -- (c)
      SpansBranchingMaps ι e₀ e (br.map (Int.cast : ℤ → ℂ)) := by
  -- The matrix is the `B` of `exists_int_branching_of_weylKernel`, for the vector `η` and the
  -- denominator `0 < c ≤ L ^ (3 L)` of `exists_smul_weylKernel_mul_eq_toPoly`.
  subst hκ
  obtain ⟨c, c_pos, c_le, η, hη⟩ :=
    exists_smul_weylKernel_mul_eq_toPoly (n := n) (γ := fun (τ : Φ) (h : ℕ) ↦ γ τ (h + 1)) hq hκ₀
  obtain ⟨B, B_top, B_equiv⟩ := exists_int_branching_of_weylKernel ι hη
  -- Equivariance over `ℂ` for `diag(g, 1)`.
  have B_block (g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) :
      B.map (Int.cast : ℤ → ℂ) * schur (γ + κ') (blockScalar ι g 1) =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * B.map (Int.cast : ℤ → ℂ)) := by
    simpa using B_equiv ℂ g 1
  refine ⟨B, fun R _ _ g s x hx ↦ ?_, fun L hL ξ ↦ ?_,
    spansBranchingMaps_of_equivariant ι c_pos.ne' he₀ B_top B_block⟩
  · -- Multiply `B_equiv` by the powers of the determinants, with `det (x τ) = det (g τ) * s τ`.
    have h_schur : B.map (Int.cast : ℤ → R) * schur (γ + κ') (fun τ : Φ ↦ (x τ).val) =
        (∏ τ : Φ, (s τ).val ^ diagramWeight (rankAt N) γ (τ, 0) *
            (g τ).val.det ^ κ' τ (rankAt n τ)) •
          (schur κ₀ (fun τ : Φ ↦ (g τ).val) * B.map (Int.cast : ℤ → R)) := by
      rw [funext hx]
      exact B_equiv R (fun τ : Φ ↦ (g τ).val) fun τ : Φ ↦ (s τ).val
    have h_det (τ : Φ) : (x τ).val.det = (g τ).val.det * (s τ).val := by
      simp [hx τ, blockScalar]
    simp [weylRep, h_schur, h_det, he₀, Units.smul_def, mul_zpow, _root_.zpow_add, smul_smul,
      prod_mul_distrib, mul_assoc, mul_left_comm]
  · have hc_le : (c : ℝ) ≤ ((L : ℝ) ^ L) ^ 3 := by exact_mod_cast c_le L hL
    calc weylNormSq (B.map (Int.cast : ℤ → ℂ) *ᵥ ξ)
      _ ≤ (c : ℝ) ^ 2 * weylNormSq ξ := weylNormSq_mulVec_le_of_equivariant ι B_top B_block ξ
      _ ≤ (((L : ℝ) ^ L) ^ 3) ^ 2 * weylNormSq ξ := by
        gcongr
        exact weylNormSq_nonneg ξ

end New.GL

end Branching

end
