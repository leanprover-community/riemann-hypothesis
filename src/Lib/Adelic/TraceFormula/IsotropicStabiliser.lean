module

public import Lib.Adelic.Reduction.FirstMinimumShortBases
import TauCeti.LinearAlgebra.Matrix.Charpoly.Inverse
import Lib.General.LinearAlgebra.MatrixPolynomials

/-!
# The stabiliser of an isotropic subspace

Let `J` be a nondegenerate hermitian form and `A` an isotropic subspace, spanned by the columns of
a matrix `X`. An isometry that keeps `A ≠ 0` has a reducible characteristic polynomial. If an
isometry keeps `A`, its characteristic polynomial does not change under left multiplication by the
unipotent radical of the stabiliser of `A`.

Notions from other files:
* `U J` is the unitary group of `J`: the invertible matrices `g` with `gᴴ * J * g = J`.
* `dilationGroup X` consists of the pairs `(g, c)` of an isometry and a unit such that
  `g * X = c • X` and `g` is the identity on `A^⊥` modulo its radical. Its members with `c = 1`
  form the unipotent radical.
-/

@[expose] public section

open Matrix Polynomial

namespace New

variable {E n : Type} [Field E] [Fintype n] [DecidableEq n]

/-- If `γ * A = A * r` and `s * A = 0`, then `γ + A * s` has the characteristic polynomial of
`γ`. In words: `γ` keeps the span of the columns of `A`, and the added matrix has values in this
span and maps it to `0`. -/
lemma charpoly_add_mul_of_mul_eq_zero {γ A r s : Matrix n n E} (h_keeps : γ * A = A * r)
    (h_zero : s * A = 0) : (γ + A * s).charpoly = γ.charpoly := by
  -- The two products of the same two block matrices are block triangular, with the diagonal
  -- blocks `r`, `γ + A * s` and `r`, `γ`.
  apply mul_left_cancel₀ r.charpoly_monic.ne_zero
  rw [← charpoly_fromBlocks_zero₂₁ r s, ← charpoly_fromBlocks_zero₂₁ r s]
  simpa [fromBlocks_multiply, add_comm, h_keeps, h_zero] using
    charpoly_mul_comm (fromBlocks 1 0 A 1) (fromBlocks r s (-(A * r)) γ)

/-- An invertible matrix `γ` with `γ * X = X * r`, where `X ≠ 0` and `r` is singular, has a
reducible characteristic polynomial. -/
lemma not_irreducible_charpoly_of_mul_eq_mul {γ X r : Matrix n n E} (hγ : γ.det ≠ 0) (hX : X ≠ 0)
    (h_keeps : γ * X = X * r) (hr : r.det = 0) : ¬Irreducible γ.charpoly := by
  intro h_irred
  -- The polynomial of `r`, taken at `γ`, kills `X`. So it has a common factor with the
  -- polynomial of `γ`, hence equals it, and then `γ` is singular.
  have h_dvd : γ.charpoly ∣ r.charpoly := by_contra fun h ↦
    hX ((isUnit_aeval_iff_isCoprime.2 (h_irred.coprime_iff_not_dvd.2 h)).mul_right_eq_zero.1
      (by rw [← aeval_semiconj h_keeps.symm, aeval_self_charpoly, mul_zero]))
  have h_eq := eq_of_monic_of_dvd_of_natDegree_le γ.charpoly_monic r.charpoly_monic h_dvd (by simp)
  exact hγ (by rw [det_eq_sign_charpoly_coeff, ← h_eq, ← det_eq_sign_charpoly_coeff, hr])

variable [StarRing E]

/-- The stabiliser in the unitary group `U J` of the span of the columns of `X`: the isometries
`γ` of `J` with `γ * X = X * r` for some matrix `r`. -/
def spanStabilizer (J X : Matrix n n E) : Subgroup (U J) where
  carrier := {γ : U J | ∃ r : Matrix n n E, γ * X = X * r}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := fun ⟨r, hr⟩ ⟨t, ht⟩ ↦
    ⟨r * t, by rw [Subgroup.coe_mul, Units.val_mul, mul_assoc, ht, ← mul_assoc, hr, mul_assoc]⟩
  inv_mem' {γ} hγ := by
    -- The matrices `M` with `M * X = X * r` for some `r` form a subalgebra,
    -- which contains the inverses of its invertible elements.
    let S : Subalgebra E (Matrix n n E) :=
      { carrier := {M | ∃ r, M * X = X * r}
        mul_mem' := fun ⟨r, hr⟩ ⟨t, ht⟩ ↦ ⟨r * t, by rw [mul_assoc, ht, ← mul_assoc, hr, mul_assoc]⟩
        add_mem' := fun ⟨r, hr⟩ ⟨t, ht⟩ ↦ ⟨r + t, by rw [add_mul, hr, ht, mul_add]⟩
        algebraMap_mem' c := ⟨algebraMap E _ c, by simp [Algebra.algebraMap_eq_smul_one]⟩ }
    simpa [S, Subgroup.coe_inv, ← Matrix.inv_eq_left_inv γ.val.inv_mul] using
      nonsing_inv_mem (S := S) hγ

variable {J X Y : Matrix n n E}

omit [DecidableEq n] in
/-- Orthogonality for a hermitian matrix `J` is symmetric: `vᴴ J w = 0` implies `wᴴ J v = 0`. -/
lemma gram_eq_zero_symm (hJ : J.IsHermitian) {v w : Matrix n n E}
    (hvw : vᴴ * (J * w) = 0) : wᴴ * (J * v) = 0 := by
  simpa [hJ.eq, mul_assoc] using congrArg conjTranspose hvw

lemma mem_spanStabilizer {γ : U J} :
    γ ∈ spanStabilizer J X ↔ ∃ r : Matrix n n E, γ * X = X * r := .rfl

/-- If `(ν, 1)` lies in the dilation group of `X`, whose members `(g, c)` satisfy `g * X = c • X`,
then `ν` fixes the columns of `X`. -/
lemma mul_eq_self_of_mem_dilationGroup {ν : U J} (hν : (ν, 1) ∈ dilationGroup X) :
    ν * X = X := by
  simpa using hν.1

/-- If `(ν, 1)` lies in the dilation group of `X`, whose members act as the identity on the
orthogonal of `X` modulo its radical, then `wᴴ J (ν v) = wᴴ J v` for all `v` and `w` orthogonal to
the columns of `X`. -/
lemma gram_mul_eq_of_mem_dilationGroup {ν : U J} (hν : (ν, 1) ∈ dilationGroup X)
    {v w : Matrix n n E} (hv : Xᴴ * (J * v) = 0) (hw : Xᴴ * (J * w) = 0) :
    wᴴ * (J * (ν * v)) = wᴴ * (J * v) :=
  hν.2 v w hv hw

/-- An isometry `ν` with `(ν, 1)` in the dilation group of `X` fixes the columns of `X`, so it lies
in the stabiliser of their span. -/
lemma mem_spanStabilizer_of_mem_dilationGroup {ν : U J} (hν : (ν, 1) ∈ dilationGroup X) :
    ν ∈ spanStabilizer J X :=
  mem_spanStabilizer.2 ⟨1, by rw [mul_eq_self_of_mem_dilationGroup hν, mul_one]⟩

/-- For a nondegenerate hermitian form `J`, the columns of `X` span an isotropic subspace `A` and
the columns of `Y` span its orthogonal `A^⊥`. -/
structure IsIsotropicFrame (J X Y : Matrix n n E) : Prop where
  /-- The form is hermitian. -/
  isHermitian : J.IsHermitian
  /-- The form is nondegenerate. -/
  isUnit : IsUnit J
  /-- The subspace `A` is isotropic. -/
  isotropic : Xᴴ * (J * X) = 0
  /-- The columns of `Y` lie in `A^⊥`. -/
  orthogonal : Xᴴ * (J * Y) = 0
  /-- There are matrices `e` and `b` with `Y * e + b * (Xᴴ * J) = 1`. So every `v` in `A^⊥` is
  `Y * (e * v)`, that is, the columns of `Y` span `A^⊥`. -/
  spans : ∃ e b : Matrix n n E, Y * e + b * (Xᴴ * J) = 1

namespace IsIsotropicFrame

/-- In an isotropic frame `(J, X, Y)`, every vector orthogonal to the columns of `X` is a
combination of those of `Y`, with coefficients given by one matrix `e`: `Xᴴ J v = 0` implies
`Y * (e * v) = v`. -/
lemma exists_mul_mul_eq_of_orthogonal_left (h : IsIsotropicFrame J X Y) :
    ∃ e : Matrix n n E, ∀ v : Matrix n n E, Xᴴ * (J * v) = 0 → Y * (e * v) = v := by
  obtain ⟨e, b, h_one⟩ := h.spans
  exact ⟨e, fun v hv ↦ by simpa [add_mul, mul_assoc, hv] using congrArg (· * v) h_one⟩

/-- In an isotropic frame `(J, X, Y)`, every vector orthogonal to the columns of `Y` is a
combination of those of `X`, with coefficients given by one matrix `c`: `Yᴴ J v = 0` implies
`X * (c * v) = v`. -/
lemma exists_mul_mul_eq_of_orthogonal_right (h : IsIsotropicFrame J X Y) :
    ∃ c : Matrix n n E, ∀ v : Matrix n n E, Yᴴ * (J * v) = 0 → X * (c * v) = v := by
  obtain ⟨e, b, h_one⟩ := h.spans
  refine ⟨bᴴ * J, fun v hv ↦ h.isUnit.mul_left_cancel ?_⟩
  simpa [h.isHermitian.eq, add_mul, mul_assoc, hv] using congrArg (·ᴴ * (J * v)) h_one

/-- In an isotropic frame `(J, X, Y)`, where `X` spans `A` and `Y` spans `A^⊥`, an isometry `γ`
keeps `A` exactly if it maps `A` into the orthogonal of `A^⊥`, because `A = (A^⊥)^⊥`. -/
lemma mem_spanStabilizer_iff (h : IsIsotropicFrame J X Y) {γ : U J} :
    γ ∈ spanStabilizer J X ↔ Yᴴ * (J * (γ * X)) = 0 := by
  obtain ⟨c, hc⟩ := h.exists_mul_mul_eq_of_orthogonal_right
  refine ⟨fun ⟨r, hr⟩ ↦ ?_, fun h_orth ↦ ⟨c * (γ * X), (hc _ h_orth).symm⟩⟩
  rw [hr, ← mul_assoc J, ← mul_assoc, gram_eq_zero_symm h.isHermitian h.orthogonal, zero_mul]

/-- In an isotropic frame `(J, X, Y)`, where `X` spans `A` and `Y` spans `A^⊥`, an isometry `γ`
that keeps `A` also keeps `A^⊥`: it maps the columns of `Y` into the orthogonal of `A`. -/
lemma orthogonal_mul (h : IsIsotropicFrame J X Y) {γ : U J} (hγ : γ ∈ spanStabilizer J X) :
    Xᴴ * (J * (γ * Y)) = 0 := by
  -- Apply the isometry `γ⁻¹`, which keeps the span, to both arguments of the form.
  obtain ⟨r, hr⟩ := inv_mem hγ
  rw [← mul_assoc, ← U.gram_invariant γ⁻¹, hr]
  simp [mul_assoc, h.orthogonal]

/-- In an isotropic frame `(J, X, Y)`, the matrix `X ≠ 0` is singular, since its columns span an
isotropic subspace for the nondegenerate form `J`. -/
lemma det_eq_zero (h : IsIsotropicFrame J X Y) (hX : X ≠ 0) : X.det = 0 := by
  by_contra h_ne
  exact hX (h.isUnit.mul_right_eq_zero.1
    (((isUnit_iff_isUnit_det X).2 (Ne.isUnit h_ne)).star.mul_right_eq_zero.1 h.isotropic))

/-- In an isotropic frame `(J, X, Y)` with `X ≠ 0`, an isometry that keeps the isotropic subspace
spanned by the columns of `X` has a reducible characteristic polynomial. -/
lemma not_irreducible_charpoly (h : IsIsotropicFrame J X Y) (hX : X ≠ 0) {γ : U J}
    (hγ : γ ∈ spanStabilizer J X) : ¬Irreducible (γ : Matrix n n E).charpoly := by
  obtain ⟨c, hc⟩ := h.exists_mul_mul_eq_of_orthogonal_right
  exact not_irreducible_charpoly_of_mul_eq_mul (GeneralLinearGroup.det_ne_zero (γ : GL n E))
    hX (hc _ (h.mem_spanStabilizer_iff.1 hγ)).symm (by simp [h.det_eq_zero hX])

/-- In an isotropic frame `(J, X, Y)` (a nondegenerate hermitian `J`, the columns of `X` spanning
an isotropic subspace `A` and those of `Y` its orthogonal `A^⊥`), let the isometry `γ` keep `A`
and let the isometry `ν` lie in the unipotent radical of the stabiliser of `A`, that is, `(ν, 1)`
is in the dilation group of `X`: `ν` fixes `A` and is the identity on `A^⊥` modulo `A`. Then
`ν * γ` has the characteristic polynomial of `γ`. -/
lemma charpoly_radical_mul (h : IsIsotropicFrame J X Y) {ν γ : U J}
    (hν : (ν, 1) ∈ dilationGroup X) (hγ : γ ∈ spanStabilizer J X) :
    ((ν * γ : U J) : Matrix n n E).charpoly = (γ : Matrix n n E).charpoly := by
  -- The matrix `N = ν - 1` maps the space into `A^⊥`, `A^⊥` into `A` and `A` to `0`. With the
  -- projection `Y * e` on `A^⊥` and `P = 1 - Y * e`, add `N γ` to `γ` in two steps: first `N γ P`,
  -- which maps into `A^⊥` and kills `A^⊥`, then `N γ Y e`, which maps into `A` and kills `A`.
  obtain ⟨e, he⟩ := h.exists_mul_mul_eq_of_orthogonal_left
  obtain ⟨c, hc⟩ := h.exists_mul_mul_eq_of_orthogonal_right
  obtain ⟨r, hr⟩ := mem_spanStabilizer.1 hγ
  set N : Matrix n n E := ν - 1
  set P : Matrix n n E := 1 - Y * e
  have h_fix : (ν : Matrix n n E) * X = X := mul_eq_self_of_mem_dilationGroup hν
  have h_into_perp : Xᴴ * (J * N) = 0 := by
    rw [← mul_assoc, mul_sub, mul_one, sub_eq_zero]
    simpa [h_fix] using U.gram_invariant ν X (1 : Matrix n n E)
  have h_perp_into : Yᴴ * (J * (N * (γ * Y))) = 0 := by
    simp [N, sub_mul, mul_sub,
      gram_mul_eq_of_mem_dilationGroup hν (h.orthogonal_mul hγ) h.orthogonal]
  have hP {v : Matrix n n E} (hv : Xᴴ * (J * v) = 0) : P * v = 0 := by
    simp [P, sub_mul, mul_assoc, he v hv]
  have h_eq : ((ν * γ : U J) : Matrix n n E) =
      (γ + Y * (e * (N * (γ * P)))) + X * (c * (N * (γ * Y)) * e) := by
    rw [he _ (by rw [← mul_assoc J, ← mul_assoc, h_into_perp, zero_mul]),
      ← mul_assoc X, hc _ h_perp_into, Subgroup.coe_mul, Units.val_mul]
    simp only [N, P]; noncomm_ring
  rw [h_eq, charpoly_add_mul_of_mul_eq_zero (r := r),
    charpoly_add_mul_of_mul_eq_zero (r := e * ((γ : Matrix n n E) * Y))]
  -- First step, from `γ` to `γ + Y * (e * (N * (γ * P)))`:
  · exact (he _ (h.orthogonal_mul hγ)).symm
  · simp [mul_assoc, hP h.orthogonal]
  -- Second step, from `γ + Y * (e * (N * (γ * P)))` to `ν * γ`:
  · simp [add_mul, mul_assoc, hP h.isotropic, hr]
  · simp [N, sub_mul, mul_assoc, he X h.isotropic, hr, ← mul_assoc _ X, h_fix]

end IsIsotropicFrame

end New
