module

import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Data.Finset.CastCard
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
public import Lib.General.Groups.BesselGroups

/-!
# Lines and hyperplanes over a field

This file describes the stabilisers in `GL_n` of the line of a basis vector `e_i` and of the
complementary coordinate hyperplane. Over a finite field it counts the linear forms with value `1`
at `e_i`, and those with value `1` both at `e_i` and at a vector off its line. It shows that `0`
is a simple root of the characteristic polynomial of a matrix of block shape `(0 ∗; 0 g')`
with `g'` invertible.

Notions from other files:
* `parabolic lev`: the subgroup of `GL_n` of the matrices `g` with `g a b = 0` whenever
  `lev b < lev a`. The two stabilisers use level functions with values in `Prop`, ordered by
  implication.

## Relation to the literature

Standard linear algebra.
-/

@[expose] public section

namespace New

open Matrix Finset

/-! ### Stabilisers and counts -/

attribute [local instance] Prop.linearOrder

section Field

variable {F n : Type} [Field F] [Fintype n] [DecidableEq n] {i : n} {g h : GL n F}

/-- In the order of propositions by implication, `p < q` says that `q` holds and `p` does not. -/
lemma prop_lt_iff_not_and {p q : Prop} : p < q ↔ ¬p ∧ q := by
  simp only [lt_iff_le_not_ge, le_Prop_eq]
  tauto

/-- An element lies in `parabolic lev` exactly when its matrix is block triangular for `lev`. -/
lemma mem_parabolic_iff_blockTriangular {α : Type} [LinearOrder α] {lev : n → α} :
    g ∈ parabolic lev ↔ (g : Matrix n n F).BlockTriangular lev :=
  Iff.rfl

/-- An element `g` lies in `parabolic (· ≠ i)`, the block triangular matrices for the levels
`(· ≠ i)`, exactly when `g j i = 0` for all `j ≠ i`: the group is the stabiliser of the line of
`e_i`. -/
lemma mem_parabolic_ne : g ∈ parabolic (· ≠ i) ↔ ∀ j ≠ i, g j i = 0 := by
  rw [mem_parabolic_iff_blockTriangular]
  refine ⟨fun hg j hj ↦ hg (prop_lt_iff_not_and.2 ⟨not_not.2 rfl, hj⟩), fun hg a b h_lt ↦ ?_⟩
  obtain ⟨rfl, ha⟩ : b = i ∧ a ≠ i := by simpa [prop_lt_iff_not_and] using h_lt
  exact hg a ha

/-- An element `g` lies in `parabolic (· = i)`, the block triangular matrices for the levels
`(· = i)`, exactly when `g i j = 0` for all `j ≠ i`: the group is the stabiliser of the hyperplane
spanned by the `e_j`, `j ≠ i`. -/
lemma mem_parabolic_eq : g ∈ parabolic (· = i) ↔ ∀ j ≠ i, g i j = 0 := by
  rw [mem_parabolic_iff_blockTriangular]
  refine ⟨fun hg j hj ↦ hg (prop_lt_iff_not_and.2 ⟨hj, rfl⟩), fun hg a b h_lt ↦ ?_⟩
  obtain ⟨hb, rfl⟩ : b ≠ i ∧ a = i := prop_lt_iff_not_and.1 h_lt
  exact hg b hb

omit [Fintype n] in
/-- A vector is a multiple of `e_i` exactly when its other coordinates vanish. -/
lemma exists_eq_smul_single_iff {z : n → F} :
    (∃ c : F, z = c • Pi.single i 1) ↔ ∀ j ≠ i, z j = 0 := by
  refine ⟨?_, fun hz ↦ ⟨z i, by ext j; by_cases hj : j = i <;> simp [hj, hz]⟩⟩
  rintro ⟨c, rfl⟩ j hj
  simp [hj]

/-- The elements `g` and `h` have the same left coset of `parabolic (· ≠ i)`, the stabiliser of
the line of `e_i`, exactly when `h e_i` lies on the line of `g e_i`. -/
lemma inv_mul_mem_parabolic_ne :
    g⁻¹ * h ∈ parabolic (· ≠ i) ↔
      ∃ c : F, (h : Matrix n n F).col i = c • (g : Matrix n n F).col i := by
  have h_col (j : n) : (g⁻¹ * h) j i = ((g⁻¹ : GL n F) *ᵥ (h : Matrix n n F).col i) j := by
    simp [Matrix.mul_apply, mulVec, dotProduct]
  simp only [mem_parabolic_ne, h_col, ← exists_eq_smul_single_iff]
  refine exists_congr fun c ↦ ?_
  rw [← mulVec_single_one (g : Matrix n n F), ← mulVec_smul]
  exact ⟨fun h_eq ↦ by simp [← h_eq, mulVec_mulVec],
    fun h_eq ↦ by simp [h_eq, mulVec_mulVec]⟩

/-- The elements `g` and `h` have the same right coset of `parabolic (· = i)`, the stabiliser of
the hyperplane `z i = 0`, exactly when the `i`-th row of `h` is a multiple of that of `g`. -/
lemma mul_inv_mem_parabolic_eq :
    h * g⁻¹ ∈ parabolic (· = i) ↔
      ∃ c : F, (h : Matrix n n F).row i = c • (g : Matrix n n F).row i := by
  simpa [mem_parabolic_eq, mem_parabolic_ne, transposeGL, ← transpose_mul, Matrix.col, Matrix.row]
    using (inv_mul_mem_parabolic_ne (i := i) (g := transposeGL g) (h := transposeGL h))

/-- If the `i`-th column of an invertible `g` vanishes off the diagonal, then `g i i ≠ 0`. -/
lemma diag_ne_zero_of_col (hg : ∀ j ≠ i, g j i = 0) : g i i ≠ 0 :=
  fun h_zero ↦ g.det_ne_zero (det_eq_zero_of_column_eq_zero i fun j ↦ by grind)

/-- If the `i`-th row of an invertible `g` vanishes off the diagonal, then `g i i ≠ 0`. -/
lemma diag_ne_zero_of_row (hg : ∀ j ≠ i, g i j = 0) : g i i ≠ 0 :=
  diag_ne_zero_of_col (g := transposeGL g) hg

/-- Replacing the `j`-th column of the identity matrix by `z` gives determinant `z j`. -/
lemma det_updateCol_one (j : n) (z : n → F) : (updateCol 1 j z).det = z j := by
  rw [← cramer_apply, cramer_one, one_apply_eq_self]

/-- Replacing the `j`-th row of the identity matrix by `z` gives determinant `z j`. -/
lemma det_updateRow_one (j : n) (z : n → F) : (updateRow 1 j z).det = z j := by
  rw [← det_transpose, ← updateCol_transpose, transpose_one, det_updateCol_one]

/-- Every non-zero vector is the `i`-th column of an invertible matrix. -/
lemma exists_col_eq (i : n) {z : n → F} (hz : z ≠ 0) :
    ∃ g : GL n F, (g : Matrix n n F).col i = z := by
  -- Put `z` into a column `j` with `z j ≠ 0` of the identity, and exchange the columns `i`, `j`.
  obtain ⟨j, hj⟩ : ∃ j : n, z j ≠ 0 := Function.ne_iff.1 hz
  refine ⟨GeneralLinearGroup.mkOfDetNeZero (updateCol 1 j z) (by rwa [det_updateCol_one]) *
    GeneralLinearGroup.swap F j i, by ext; simp⟩

/-- A fibre of a surjective additive homomorphism has size `#A / #B`, viewed in `ℂ`. -/
private lemma cast_card_fiber_of_surjective {A B : Type} [AddGroup A] [Fintype A] [AddGroup B]
    [Fintype B] [DecidableEq B] (p : A →+ B) (hp : Function.Surjective p) (b : B) :
    (#{a : A | p a = b} : ℂ) = Fintype.card A / Fintype.card B := by
  apply (eq_div_iff (Nat.cast_ne_zero.2 Fintype.card_ne_zero)).2
  rw [AddMonoidHom.card_fiber_eq_of_mem_range p (hp b) (hp 0)]
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    congrArg (Nat.cast : ℕ → ℂ) (AddSubgroup.card_ker_mul_card_of_surjective hp)

variable [Fintype F] [DecidableEq F]

/-- There are `qⁿ / q` forms taking the value one at the coordinate vector `eᵢ`. -/
private lemma card_normalized_forms (i : n) :
    (#{ξ : n → F | ξ i = 1} : ℂ) = (Fintype.card F : ℂ) ^ Fintype.card n / Fintype.card F := by
  simpa using cast_card_fiber_of_surjective (Pi.evalAddMonoidHom (fun _ : n ↦ F) i)
    (Function.surjective_eval i) 1

/-- A form taking the value one at `eᵢ` takes that value on `qⁿ / q` vectors. -/
private lemma card_affine_hyperplane {ξ : n → F} (hξ : ξ i = 1) :
    (#{z : n → F | ξ ⬝ᵥ z = 1} : ℂ) = (Fintype.card F : ℂ) ^ Fintype.card n / Fintype.card F := by
  simpa using cast_card_fiber_of_surjective (AddMonoidHom.mk' (ξ ⬝ᵥ ·) (dotProduct_add ξ))
    (fun t ↦ ⟨Pi.single i t, by simpa using congrArg (· * t) hξ⟩) 1

/-- For `z` off the line of `eᵢ`, evaluation at `eᵢ` and at `z` prescribes two independent
coordinates of a form. There are `qⁿ / q²` forms taking the value one at both. -/
private lemma card_normalized_forms_through {z : n → F} {j : n} (hj : j ≠ i) (hz : z j ≠ 0) :
    (#{ξ : n → F | ξ i = 1 ∧ ξ ⬝ᵥ z = 1} : ℂ) =
      (Fintype.card F : ℂ) ^ Fintype.card n / (Fintype.card F : ℂ) ^ 2 := by
  let p : (n → F) →+ F × F := (Pi.evalAddMonoidHom (fun _ : n ↦ F) i).prod
    (AddMonoidHom.mk' (· ⬝ᵥ z) fun a b ↦ add_dotProduct a b z)
  have onto : Function.Surjective p := by
    rintro ⟨a, b⟩
    exact ⟨Pi.single i a + Pi.single j ((b - a * z i) / z j), by simp [p, hj.symm, hz]⟩
  simpa [p, Prod.mk.injEq, sq] using cast_card_fiber_of_surjective p onto (1, 1)

/-- For a vector `z` let `N z` be the number of forms `ξ` with `ξ e_i = 1` and `ξ z = 1`. The sum
of `f z` over the pairs `(ξ, z)` with `ξ e_i = 1` and `ξ z = 1` is the sum of `N z • f z` over all
vectors `z`. -/
lemma sum_forms_sum_eq_sum_card_smul {W : Type} [AddCommMonoid W] (i : n) (f : (n → F) → W) :
    ∑ ξ : n → F with ξ i = 1, ∑ z : n → F with ξ ⬝ᵥ z = 1, f z =
      ∑ z : n → F, #{ξ : n → F | ξ i = 1 ∧ ξ ⬝ᵥ z = 1} • f z := by
  simp [sum_comm' (t' := univ) (s' := fun z ↦ {ξ : n → F | ξ i = 1 ∧ ξ ⬝ᵥ z = 1})]

/-- If a weight vanishes on the nonzero multiples of `eᵢ`, the incidence sum counts each
remaining nonzero vector with the same multiplicity `qⁿ / q²`. -/
private lemma sum_incidence_of_vanishing_on_line {W : Type} [AddCommGroup W] [Module ℂ W]
    (g : (n → F) → W) (hg : ∀ z, z ≠ 0 → (∀ j ≠ i, z j = 0) → g z = 0) :
    ∑ ξ : n → F with ξ i = 1, ∑ z : n → F with ξ ⬝ᵥ z = 1, g z =
      ((Fintype.card F : ℂ) ^ Fintype.card n / (Fintype.card F : ℂ) ^ 2) •
        ∑ z : n → F with z ≠ 0, g z := by
  classical
  rw [sum_forms_sum_eq_sum_card_smul, filter_ne', ← sum_erase_add _ _ (mem_univ (0 : n → F))]
  simp only [dotProduct_zero, zero_ne_one, and_false, filter_false, card_empty, zero_smul, add_zero,
    smul_sum]
  refine sum_congr rfl fun z hz ↦ ?_
  by_cases h : ∀ j ≠ i, z j = 0
  · simp [hg z (ne_of_mem_erase hz) h]
  · obtain ⟨j, hj, hzj⟩ : ∃ j ≠ i, z j ≠ 0 := by simpa using h
    rw [← Nat.cast_smul_eq_nsmul ℂ, card_normalized_forms_through hj hzj]

/-- Over a field of `q` elements and in dimension `n`, let `f` have the value `y` at the non-zero
multiples of `e_i`. Then the sum of `f z` over all forms `ξ` with `ξ e_i = 1` and all vectors `z`
with `ξ z = 1` is `q ^ (n - 2)` times the sum of `y` and all `f z` with `z ≠ 0`. Here `ξ` stands
for a hyperplane that does not contain `e_i`, and `z` for a line outside this hyperplane. -/
lemma sum_sum_dotProduct_eq_one_eq_smul {W : Type} [AddCommGroup W] [Module ℂ W] {f : (n → F) → W}
    {y : W} (hf : ∀ z : n → F, z ≠ 0 → (∀ j ≠ i, z j = 0) → f z = y) :
    ∑ ξ : n → F with ξ i = 1, ∑ z : n → F with ξ ⬝ᵥ z = 1, f z =
      (Fintype.card F : ℂ) ^ (Fintype.card n - 2 : ℤ) • (y + ∑ z : n → F with z ≠ 0, f z) := by
  -- Apply the incidence count to `f - y`, which vanishes on the nonzero multiples of `e_i`.
  -- To add back the constant weight `y`, count the normalized forms and the vectors on each
  -- affine hyperplane using `card_normalized_forms` and `card_affine_hyperplane`.
  have centered := sum_incidence_of_vanishing_on_line (i := i) (fun z ↦ f z - y)
    (fun z hz h ↦ sub_eq_zero.mpr (hf z hz h))
  have hcard (ξ : n → F) (hξ : ξ ∈ ({ξ : n → F | ξ i = 1} : Finset _)) :=
    card_affine_hyperplane (mem_filter.mp hξ).2
  simp +contextual only [sum_sub_distrib, sum_const, ← Nat.cast_smul_eq_nsmul ℂ, hcard,
    card_normalized_forms, filter_ne', cast_card_erase_of_mem (mem_univ _),
    card_univ, Fintype.card_fun, Nat.cast_pow] at centered
  have hq : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [zpow_sub₀ hq, zpow_natCast, zpow_ofNat, filter_ne']
  linear_combination (norm := module) centered

end Field

/-! ### Matrices that keep a line -/

section Shape

open Polynomial

variable {F n : Type} [Field F] [Fintype n] [DecidableEq n] {i : n} {M N : Matrix n n F}

/-- The matrix `M` has the block shape `(∗ ∗; 0 g')` with `g'` invertible, where the first block is
the index `i`. -/
structure KeepsLine (i : n) (M : Matrix n n F) : Prop where
  /-- The `i`-th column vanishes off the diagonal. -/
  col_eq_zero : ∀ j ≠ i, M j i = 0
  /-- The block on the other indices is invertible. -/
  block_det_ne_zero : (M.toSquareBlockProp (· ≠ i)).det ≠ 0

/-- If `KeepsLine i N`, so that the column `i` of `N` vanishes off the diagonal and its block on
the other indices is invertible, then the diagonal entry at `i` of `M * N` is the product of those
of `M` and `N`. -/
lemma KeepsLine.mul_apply_self (hN : KeepsLine i N) : (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply]
  exact Fintype.sum_eq_single i fun j hj ↦ mul_eq_zero_of_right _ (hN.col_eq_zero j hj)

/-- If `M` and `N` satisfy `KeepsLine i` (their column `i` vanishes off the diagonal and their
block on the other indices is invertible), then so does `M * N`. -/
lemma KeepsLine.mul (hM : KeepsLine i M) (hN : KeepsLine i N) : KeepsLine i (M * N) where
  col_eq_zero j hj := by
    rw [Matrix.mul_apply,
      Fintype.sum_eq_single i fun l hl ↦ mul_eq_zero_of_right _ (hN.col_eq_zero l hl),
      hM.col_eq_zero j hj, zero_mul]
  block_det_ne_zero := by
    have h_block : (M * N).toSquareBlockProp (· ≠ i) =
        M.toSquareBlockProp (· ≠ i) * N.toSquareBlockProp (· ≠ i) := by
      ext a b
      have h_corner : M a i * N i b = 0 := mul_eq_zero_of_left (hM.col_eq_zero a a.property) _
      simp only [toSquareBlockProp_def, Matrix.mul_apply, of_apply]
      rw [← sum_subtype (univ.erase i) (by simp) fun l : n ↦ M a l * N l b,
        sum_erase univ (f := fun l : n ↦ M a l * N l b) h_corner]
    rw [h_block, det_mul]
    exact mul_ne_zero hM.block_det_ne_zero hN.block_det_ne_zero

/-- If the column `i` of `M` vanishes off the diagonal, then `det M` is the product of `M i i` and
the determinant of the block on the other indices. -/
lemma det_eq_mul_det_block {R : Type} [CommRing R] {M : Matrix n n R} (hM : ∀ j ≠ i, M j i = 0) :
    M.det = M i i * (M.toSquareBlockProp (· ≠ i)).det := by
  have h_corner : (M.toSquareBlockProp (· = i)).det = M i i := by
    rw [det_eq_elem_of_subsingleton _ ⟨i, rfl⟩, toSquareBlockProp_def, of_apply]
  rw [← h_corner]
  -- `convert` matches the two `Fintype` instances on the indices equal to `i`.
  convert twoBlockTriangular_det M (· = i) fun a ha b hb ↦ by simpa [hb] using hM a ha

/-- An element of `parabolic (· ≠ i)`, the stabiliser of the line of `e_i`, has the block shape
`KeepsLine i`: its column `i` vanishes off the diagonal and the block on the other indices is
invertible. -/
lemma keepsLine_of_mem_parabolic {g : GL n F} (hg : g ∈ parabolic (· ≠ i)) :
    KeepsLine i (g : Matrix n n F) where
  col_eq_zero := mem_parabolic_ne.1 hg
  block_det_ne_zero := right_ne_zero_of_mul
    ((det_eq_mul_det_block (mem_parabolic_ne.1 hg)).symm.trans_ne g.det_ne_zero)

/-- If the column `i` of `M` is zero, also at the diagonal, and the block on the other indices is
invertible, then `0` is a simple root of the characteristic polynomial of `M`. -/
lemma KeepsLine.rootMultiplicity_charpoly (hM : KeepsLine i M) (h_zero : M i i = 0) :
    M.charpoly.rootMultiplicity 0 = 1 := by
  set M' : Matrix {j : n // j ≠ i} {j : n // j ≠ i} F := M.toSquareBlockProp (· ≠ i)
  have h_factor : M.charpoly = X * M'.charpoly := by
    have h_block : M.charmatrix.toSquareBlockProp (· ≠ i) = M'.charmatrix := by
      ext1 a b
      simp [M', toSquareBlockProp_def, charmatrix_apply, diagonal_apply, Subtype.ext_iff]
    rw [Matrix.charpoly, det_eq_mul_det_block (i := i) fun j hj ↦ by simp [hj, hM.col_eq_zero j hj],
      h_block, charmatrix_apply_eq, h_zero, C_0, sub_zero, Matrix.charpoly]
  have h_root : ¬ M'.charpoly.IsRoot 0 := fun h_root ↦ hM.block_det_ne_zero <| by
    rw [det_eq_sign_charpoly_coeff, coeff_zero_eq_eval_zero, h_root.eq_zero, mul_zero]
  rw [h_factor, rootMultiplicity_mul (mul_ne_zero X_ne_zero M'.charpoly_monic.ne_zero),
    rootMultiplicity_eq_zero h_root, add_zero]
  simpa only [C_0, sub_zero] using rootMultiplicity_X_sub_C_self (x := (0 : F))

end Shape

end New
