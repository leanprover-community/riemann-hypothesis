module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Lemma
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder
open ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall

noncomputable def qC {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ) (y : Fin r → ℂ) : ℝ :=
  (∑ i, ∑ j, starRingEnd ℂ (y i) * G i j * y j).re

noncomputable def qR {r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) (y : Fin r → ℝ) : ℝ :=
  ∑ i, ∑ j, y i * G i j * y j

private lemma qC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (y : Fin r → ℂ) :
    qC (Bᴴ * B) y = ∑ k, ‖(B *ᵥ y) k‖ ^ 2 := by
  have h1 : (∑ i, ∑ j, starRingEnd ℂ (y i) * (Bᴴ * B) i j * y j) =
      dotProduct (star y) ((Bᴴ * B) *ᵥ y) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply, RCLike.star_def]
  unfold qC
  rw [h1, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.re_sum, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  refine Finset.sum_congr rfl (fun k _ => by ring)

private lemma qR_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (y : Fin r → ℝ) :
    qR (Bᵀ * B) y = ∑ k, ‖(B *ᵥ y) k‖ ^ 2 := by
  have h1 : qR (Bᵀ * B) y = dotProduct y ((Bᵀ * B) *ᵥ y) := by
    simp only [qR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [h1, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, Real.norm_eq_abs, sq, abs_mul_abs_self]

private lemma setC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    {y | qC (Bᴴ * B) y ≤ R ^ 2} = ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, qC_eq, LinearMap.restrictScalars_apply,
    Matrix.toLin'_apply, sqBall]

private lemma setR_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    {y | qR (Bᵀ * B) y ≤ R ^ 2} = (Matrix.toLin' B) ⁻¹' sqBall r ℝ R := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, qR_eq, Matrix.toLin'_apply, sqBall]

private theorem isBounded_preimage_sqBall_complex_of_det_ne_zero {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (hdet : B.det ≠ 0) (R : ℝ) :
    Bornology.IsBounded (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) := by
  have hS : IsCompact (sqBall r ℂ R) :=
    Metric.isCompact_of_isClosed_isBounded (sqBall_isClosed r R) (sqBall_isBounded r R)
  have hc' : Continuous ((Matrix.toLin' B⁻¹).restrictScalars ℝ) :=
    LinearMap.continuous_of_finiteDimensional _
  refine (hS.image hc').isBounded.subset ?_
  intro y hy
  refine ⟨(Matrix.toLin' B).restrictScalars ℝ y, hy, ?_⟩
  show Matrix.mulVec B⁻¹ (Matrix.mulVec B y) = y
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]

theorem ellipsoidC_props {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (R : ℝ) :
    Convex ℝ {y | qC G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qC G y ≤ R ^ 2}, -y ∈ {y | qC G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qC G y ≤ R ^ 2} ∧ MeasurableSet {y | qC G y ≤ R ^ 2} := by
  obtain ⟨B, hBu, hB⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hG.isStrictlyPositive
  rw [hB, Matrix.star_eq_conjTranspose, setC_eq]
  let T := (Matrix.toLin' B).restrictScalars ℝ
  have hc : Continuous T := LinearMap.continuous_of_finiteDimensional _
  exact ⟨(sqBall_convex (E := ℂ) r R).linear_preimage T,
    fun y hy => by simpa only [Set.mem_preimage, map_neg] using sqBall_neg (E := ℂ) r R _ hy,
    isBounded_preimage_sqBall_complex_of_det_ne_zero B
      ((Matrix.isUnit_iff_isUnit_det B).mp hBu).ne_zero R,
    ((sqBall_isClosed r R).preimage hc).measurableSet⟩

private theorem isBounded_preimage_sqBall_real_of_det_ne_zero {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (hdet : B.det ≠ 0) (R : ℝ) :
    Bornology.IsBounded ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) := by
  have hS : IsCompact (sqBall r ℝ R) :=
    Metric.isCompact_of_isClosed_isBounded (sqBall_isClosed r R) (sqBall_isBounded r R)
  have hc' : Continuous (Matrix.toLin' B⁻¹) := LinearMap.continuous_of_finiteDimensional _
  refine (hS.image hc').isBounded.subset ?_
  intro y hy
  refine ⟨Matrix.toLin' B y, hy, ?_⟩
  show Matrix.mulVec B⁻¹ (Matrix.mulVec B y) = y
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]

theorem ellipsoidR_props {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) (R : ℝ) :
    Convex ℝ {y | qR G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qR G y ≤ R ^ 2}, -y ∈ {y | qR G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qR G y ≤ R ^ 2} ∧ MeasurableSet {y | qR G y ≤ R ^ 2} := by
  obtain ⟨B, hBu, hB⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hG.isStrictlyPositive
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at hB
  rw [hB, setR_eq]
  have hc : Continuous (Matrix.toLin' B) := LinearMap.continuous_of_finiteDimensional _
  exact ⟨(sqBall_convex (E := ℝ) r R).linear_preimage (Matrix.toLin' B),
    fun y hy => by simpa only [Set.mem_preimage, map_neg] using sqBall_neg (E := ℝ) r R _ hy,
    isBounded_preimage_sqBall_real_of_det_ne_zero B
      ((Matrix.isUnit_iff_isUnit_det B).mp hBu).ne_zero R,
    ((sqBall_isClosed r R).preimage hc).measurableSet⟩

end ReciprocityTheory.GeometryOfNumbersTheory
