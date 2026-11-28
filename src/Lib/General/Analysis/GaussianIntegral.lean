module

import TauCeti.Analysis.SpecialFunctions.Gaussian.Reproducing
import TauCeti.Analysis.Matrix.L2OpNorm
import TauCeti.Analysis.Matrix.OstrowskiTaussky
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Algebra.Field
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Separation.CompletelyRegular
public import Lib.Speed
import Lib.Base

/-!
# Matrix norm estimates and the complex Gaussian integral

This file proves estimates for complex matrices and computes the complex Gaussian integral on
`ι → ℂ`. Here `‖A‖` is the `ℓ²` operator norm. For accretive `A`, the integral of
`exp (-x* A (x - a))` against normalised Lebesgue measure is `(det A)⁻¹`.
Nonvanishing of accretive determinants follows from Tau Ceti's Ostrowski–Taussky inequality.

## Main definitions and results

* `New.l2_opNorm_le_of_apply`: for an `m × n` matrix the operator norm is at most `|m| |n|` times
  a bound for the entries.
* `Matrix.IsAccretive`: the matrices `A` with `A + Aᴴ` positive definite. Positive definite matrices
  are accretive (`Matrix.PosDef.isAccretive`), and accretive matrices have nonzero determinant
  (`Matrix.IsAccretive.det_ne_zero`).
* `New.Fock.normalizedVolume`: Lebesgue measure divided by `π ^ card ι`, so that `exp (-|x|²)` has
  integral `1`.
* `New.Fock.map_mulVec_addHaar_eq_smul`, `New.lintegral_eq_norm_det_sq_mul_lintegral_mulVec`: the
  change of variables by an invertible complex matrix `u`, whose real Jacobian is `‖det u‖ ^ 2`.
* `New.Fock.integral_gauss`: if `A` is accretive, the integral of `exp (-x* A (x - a))` is
  `(det A)⁻¹`.

## Relation to the literature

The Ostrowski–Taussky inequality and the complex Gaussian integral are known results.
-/

@[expose] public section

/-! ## Operator norm and matrix entries -/

namespace New

open Matrix Norms.L2Operator ComplexOrder Fintype

variable {m n : Type _} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}

lemma l2_opNorm_single [DecidableEq m] {i : m} {j : n} {c : ℂ} : ‖single i j c‖ = ‖c‖ := by
  simp [← mul_self_inj, ← l2_opNorm_conjTranspose_mul_self, ← diagonal_single, Pi.norm_single]

/-- If all entries of an `m × n` complex matrix `A` have norm at most `M`, then the `ℓ²` operator
norm of `A` is at most `|m| |n| M`. -/
lemma l2_opNorm_le_of_apply {M : ℝ} (h_apply : ∀ (i : m) (j : n), ‖A i j‖ ≤ M) :
    ‖A‖ ≤ card m * card n * M := by
  classical
  -- `A` is the sum of `card m * card n` matrices with one entry each.
  grw [A.matrix_eq_sum_single, norm_sum_le, norm_sum_le, l2_opNorm_single.le, h_apply]
  simp [field]

end New

/-! ## Accretive matrices, normalised measure on `ι → ℂ` and the complex Gaussian integral -/

section GaussianIntegral

open MeasureTheory Matrix Complex Finset ComplexOrder MatrixOrder PiLp CStarAlgebra NNReal WithLp

variable {ι : Type _} [Fintype ι] (x : ι → ℂ) {A : Matrix ι ι ℂ}

/-- A complex square matrix `A` is (strictly) accretive if `A + Aᴴ` is positive definite. -/
def Matrix.IsAccretive (A : Matrix ι ι ℂ) : Prop := (A + Aᴴ).PosDef

omit [Fintype ι] in
lemma Matrix.PosDef.isAccretive (hA : A.PosDef) : A.IsAccretive := hA.add hA.conjTranspose

lemma Matrix.IsAccretive.det_ne_zero [DecidableEq ι]
    (hA : A.IsAccretive) : A.det ≠ 0 := fun h_det ↦ by
  have h_le : ‖(A + Aᴴ).det‖ ≤ 2 ^ Fintype.card ι * ‖A.det‖ :=
    hA.posSemidef.norm_det_le_two_pow_mul (by simpa using PosSemidef.zero)
  simp [h_det, hA.det_pos.ne'] at h_le

namespace New.Fock

/-- Lebesgue measure on `ι → ℂ` divided by `π ^ card ι`. -/
noncomputable def normalizedVolume (ι : Type*) [Fintype ι] : Measure (ι → ℂ) :=
  NNReal.pi⁻¹ ^ Fintype.card ι • volume

instance : (normalizedVolume ι).IsAddHaarMeasure := .nnreal_smul _ (by simp [pi_ne_zero])

/-- The image of an additive Haar measure `μ` on `ι → ℂ` under an invertible complex matrix `u` is
`|det u|⁻² μ`. -/
lemma map_mulVec_addHaar_eq_smul [DecidableEq ι]
    {μ : Measure (ι → ℂ)} [μ.IsAddHaarMeasure] {u : Matrix ι ι ℂ} (hu : det u ≠ 0) :
    μ.map (fun x : ι → ℂ ↦ u *ᵥ x) = (ENNReal.ofReal (‖u.det‖ ^ 2))⁻¹ • μ := by
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := u.toLin'.restrictScalars ℝ
  -- the real determinant of the complex linear map `u` is `‖det u‖ ^ 2`
  have h_det : LinearMap.det f = ‖u.det‖ ^ 2 := by
    simp [f, LinearMap.det_restrictScalars, Algebra.norm_complex_eq, ← Complex.sq_norm]
  change μ.map f = _
  simp [μ.map_linearMap_addHaar_eq_smul_addHaar, h_det, hu]

/-- Change of variables on `ι → ℂ`: for a complex square matrix `u` with `det u ≠ 0` and any
`g : (ι → ℂ) → [0, ∞]`, one has `∫ g(y) dy = |det u|² ∫ g(u y) dy` (lower Lebesgue integrals). -/
lemma _root_.New.lintegral_eq_norm_det_sq_mul_lintegral_mulVec [DecidableEq ι]
    (u : Matrix ι ι ℂ) (hu : u.det ≠ 0) (g : (ι → ℂ) → ENNReal) :
    ∫⁻ y : ι → ℂ, g y = ENNReal.ofReal (‖u.det‖ ^ 2) * ∫⁻ y : ι → ℂ, g (u *ᵥ y) := by
  have h_emb : MeasurableEmbedding (fun y : ι → ℂ ↦ u *ᵥ y) :=
    Continuous.measurableEmbedding (by fun_prop) (mulVec_injective_of_det_ne_zero hu)
  rw [← h_emb.lintegral_map, map_mulVec_addHaar_eq_smul hu]
  simp [ENNReal.mul_inv_cancel_left, hu]

lemma star_dotProduct_self_eq_sum : star x ⬝ᵥ x = (∑ i : ι, ‖x i‖ ^ 2 : ℝ) := by
  simp [dotProduct, conj_mul']

lemma star_dotProduct_self_eq_norm_sq : star x ⬝ᵥ x = (‖toLp 2 x‖ : ℂ) ^ 2 := by
  rw [star_dotProduct_self_eq_sum, ← ofReal_pow, norm_sq_eq_of_L2]

/-- The square of the sup norm of `x : ι → ℂ` is at most `x* x = ∑ |x i|²`. -/
lemma norm_sq_le_re_star_dotProduct_self : ‖x‖ ^ 2 ≤ (star x ⬝ᵥ x).re := by
  rw [star_dotProduct_self_eq_norm_sq, ← ofReal_pow, ofReal_re]
  gcongr
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (PiLp.norm_apply_le (toLp 2 x))

/-- An accretive matrix `A` (that is, `A + Aᴴ` is positive definite) is congruent to a diagonal
matrix whose entries have positive real part. -/
lemma exists_eq_conjTranspose_mul_diagonal_mul [DecidableEq ι] (hA : A.IsAccretive) :
    ∃ (p : GL ι ℂ) (d : ι → ℂ),
      A = (p : Matrix ι ι ℂ)ᴴ * diagonal d * (p : Matrix ι ι ℂ) ∧ ∀ i : ι, 0 < (d i).re := by
  -- Write `A + Aᴴ = Bᴴ B` and diagonalise `H = B⁻ᴴ (Im A) B⁻¹` by a unitary `U`, with real
  -- eigenvalues `λ`. Then `p = U⁻¹ B` and `d = i λ + 1 / 2`.
  obtain ⟨b, hb_unit, hb : A + Aᴴ = star b * b⟩ :=
    isStrictlyPositive_iff_eq_star_mul_self.mp hA.isStrictlyPositive
  lift b to GL ι ℂ using hb_unit with B
  set H : Matrix ι ι ℂ := star (B : Matrix ι ι ℂ)⁻¹ * imaginaryPart A * (B : Matrix ι ι ℂ)⁻¹
  have hH : H.IsHermitian := ((imaginaryPart A).prop.conjugate' B⁻¹).isHermitian
  set U : Matrix ι ι ℂ := ↑hH.eigenvectorUnitary
  have h_spectral : U * diagonal (ofReal ∘ hH.eigenvalues) * star U = H := by
    simpa using hH.spectral_theorem.symm
  let d : ι → ℂ := fun i ↦ I * hH.eigenvalues i + 2⁻¹
  have hd : diagonal d = I • diagonal (ofReal ∘ hH.eigenvalues) + (2⁻¹ : ℂ) • 1 := by
    simp [smul_one_eq_diagonal, ← diagonal_smul, d]
  refine ⟨Unitary.toUnits hH.eigenvectorUnitary⁻¹ * B, d, ?_, by simp [d]⟩
  calc
    A = I • (imaginaryPart A : Matrix ι ι ℂ) + (2⁻¹ : ℂ) • (A + Aᴴ) := by
      rw [imaginaryPart_apply_coe, smul_smul, mul_neg, I_mul_I, neg_neg, star_eq_conjTranspose]
      module
    _ = star (B : Matrix ι ι ℂ) * (I • H + (2⁻¹ : ℂ) • 1) * B := by
      simp [mul_add, add_mul, hb, H, ← mul_assoc, ← star_mul]
    _ = star (B : Matrix ι ι ℂ) * (U * diagonal d * star U) * B := by
      simp [hd, mul_add, add_mul, h_spectral, U]
    _ = _ := by simp [U, star_eq_conjTranspose, mul_assoc]

/-- The complex Gaussian integral in one variable: if `0 < re d`, then `exp (-z̄ d (z - a))` has
integral `π / d` over `ℂ`. -/
lemma integral_cexp_neg_star_mul {d : ℂ} (hd : 0 < d.re) (a : ℂ) :
    ∫ z : ℂ, exp (-(star z * (d * (z - a)))) = Real.pi / d := by
  convert TauCeti.integral_cexp_neg_mul_norm_sq_add hd 0 (d * a) using 1
  · congr 1; ext z; congr 1
    rw [← conj_mul', star_def]
    ring
  · simp

/-- The complex Gaussian integral: if `A` is accretive (that is, `A + Aᴴ` is positive definite),
then `exp (-x* A (x - a))` has integral `(det A)⁻¹` for `normalizedVolume ι`, Lebesgue measure on
`ι → ℂ` divided by `π ^ card ι`. -/
lemma integral_gauss [DecidableEq ι] (hA : A.IsAccretive) (a : ι → ℂ) :
    ∫ x : ι → ℂ, exp (-(star x ⬝ᵥ A *ᵥ (x - a))) ∂normalizedVolume ι = A.det⁻¹ := by
  -- Write `A = pᴴ diagonal d p`. After the change of variables `y = p x` the integrand is a
  -- product of Gaussians in one variable.
  obtain ⟨p, d, rfl, hd⟩ := exists_eq_conjTranspose_mul_diagonal_mul hA
  set P : Matrix ι ι ℂ := (p : Matrix ι ι ℂ)
  let g (i : ι) (z : ℂ) : ℂ := exp (-(star z * (d i * (z - (P *ᵥ a) i))))
  have h_form (x : ι → ℂ) :
      exp (-(star x ⬝ᵥ (Pᴴ * diagonal d * P) *ᵥ (x - a))) = ∏ i : ι, g i ((P *ᵥ x) i) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← star_mulVec_dotProduct, mulVec_sub]
    simp [g, dotProduct, mulVec_diagonal, ← exp_sum]
  have h_prod : ∫ y : ι → ℂ, ∏ i : ι, g i (y i) = ∏ i : ι, Real.pi / d i := by
    simp only [integral_fintype_prod_volume_eq_prod g, g, integral_cexp_neg_star_mul (hd _)]
  have h_det : (Pᴴ * diagonal d * P).det = ‖P.det‖ ^ 2 * ∏ i : ι, d i := by
    simp [← mul_conj', mul_comm, mul_left_comm]
  calc
    _ = ∫ y : ι → ℂ, ∏ i : ι, g i (y i) ∂(normalizedVolume ι).map (fun x : ι → ℂ ↦ P *ᵥ x) := by
      rw [integral_map (by fun_prop) (Continuous.aestronglyMeasurable (by fun_prop)), funext h_form]
    _ = (‖P.det‖ ^ 2 * Real.pi ^ Fintype.card ι)⁻¹ * ∏ i : ι, Real.pi / d i := by
      rw [map_mulVec_addHaar_eq_smul p.det_ne_zero]
      simp [normalizedVolume, P, h_prod, NNReal.smul_def, field]
    _ = (Pᴴ * diagonal d * P).det⁻¹ := by simp [h_det, field]

end New.Fock

end GaussianIntegral
