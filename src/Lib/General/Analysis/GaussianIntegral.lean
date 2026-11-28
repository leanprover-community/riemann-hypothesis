module

import TauCeti.Analysis.Matrix.Accretive
import TauCeti.Analysis.SpecialFunctions.Gaussian.Accretive
import TauCeti.Analysis.Matrix.L2OpNorm
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar
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
The accretive matrix results and change of variables follow from Tau Ceti. Its Gaussian
integral against Lebesgue measure gives the normalised formula by rescaling.

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

The complex Gaussian integral and the change-of-variables formulas are known results.
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
    (hA : A.IsAccretive) : A.det ≠ 0 :=
  Matrix.IsStrictlyAccretive.det_ne_zero (Matrix.isStrictlyAccretive_iff_posDef.mpr hA)

namespace New.Fock

/-- Lebesgue measure on `ι → ℂ` divided by `π ^ card ι`. -/
noncomputable def normalizedVolume (ι : Type*) [Fintype ι] : Measure (ι → ℂ) :=
  NNReal.pi⁻¹ ^ Fintype.card ι • volume

instance : (normalizedVolume ι).IsAddHaarMeasure := .nnreal_smul _ (by simp [pi_ne_zero])

/-- The image of an additive Haar measure `μ` on `ι → ℂ` under an invertible complex matrix `u` is
`|det u|⁻² μ`. -/
lemma map_mulVec_addHaar_eq_smul [DecidableEq ι]
    {μ : Measure (ι → ℂ)} [μ.IsAddHaarMeasure] {u : Matrix ι ι ℂ} (hu : det u ≠ 0) :
    μ.map (fun x : ι → ℂ ↦ u *ᵥ x) = (ENNReal.ofReal (‖u.det‖ ^ 2))⁻¹ • μ :=
  TauCeti.map_mulVec_addHaar_eq_smul hu

/-- Change of variables on `ι → ℂ`: for a complex square matrix `u` with `det u ≠ 0` and any
`g : (ι → ℂ) → [0, ∞]`, one has `∫ g(y) dy = |det u|² ∫ g(u y) dy` (lower Lebesgue integrals). -/
lemma _root_.New.lintegral_eq_norm_det_sq_mul_lintegral_mulVec [DecidableEq ι]
    (u : Matrix ι ι ℂ) (hu : u.det ≠ 0) (g : (ι → ℂ) → ENNReal) :
    ∫⁻ y : ι → ℂ, g y = ENNReal.ofReal (‖u.det‖ ^ 2) * ∫⁻ y : ι → ℂ, g (u *ᵥ y) :=
  TauCeti.lintegral_eq_norm_det_sq_mul_lintegral_mulVec hu g

lemma star_dotProduct_self_eq_sum : star x ⬝ᵥ x = (∑ i : ι, ‖x i‖ ^ 2 : ℝ) := by
  simp [dotProduct, conj_mul']

lemma star_dotProduct_self_eq_norm_sq : star x ⬝ᵥ x = (‖toLp 2 x‖ : ℂ) ^ 2 := by
  rw [star_dotProduct_self_eq_sum, ← ofReal_pow, norm_sq_eq_of_L2]

/-- The square of the sup norm of `x : ι → ℂ` is at most `x* x = ∑ |x i|²`. -/
lemma norm_sq_le_re_star_dotProduct_self : ‖x‖ ^ 2 ≤ (star x ⬝ᵥ x).re := by
  rw [star_dotProduct_self_eq_norm_sq, ← ofReal_pow, ofReal_re]
  gcongr
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (PiLp.norm_apply_le (toLp 2 x))

/-- The complex Gaussian integral: if `A` is accretive (that is, `A + Aᴴ` is positive definite),
then `exp (-x* A (x - a))` has integral `(det A)⁻¹` for `normalizedVolume ι`, Lebesgue measure on
`ι → ℂ` divided by `π ^ card ι`. -/
lemma integral_gauss [DecidableEq ι] (hA : A.IsAccretive) (a : ι → ℂ) :
    ∫ x : ι → ℂ, exp (-(star x ⬝ᵥ A *ᵥ (x - a))) ∂normalizedVolume ι = A.det⁻¹ := by
  have hA' := Matrix.isStrictlyAccretive_iff_posDef.mpr hA
  simp [normalizedVolume, NNReal.smul_def,
    TauCeti.integral_cexp_neg_star_dotProduct_mulVec hA' a, field]

end New.Fock

end GaussianIntegral
