module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Star.Real
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem a_bounds_of_ge_two_n_pow_five : ∀ (k r : ℕ) (a : ℝ), 1 ≤ k → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 ≤ a → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < a / 2 ∧ (2 * ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) * (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) + 1) + 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 1 ≤ a := by
  intro k r a hk ha
  have hM : ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) = 2 * ((r : ℝ) ^ 2 + r + 1) := by push_cast; ring
  rw [hM]
  generalize hN : ((2 * r + k + 1 : ℕ) : ℝ) = N at ha ⊢
  have hN' : N = 2 * (r : ℝ) + k + 1 := by rw [← hN]; push_cast; ring
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) ≤ r := r.cast_nonneg
  have h2 : 2 ≤ N := by linarith
  have hrn : 2 * ((r : ℝ) + 1) ≤ N := by linarith
  have hN2 : 4 ≤ N ^ 2 := by linarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 2]
  have hN3 : 8 ≤ N ^ 3 := by linarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 3]
  have hN4 : 4 * N ^ 2 ≤ N ^ 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hN2) (sq_nonneg N)]
  have h5a : 8 * N ^ 2 ≤ N ^ 5 := by nlinarith [mul_nonneg (sub_nonneg.mpr hN3) (sq_nonneg N)]
  have h5b : 2 * N ^ 4 ≤ N ^ 5 := by nlinarith [mul_nonneg (sub_nonneg.mpr h2) (pow_nonneg (by linarith : (0:ℝ) ≤ N) 4)]
  have hm : 4 * ((r : ℝ) ^ 2 + r + 1) ≤ N ^ 2 := by nlinarith
  have hm2 : 4 * ((r : ℝ) ^ 2 + r + 1) * N ^ 2 ≤ N ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hm (sq_nonneg N)]
  constructor
  · linarith
  · nlinarith

end GlobalTheory.SgInf
