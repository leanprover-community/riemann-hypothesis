import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.QuadraticHeckeZeroEstimates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPrimesShortIntervalLower

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.ShortWindow

theorem ev_log_le {a k : ℝ} (ha : 0 < a) (hk : 0 < k) (A D : ℝ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop, A + D * Real.log x ≤ k * x ^ a := by
  have h1 := (isLittleO_log_rpow_atTop ha).bound (c := k / 2 / D) (by positivity)
  have h2 := (tendsto_rpow_atTop ha).eventually_ge_atTop (A / (k / 2))
  filter_upwards [h1, h2, eventually_ge_atTop (0 : ℝ)] with x h1 h2 hx
  have hp : 0 ≤ x ^ a := Real.rpow_nonneg hx a
  rw [Real.norm_of_nonneg hp] at h1
  have h3 : Real.log x ≤ k / 2 / D * x ^ a := (le_abs_self _).trans h1
  have h4 : D * Real.log x ≤ k / 2 * x ^ a := by
    calc D * Real.log x ≤ D * (k / 2 / D * x ^ a) := by gcongr
      _ = k / 2 * x ^ a := by field_simp
  have h5 : A ≤ k / 2 * x ^ a := by
    rw [div_le_iff₀ (by positivity)] at h2
    linarith
  linarith

theorem exp_term_le {C x W y : ℝ} (hC : 0 < C) (hx : 0 < x) (hW : 1 ≤ W) (hWx : W ≤ x ^ (12 : ℝ))
    (hy : Real.log (200 * C) + 12 * Real.log x ≤ y) : C * Real.exp (-y) ≤ 1 / W / 200 := by
  have h1 : 200 * C * W ≤ Real.exp y := by
    calc 200 * C * W ≤ 200 * C * x ^ (12 : ℝ) := by gcongr
      _ = Real.exp (Real.log (200 * C) + 12 * Real.log x) := by
        rw [Real.exp_add, Real.exp_log (by positivity), Real.rpow_def_of_pos hx, mul_comm (Real.log x)]
      _ ≤ _ := Real.exp_le_exp.2 hy
  have hW0 : 0 < W := by linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  nlinarith


end GlobalTheory.Mem.An.ShortWindow
