module

public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.Integrability.Log

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Real
open scoped InnerProductSpace

theorem norm_circleMap_sub_ofReal_sq (r φ : ℝ) :
    ‖circleMap 0 1 φ - (r : ℂ)‖ ^ 2 = 1 + r ^ 2 - 2 * r * Real.cos φ := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [circleMap, Complex.exp_re, Complex.exp_im]
  nlinarith [Real.sin_sq_add_cos_sq φ]

theorem ZonalKernel.proof : ZonalKernel.Statement := by
  intro c₁ h₁ c₂ h₂ hne
  obtain ⟨h₁l, h₁u⟩ := h₁
  obtain ⟨h₂l, h₂u⟩ := h₂
  have hs₁ : Real.sqrt (1 - c₁ ^ 2) ^ 2 = 1 - c₁ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs₂ : Real.sqrt (1 - c₂ ^ 2) ^ 2 = 1 - c₂ ^ 2 := Real.sq_sqrt (by nlinarith)
  set B := Real.sqrt (1 - c₁ ^ 2) * Real.sqrt (1 - c₂ ^ 2) with hBdef
  set A := 1 - c₁ * c₂ with hAdef
  set D := |c₁ - c₂| with hDdef
  have hD : 0 < D := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hA : 0 ≤ A := by nlinarith
  have hB : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hABD : A ^ 2 = B ^ 2 + D ^ 2 := by
    rw [hBdef, mul_pow, hs₁, hs₂, hDdef, sq_abs]; ring
  have hAD : 0 < A + D := by linarith
  set r := B / (A + D) with hrdef
  have hr0 : 0 ≤ r := div_nonneg hB hAD.le
  have hBlt : B < A + D := by nlinarith
  have hr1 : r < 1 := (div_lt_one hAD).mpr hBlt
  have key : ∀ φ : ℝ, kernelL ⟪spherePoint c₁ 0, spherePoint c₂ φ⟫_ℝ =
      (1 / 2) * Real.log ((A + D) / 4) + Real.log ‖circleMap 0 1 φ - (r : ℂ)‖ := by
    intro φ
    have hinner : ⟪spherePoint c₁ 0, spherePoint c₂ φ⟫_ℝ = c₁ * c₂ + B * Real.cos φ := by
      simp [spherePoint, PiLp.inner_apply, Fin.sum_univ_three, hBdef]
      ring
    have hne0 : ‖circleMap 0 1 φ - (r : ℂ)‖ ≠ 0 := by
      rw [norm_ne_zero_iff, sub_ne_zero]
      intro h
      have := congrArg norm h
      rw [norm_circleMap_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at this
      norm_num at this
      linarith
    have hfac : (1 - (c₁ * c₂ + B * Real.cos φ)) / 2 =
        (A + D) / 4 * ‖circleMap 0 1 φ - (r : ℂ)‖ ^ 2 := by
      rw [norm_circleMap_sub_ofReal_sq, hrdef]
      field_simp
      linear_combination (2 : ℝ) * hABD
    rw [kernelL, hinner, hfac, Real.log_mul (by positivity) (pow_ne_zero 2 hne0), Real.log_pow]
    push_cast
    ring
  simp only [key]
  have hint : IntervalIntegrable (fun φ : ℝ => Real.log ‖circleMap 0 1 φ - (r : ℂ)‖)
      MeasureTheory.volume 0 (2 * π) := circleIntegrable_log_norm_sub_const (a := (r : ℂ)) (c := 0) 1
  rw [intervalIntegral.integral_add intervalIntegrable_const hint, intervalIntegral.integral_const]
  have havg := circleAverage_log_norm_sub_const₀ (a := (r : ℂ))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
  rw [circleAverage_def, smul_eq_mul] at havg
  have hpi : (2 * π) ≠ 0 := by positivity
  have hsum : A + D = (1 + max c₁ c₂) * (1 - min c₁ c₂) := by
    rcases le_total c₁ c₂ with h | h
    · rw [max_eq_right h, min_eq_left h, hDdef, abs_of_nonpos (by linarith), hAdef]; ring
    · rw [max_eq_left h, min_eq_right h, hDdef, abs_of_nonneg (by linarith), hAdef]; ring
  rw [zonalKernel, ← hsum, mul_add, havg, smul_eq_mul, sub_zero, ← mul_assoc, inv_mul_cancel₀ hpi]
  ring

end GroundTheory.Heights₂.Heights.FlagBundles
