module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointMemHalfPlane
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaAtBasePointZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Set Filter Topology Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

theorem continuousOn_bet (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    ContinuousOn (bet α) (Hh TT) := by
  exact (contDiffOn_bet hα).continuousOn

theorem cont_vert (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    Continuous fun θ : ℝ => bet α (x0 TT + (θ : ℂ) * I) := by
  exact (continuousOn_bet hα).comp_continuous (by fun_prop) (vert_mem hTT)

theorem im_circleIntegral (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    (circleIntegral α 0 (TT + 1)).im = ∫ θ in (0 : ℝ)..2 * Real.pi, (bet α (x0 TT + (θ : ℂ) * I)).re := by
  have hint : IntervalIntegrable (fun θ : ℝ => I * bet α (x0 TT + (θ : ℂ) * I)) MeasureTheory.volume
      0 (2 * Real.pi) :=
    (continuous_const.mul (cont_vert hTT hα)).intervalIntegrable _ _
  rw [circleIntegral_eq hTT, ← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
  congr 1
  funext θ
  simp [Complex.mul_im]

theorem th_top (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    th TT α (x0 TT + 2 * Real.pi * I) = 2 * (circleIntegral α 0 (TT + 1)).im := by
  rw [im_circleIntegral hTT hα]
  have hw : x0 TT + 2 * Real.pi * I - x0 TT = ((2 * Real.pi : ℝ) : ℂ) * I := by push_cast; ring
  have harg : ∀ t : ℝ, x0 TT + (t : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * I) =
      x0 TT + ((2 * Real.pi * t : ℝ) : ℂ) * I := by
    intro t; push_cast; ring
  have him : ∀ z : ℂ, (z * (((2 * Real.pi : ℝ) : ℂ) * I)).im = 2 * Real.pi * z.re := by
    intro z
    simp [Complex.mul_im, Complex.mul_re]
    ring
  simp only [th, prim, hw, om_apply, harg, him]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (f := fun θ : ℝ => (bet α (x0 TT + (θ : ℂ) * I)).re)
      (by positivity : (2 * Real.pi) ≠ 0)]
  simp only [mul_zero, mul_one, smul_eq_mul]
  have hpi : (2 * Real.pi) * (2 * Real.pi)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  rw [← mul_assoc (2 * Real.pi), hpi, one_mul]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
