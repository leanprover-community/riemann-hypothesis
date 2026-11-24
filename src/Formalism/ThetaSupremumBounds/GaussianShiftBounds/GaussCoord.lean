module

public import Formalism.ThetaSupremumBounds.StatementA
public import Formalism.ThetaSupremumBounds.GaussianShiftBounds.BlockIntegralOf
public import Formalism.ThetaSupremumBounds.GaussianShiftBounds.HeightsoundOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public section

open Finset MeasureTheory
open scoped ComplexConjugate Real

namespace Formalism.DimensionVariation

private theorem integral_complex_exp_neg_mul_sq_norm {c : ℝ} (hc : 0 < c) :
    ∫ z : ℂ, Real.exp (-(c * ‖z‖ ^ 2)) = π / c := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  calc ∫ z : ℂ, Real.exp (-(c * ‖z‖ ^ 2))
      = ∫ z : ℂ, (fun p : ℝ × ℝ => Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2))
          (Complex.measurableEquivRealProd z) := by
        congr 1
        funext z
        show Real.exp (-(c * ‖z‖ ^ 2)) = Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2)
        rw [← Real.exp_add, hsq]
        congr 1
        ring
    _ = ∫ p : ℝ × ℝ, Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2) := by
        exact Complex.volume_preserving_equiv_real_prod.integral_comp'
          (fun p : ℝ × ℝ => Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2))
    _ = (∫ x : ℝ, Real.exp (-c * x ^ 2)) * ∫ y : ℝ, Real.exp (-c * y ^ 2) :=
        integral_prod_mul (fun x : ℝ => Real.exp (-c * x ^ 2)) (fun y : ℝ => Real.exp (-c * y ^ 2))
    _ = π / c := by
        rw [integral_gaussian]
        exact Real.mul_self_sqrt (div_nonneg Real.pi_pos.le hc.le)

theorem gaussianIntegralDiagonal : GaussCoord := by
  intro κ hκ b hb
  have hint_r : ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2) = ∏ x, π / b x := by
    calc ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2)
        = ∫ u : κ → ℂ, ∏ x, Real.exp (-(b x * ‖u x‖ ^ 2)) := by
          congr 1
          funext u
          rw [← Finset.sum_neg_distrib, Real.exp_sum]
      _ = ∏ x, ∫ z : ℂ, Real.exp (-(b x * ‖z‖ ^ 2)) := by
          exact MeasureTheory.integral_fintype_prod_volume_eq_prod
            (fun x (z : ℂ) => Real.exp (-(b x * ‖z‖ ^ 2)))
      _ = ∏ x, π / b x :=
          Finset.prod_congr rfl fun x _ => integral_complex_exp_neg_mul_sq_norm (hb x)
  refine ⟨?_, hint_r⟩
  by_contra hni
  have h0 : ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2) = 0 := integral_undef hni
  rw [hint_r] at h0
  exact (Finset.prod_ne_zero_iff.mpr fun x _ => div_ne_zero Real.pi_ne_zero (hb x).ne') h0

theorem blockIntegralBound : BlockIntegral :=
  blockIntegral_of gaussianIntegralDiagonal

theorem blockBound_of_fockJet (hF : FockJet) : BlockBound :=
  blockBound_of hF blockIntegralBound

end Formalism.DimensionVariation
