module

public import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem covDet (n : ℕ) (f' : V n →L[ℂ] V n) :
    |(f'.restrictScalars ℝ : V n →L[ℝ] V n).det| =
      ‖LinearMap.det (f' : V n →ₗ[ℂ] V n)‖ ^ 2 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, LinearMap.det_restrictScalars,
    Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity)]

theorem cov (n : ℕ) : CovStatement n := by
  intro W G f hW hG hinj _
  have hd : ∀ y ∈ W, HasFDerivWithinAt G ((fderiv ℂ G y).restrictScalars ℝ) W y := fun y hy =>
    (((hG y hy).differentiableAt (hW.mem_nhds hy)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hW.measurableSet hd hinj f]
  simp only [covDet]

end ReciprocityTheory.L2DbarEstimates.I
