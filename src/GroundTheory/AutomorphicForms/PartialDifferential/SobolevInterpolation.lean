module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Lean.Elab.MutualDef
import Mathlib.Analysis.Distribution.TemperedDistribution

@[expose] public section

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem one_add_norm_sq_le (ξ η : E) :
    1 + ‖ξ‖ ^ 2 ≤ 2 * (1 + ‖ξ - η‖ ^ 2) * (1 + ‖η‖ ^ 2) := by
  have h : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by
    simpa using norm_add_le (ξ - η) η
  have h2 : ‖ξ‖ ^ 2 ≤ 2 * ‖ξ - η‖ ^ 2 + 2 * ‖η‖ ^ 2 := by
    nlinarith [norm_nonneg ξ, norm_nonneg (ξ - η), norm_nonneg η, sq_nonneg (‖ξ - η‖ - ‖η‖)]
  nlinarith [sq_nonneg ‖ξ - η‖, sq_nonneg ‖η‖, mul_nonneg (sq_nonneg ‖ξ - η‖) (sq_nonneg ‖η‖)]

theorem peetre (r : ℝ) (ξ η : E) :
    (1 + ‖ξ‖ ^ 2) ^ r ≤ 2 ^ |r| * (1 + ‖ξ - η‖ ^ 2) ^ |r| * (1 + ‖η‖ ^ 2) ^ r := by
  have pξ : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  have pη : (0 : ℝ) < 1 + ‖η‖ ^ 2 := by positivity
  have pζ : (0 : ℝ) < 1 + ‖ξ - η‖ ^ 2 := by positivity
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr, ← Real.mul_rpow (by norm_num) pζ.le, ← Real.mul_rpow (by positivity) pη.le]
    exact Real.rpow_le_rpow pξ.le (one_add_norm_sq_le ξ η) hr
  · rw [abs_of_nonpos hr]
    have key : (1 + ‖η‖ ^ 2) ^ (-r) ≤ 2 ^ (-r) * (1 + ‖ξ - η‖ ^ 2) ^ (-r) * (1 + ‖ξ‖ ^ 2) ^ (-r) := by
      rw [← Real.mul_rpow (by norm_num) pζ.le, ← Real.mul_rpow (by positivity) pξ.le]
      apply Real.rpow_le_rpow pη.le _ (by linarith)
      have := one_add_norm_sq_le η ξ
      rwa [norm_sub_rev] at this
    rw [Real.rpow_neg pη.le, Real.rpow_neg pξ.le] at key
    have a := Real.rpow_pos_of_pos pξ r
    have b := Real.rpow_pos_of_pos pη r
    have c : 0 < 2 ^ (-r) * (1 + ‖ξ - η‖ ^ 2) ^ (-r) := by positivity
    rw [le_mul_inv_iff₀ a, inv_mul_le_iff₀ b] at key
    calc (1 + ‖ξ‖ ^ 2) ^ r = (1 + ‖ξ‖ ^ 2) ^ r * 1 := (mul_one _).symm
      _ ≤ _ := by nlinarith

end

end GroundTheory.Automorphic.Sobolev
