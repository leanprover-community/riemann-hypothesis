module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

theorem fx_lp_norm_sq_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (v : Lp ℂ 2 μ)
    (G : α → ℂ) (h : (v : α → ℂ) =ᵐ[μ] G) :
    eLpNorm G 2 μ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [eLpNorm_congr_ae h.symm, Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top v), ENNReal.rpow_two]

end

end ReciprocityTheory.L2DbarEstimates.I
