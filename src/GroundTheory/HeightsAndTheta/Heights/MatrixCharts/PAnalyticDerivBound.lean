module

public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsBounds
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem AnalyticDerivBound.proof : AnalyticDerivBound.Statement := by
  intro E _ _ f U K hU hf hK hKU
  have hcd : ContDiffOn ℂ 1 f U := hf.contDiffOn hU.uniqueDiffOn
  have hf' : ContinuousOn (fderiv ℂ f) U := hcd.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn (hcd.continuousOn.mono hKU)
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn (hf'.mono hKU)
  refine ⟨max (max C₁ C₂) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx => ?_⟩
  have hd : DifferentiableAt ℂ f x := (hf x (hKU hx)).differentiableAt
  refine ⟨hd.restrictScalars ℝ, ?_, ?_⟩
  · exact (hC₁ x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
  · rw [hd.fderiv_restrictScalars ℝ, ContinuousLinearMap.norm_restrictScalars]
    exact (hC₂ x hx).trans ((le_max_right _ _).trans (le_max_left _ _))

end GroundTheory.Heights₂.Heights
