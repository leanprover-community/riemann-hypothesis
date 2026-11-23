module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUniformiserLocallyInjective
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUniformiserGradientIndependent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolynomialChartInjective
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

theorem UniformiserLocallyInjective.proof (hgrad : UniformiserGradientIndependent.Statement)
    (hchart : PolynomialChartInjective.Statement) : UniformiserLocallyInjective.Statement := by
  intro σ _ I w t hI hic hdim hw ht
  obtain ⟨k, f, hk, hfI, hli⟩ := hgrad σ I w t hI hic hdim hw ht
  obtain ⟨U, hU, hinj⟩ := hchart σ k t f w hk hli
  refine ⟨U, hU, hinj.mono ?_⟩
  rintro z ⟨hz, hzU⟩
  exact ⟨hzU, fun j ↦ hz (f j) (hfI j)⟩

end GroundTheory.Heights₂.Heights
