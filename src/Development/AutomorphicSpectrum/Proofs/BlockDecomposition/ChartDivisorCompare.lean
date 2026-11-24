module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegreChartIntegralHoldsStatement
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.TargetsProjFullRankMeetsRegular
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.UniformIntegrabilityProportionalityHolds
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorCompare
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartIntegralPoints
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar

theorem chartDivisorCompare : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.proof GlobalTheory.T.segre_chart_integral_holds
    GroundTheory.Heights₂.Heights.Targets.SegreChartIntegralPoints.proof
    GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorComponents
    GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorLength

end GlobalTheory.CompanionTheory.Ar
