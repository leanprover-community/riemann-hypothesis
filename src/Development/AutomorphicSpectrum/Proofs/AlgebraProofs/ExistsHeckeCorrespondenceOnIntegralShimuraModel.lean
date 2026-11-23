module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosure
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CutEffectiveDivisorStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommuteStatement
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutContraction
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutForms
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutProjection
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutSection
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSegreFlagCutDivisorX
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSegreFlagCutLiesOverX
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersLocalIntegralClosureFinite
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.NumbersDVRC3ResidualContractionComponent
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

namespace GlobalTheory.CompanionTheory.CommAlg.SegreFlag

open GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.AutoClose

theorem segreFlagClosureCut : SegreFlagClosureCut.Statement :=
  SegreFlagClosureCut.proof GlobalTheory.T.cut_effective_divisor
    (PairNumberExpansionIndependence.proof GlobalTheory.T.vertical_divisors_commute)
    NumbersDVR_SegreFlagClosureModel
    (SegreFlagCutSection.proof NumbersDVR_SegreFlagClosureModel
      SegreFlagCutForms.proof SegreFlagCutDivisor.closed segre_flag_degree_zero_holds)
    (SegreFlagCutContraction.proof NumbersDVR_SegreFlagClosureModel
      (SegreFlagCutProjection.proof SegreFlagCutLiesOver.closed NumbersDVR_SegreFlagProjSpecialDim))

end GlobalTheory.CompanionTheory.CommAlg.SegreFlag
