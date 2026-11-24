module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitBis
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagFurtherTermIndependentStatementStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinLeftStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinRightStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagPlainValueIndependentStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ImportsAlt
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.JoinTwoModels
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.JoinVerticalDivisorStatement
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelCommonModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelValueIndep
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairValueIndep
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

namespace GlobalTheory.CompanionTheory.CommAlg.FlagModelValue


open GroundTheory.Heights₂.Heights.NumbersDVR in
theorem main : FlagModelValueIndependence.Statement :=
  FlagModelValueIndependence.proof
    (FlagPairValueIndependence.proof GlobalTheory.T.flag_plain_value_independent GlobalTheory.T.flag_further_term_independent_statement)
    (_root_.GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelCommonModel.proof
      GlobalTheory.CompanionTheory.CommAlg.joinTwoModels
      GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt.main
      GlobalTheory.CompanionTheory.Heights.join_vertical_divisor_statement
      GlobalTheory.T.flag_model_join_left GlobalTheory.T.flag_model_join_right)

end GlobalTheory.CompanionTheory.CommAlg.FlagModelValue
