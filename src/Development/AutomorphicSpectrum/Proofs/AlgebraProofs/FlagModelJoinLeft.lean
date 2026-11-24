module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSub
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairNumberPullbackStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinBirationalJoin
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelJoinLeft
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairJoinLeft
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDiv
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDivLeft
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
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

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.proof
    GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisor.proof
    (GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairJoinLeft.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorLeft.proof)
    (GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberJoinLeft.proof GlobalTheory.T.pair_number_pullback
      GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorLeft.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.BirationalJoin.proof)

end GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft
