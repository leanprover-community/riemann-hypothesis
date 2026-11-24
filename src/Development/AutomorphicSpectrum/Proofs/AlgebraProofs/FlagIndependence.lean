module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHeckeCorrespondenceOnIntegralShimuraModelStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairNumberPullbackStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommute
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PAdjoinTrdegAdd
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDvrConeDimTrdeg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHsymmPairFlagIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairBundleTrdeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairConeAlg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairConeLinesIndep
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberRelabel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreClosureNumber
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureBirational
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureTrdeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagConeAlg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSymmetricSpanHsymm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExist
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExpress
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalDivisorJoinPullback
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.CompanionTheory.CommAlg.FlagIndependence

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagIndependence.Statement := by
  have hPE := PairNumberExpansionIndependence.proof
    GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute
  have hCM : GenericProjClosureModel.Statement :=
    GenericProjClosureModel.proof TwistedDualGensExist.proof
      (GenericProjClosureDim.proof DvrConeDimTrdeg.proof
        (PairBundleTrdeg.proof AdjoinTrdegAdd.proof PairConeLinesIndep.proof PairConeAlg.proof))
      (GenericProjClosureDivisor.proof TwistedDualGensExpress.proof)
  have hFM : SegreFlagClosureModel.Statement :=
    SegreFlagClosureModel.proof (SegreFlagClosureTrdeg.proof SegreFlagConeAlg.proof)
  have hSP := SegreFlagClosurePullback.proof GlobalTheory.T.pair_number_pullback hPE hFM
    PairNumberRelabel.proof VerticalDivisorJoinPullback.proof SegreFlagClosureBirational.proof
  have hSCN := SegreClosureNumber.proof hPE hFM
    GlobalTheory.T.exists_heckeCorrespondence_on_integral_shimuraModel hSP
  exact FlagIndependence.proof hPE (HsymmPairFlagIndependence.proof hPE hCM hSCN)
    SymmetricSpanHsymm.proof

end GlobalTheory.CompanionTheory.CommAlg.FlagIndependence
