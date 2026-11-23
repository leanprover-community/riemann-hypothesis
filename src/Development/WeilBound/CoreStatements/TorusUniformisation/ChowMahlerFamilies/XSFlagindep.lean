module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosure
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PAdjoinTrdegAdd
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDvrConeDimTrdeg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHsymmPairFlagIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairBundleTrdeg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairConeAlg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairConeLinesIndep
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberRelabel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreClosureNumber
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureBirational
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureTrdeg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagConeAlg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSymmetricSpanHsymm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExist
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExpress
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalDivisorJoinPullback
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

namespace PositivityTheory.Xgn.A_s_flagindep

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem closureModel : GenericProjClosureModel.Statement :=
  GenericProjClosureModel.proof TwistedDualGensExist.proof
    (GenericProjClosureDim.proof DvrConeDimTrdeg.proof
      (PairBundleTrdeg.proof AdjoinTrdegAdd.proof PairConeLinesIndep.proof PairConeAlg.proof))
    (GenericProjClosureDivisor.proof TwistedDualGensExpress.proof)

theorem flagClosureModel : SegreFlagClosureModel.Statement :=
  SegreFlagClosureModel.proof (SegreFlagClosureTrdeg.proof SegreFlagConeAlg.proof)

theorem of_items (hC2 : VerticalDivisorsCommute.Statement.{0}) (hPull : PairNumberPullback.Statement)
    (hCut : SegreFlagClosureCut.Statement) : FlagIndependence.Statement := by
  have hPE := PairNumberExpansionIndependence.proof hC2
  have hSP := SegreFlagClosurePullback.proof hPull hPE flagClosureModel PairNumberRelabel.proof
    VerticalDivisorJoinPullback.proof SegreFlagClosureBirational.proof
  have hSCN := SegreClosureNumber.proof hPE flagClosureModel hCut hSP
  exact FlagIndependence.proof hPE (HsymmPairFlagIndependence.proof hPE closureModel hSCN)
    SymmetricSpanHsymm.proof

end PositivityTheory.Xgn.A_s_flagindep
