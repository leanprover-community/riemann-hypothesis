module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Imports
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMass
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBaseChangeAvoid
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartZeroTrdeg
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormBaseChange
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormExtend
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormReducedRadical
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeBallFinite
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFiniteFibreDim
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFsLogIntegrable
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeGraphCover
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeJacMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeKrullDimLe
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSmoothLocalGraph
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeTangentDim
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFormsThroughPoint
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGraphAreaFibre
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGraphAreaIntegral
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PHolomorphicImplicitGraph
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncIdealNeBotDim
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncIdealSeparate
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncidenceZeroLocus
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PKernelProjMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPolyLocalGenerators
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjPrimeHasPoint
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRadicalBaseChange
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentGaussInvariant
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentJacComp
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentJacCompress
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PThroughPointIncIdeal
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PThroughTwoPointsTrdeg
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTrdegAdjoinLe
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTrdegBaseAlgebraic
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PConormalGenerationGeneric
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameJacobianGeneric
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PJacobianRankGeneric
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Imports
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ChowFormBaseChange.full : ChowFormBaseChange.Statement :=
  (ChowFormBaseChange.proof
    RadicalBaseChange.proof
    (ChowFormExtend.proof RadicalBaseChange.proof)
    (ChowFormReduced.proof_of_prime_separate
      IncIdealPrime.full
      (IncIdealSeparate.proof
        IncidenceZeroLocus.proof
        (FormsThroughPoint.proof
          IncidenceZeroLocus.proof
          ThroughPointIncIdeal.proof
          (ChartZeroTrdeg.proof AffineChartTrdeg.full)
          (ThroughTwoPointsTrdeg.proof TrdegAdjoinLe.proof)
          TrdegBaseAlgebraic.proof)
        (IncIdealNeBotDim.proof IncIdealDim.full))))

theorem BaseChangeAvoid.full : BaseChangeAvoid.Statement :=
  BaseChangeAvoid.proof

theorem ProjPrimeHasPoint.full : ProjPrimeHasPoint.Statement :=
  ProjPrimeHasPoint.proof

theorem ChowFormSectionVertical.full : ChowFormSectionVertical.Statement :=
  Vertical.ChowFormSectionVertical.full

theorem ConeMassOfFibre.full : ConeMassOfFibre.Statement :=
  (ConeMassOfFibre.of_open
    ConeFiniteFibreDim.proof
    (ConeGraphCover.proof
      ConeFiniteFibreDim.proof
      (ConeTangentDim.proof
        (ConeKrullDimLe.proof ConeFiniteFibreDim.proof)
        NullSmaller.full
        (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof))
      (ConeSmoothLocalGraph.proof PolyLocalGenerators.proof HolomorphicImplicitGraph.proof))
    (ConeJacMeasurable.proof TangentJacCompress.proof KernelProjMeasurable.proof)
    (ConeTangentDim.proof
      (ConeKrullDimLe.proof ConeFiniteFibreDim.proof)
      NullSmaller.full
      (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof))
    (GraphAreaFibre.proof
      (GraphAreaIntegral.proof GraphAreaHolomorphic.full)
      TangentJacComp.proof
      AreaMultiplicityWeight.proof)
    TangentGaussInvariant.proof)

theorem ConeIntegralMass.full : ConeIntegralMass.Statement :=
  (ConeIntegralMass.proof ConeFibreDegree.full ConeMassOfFibre.full)

theorem ConeBallFinite.full : ConeBallFinite.Statement :=
  (ConeBallFinite.proof ConeIntegralMass.full)

theorem ConeFsLogIntegrable.full : ConeFsLogIntegrable.Statement :=
  (ConeFsLogIntegrable.proof ConeBallFinite.full ConeSlabBound.full)

end GroundTheory.Heights₂.Heights
