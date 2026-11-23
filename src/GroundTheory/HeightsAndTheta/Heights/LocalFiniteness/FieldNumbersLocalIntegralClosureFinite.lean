module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeDeepMass
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisBis
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTail
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocalizedQuotientIsSimpleModuleOfMul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutLiesOver
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConePolyLocalization
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocalRing
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsLocalIntegralClosureFinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepMass
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepRankOne
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AevalEqOfVdeg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivCycleEqZeroOfNotMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivCycleNeZeroFacts
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsExtra
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsSide
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingLocal
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPrimeDimLeTrdeg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagProjSpecialDim
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConePolyLocalization
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarSurj
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocFrac
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocalRing
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PLocalIntegralClosureFinite
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartDehomog
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PNoetherIntegralClosure
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelGrowthOffHypersurfacePolynomial
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.NumbersDVRC3ResidualContractionComponent
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

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConePolyLocalization.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConePolyLocalization.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConePolyLocalization.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocLocal GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarUnit GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarSurj.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarInj

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocalRing.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocalRing.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocalRing.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocLocal GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocNoetherian GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocDim

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_LocalIntegralClosureFinite.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.LocalIntegralClosureFinite.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.LocalIntegralClosureFinite.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.NoetherIntegralClosureFinite.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_FunctionFieldFinite GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof GroundTheory.Heights₂.Heights.FieldNumbers.MChartDehomog.proof GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocFrac.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.segre_flag_degree_zero_holds : GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagDegreeZero.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagDegreeZero.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureModel

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualContraction.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.ResidualContraction.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.ResidualContraction.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpOrderLe GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualContractionComponent

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3NoCommon.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.NoCommonComponentCase.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.NoCommonComponentCase.of_open.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LeftTermSupport.proof GroundTheory.Heights₂.Heights.NumbersDVR.RightTermSupport.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalCoeffRing

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagProjSpecialDim : GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagProjSpecialDim.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagProjSpecialDim.proof GroundTheory.Heights₂.Heights.NumbersDVR.PrimeDimLeTrdeg.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_FlagProjTrdegLe

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingLocal.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingLocal.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingIsLocal GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingNoetherian GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingDimLe

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ExceptionalCompare.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.ExceptionalComparison.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.ExceptionalComparison.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpOrderLe GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ExceptionalContraction

theorem GroundTheory.Heights₂.Heights.AutoClose.TubeDeepMass : GroundTheory.Heights₂.Heights.TubeDeepMass.Statement :=
  @GroundTheory.Heights₂.Heights.TubeDeepMass.proof GroundTheory.Heights₂.Heights.TubeDeepRankOne.proof GroundTheory.Heights₂.Heights.AutoClose.TubeDeepAreaCount GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.TubeDeepWeightMass
