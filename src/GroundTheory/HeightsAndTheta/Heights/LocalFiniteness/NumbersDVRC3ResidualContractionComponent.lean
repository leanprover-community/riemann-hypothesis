module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeDeepAreaCount
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BlowUpPushHypothesesExample
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ComapLiftFormConstChartPrimeExample
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsLast
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocCycle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsHomLocRingLocal
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagProjSpecialDimSteps
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarInj
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarUnit
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocDim
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFunctionFieldFinite
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreSide
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepAreaCount
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalCorresp
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalLift
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalSat
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalStrict
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagProjTrdegLe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingDimLe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalCoeffRing
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotColon
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotPrimes
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotRing
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ResidualNewVarMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RingKrullDimLeOfIsAlgebraicAdjoinSingleton
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarInj
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarUnit
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocDim
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFunctionFieldFinite
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartDehomog
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartHomog
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Imports
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartNormPts
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelGrowthOffHypersurfacePolynomial
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.IsolatedPointsCount
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

theorem GroundTheory.Heights₂.Heights.AutoClose.Inter_R1Indep : GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.Statement :=
  @GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.of_remaining GroundTheory.Heights₂.Heights.AutoClose.Inter_R1RegMaxSurj

theorem GroundTheory.Heights₂.Heights.AutoClose.chart_norm_count : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement :=
  @GroundTheory.Heights₂.Heights.Inter.ChartNormCount.proof GroundTheory.Heights₂.Heights.AutoClose.Inter_ChartSpecCount GroundTheory.Heights₂.Heights.Inter.ChartNormPts.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarInj.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarInj.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarInj.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarNumerator

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarUnit.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarUnit.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarUnit.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarNumerator

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_FunctionFieldFinite.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.MChartDehomog.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartTrdeg

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocDim.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocDim.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocDim.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.MChartHomog.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartTrdeg GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartLocDim

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureModel : GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureModel.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureModel.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureTrdeg

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_FlagProjTrdegLe : GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureTrdeg

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ExceptionalContraction.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.ExceptionalContraction.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.ExceptionalContraction.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpHorizontalCorresp.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalCorresp.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalCorresp.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalSat.full GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpHorizontalMult GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalLift.full GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalStrict.full

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualContractionComponent.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.ResidualContractionComponent.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.ResidualContractionComponent.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalCoeffRing.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.LocalCoeffRing.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.LocalCoeffRing.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotRing.proof GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotPrimes.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocCycleLocalQuot GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotColon.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalQuotFinsum GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalCoeffLocal

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingDimLe.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingMem.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingIsLocal

theorem GroundTheory.Heights₂.Heights.AutoClose.TubeDeepAreaCount : GroundTheory.Heights₂.Heights.TubeDeepAreaCount.Statement :=
  @GroundTheory.Heights₂.Heights.TubeDeepAreaCount.proof GroundTheory.Heights₂.Heights.AutoClose.IsolatedPointsCount
