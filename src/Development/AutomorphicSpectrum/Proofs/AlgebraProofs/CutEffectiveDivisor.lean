module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BlowUpPushHypothesesExample
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlowUpFibreSemilocalStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectionFormulaDegreeStatement
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AevalChartSubstMemOfMemBlowUpOf
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyDimensionInequality
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpDivisorPush
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpFibreDegree
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpVerticalFibre
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpVerticalPush
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFiniteBirationalLength
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHorizontalComponentModel
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersLocalIntegralClosureFinite
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelIrreducibleBasicOpenConnected
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelUnbranchedPartConnected
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

namespace GlobalTheory.CompanionTheory.Ar.Num.CutClosed

open GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.AutoClose

theorem verticalPush : BlowUpVerticalPush.Statement.{0} :=
  BlowUpVerticalPush.proof (BlowUpVerticalFibre.proof BlowUpModel.full
    (BlowUpFibreDegree.proof NumbersDVR_HomLocRingLocal NumbersDVR_DivCycleHomLoc
      FiniteBirationalLength.full GlobalTheory.T.blow_up_fibre_semilocal) GlobalTheory.T.projection_formula_degree)

theorem main : CutByEffectiveDivisor.Statement.{0} :=
  CutByEffectiveDivisor.of_steps NumbersDVR_C3NoCommon
    (CommonFactorInduction.of_open ReesAlgebraDim.full BlowUpStrictTransform.proof
      NumbersDVR_C3BlowUpExcessDrop verticalPush (BlowUpDivisorPush.proof verticalPush)
      NumbersDVR_BlowUpHorizontalCorresp HorizontalComponentModel.proof)

end GlobalTheory.CompanionTheory.Ar.Num.CutClosed
