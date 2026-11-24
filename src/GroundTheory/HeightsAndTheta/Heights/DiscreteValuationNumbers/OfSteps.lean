module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SpanTwoIsPrimeRelevant
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsMaxHeight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CycEvalEqAddMulOfCycle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsAlt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.MemMinimalPrimesOfDivCycleNeZero
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConservationOfNumberLE
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByEffectiveDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleFiniteSupport
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PEffectiveShift
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericCycleCorresp
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimBound
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericFibProps
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumAddFirstField
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMaximalIdealHeightFG
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialQuotDim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem DivCycleMul.full : DivCycleMul.Statement.{u} := DivCycleMul.proof

theorem DivCycleFiniteSupport.full : DivCycleFiniteSupport.Statement.{u} :=
  DivCycleFiniteSupport.proof

theorem SupSpanMultiHomog.full : SupSpanMultiHomog.Statement.{u} := SupSpanMultiHomog.proof

theorem MinimalPrimeMultiHomog.full : MinimalPrimeMultiHomog.Statement.{u} :=
  MinimalPrimeMultiHomog.proof

theorem SpecialQuotDim.full : SpecialQuotDim.Statement.{u} := SpecialQuotDim.proof

theorem MaximalIdealHeightFG.full : MaximalIdealHeightFG.Statement.{u} := MaximalIdealHeightFG.proof

theorem GenericDimBound.full : GenericDimBound.Statement.{u} :=
  GenericDimBound.proof MaximalIdealHeightFG.full

theorem GenericFibProps.full : GenericFibProps.Statement.{u} := GenericFibProps.proof

theorem GenericCycleCorresp.full : GenericCycleCorresp.Statement.{u} := GenericCycleCorresp.proof

theorem ConservationOfNumberLE.full : ConservationOfNumberLE.Statement.{u} :=
  ConservationOfNumberLE.proof IntNumAssoc.full SpecialCycleEval.full SpecialPieceRank.full
    GenericPieceRank.full SpecialIdealMultiHomog.full

theorem UniformiserCase.full : UniformiserCase.Statement.{u} :=
  UniformiserCase.proof ConservationOfNumberLE.full GenericDimBound.full GenericFibProps.full
    GenericCycleCorresp.full MinimalPrimeMultiHomog.full SupSpanMultiHomog.full DimStrictDrop.full
    CutByForm.full

theorem ShiftByUniformiser.full : ShiftByUniformiser.Statement.{u} :=
  ShiftByUniformiser.proof DivCycleMul.full DivCycleFiniteSupport.full

theorem EffectiveShift.full : EffectiveShift.Statement.{u} := EffectiveShift.proof

theorem Representative.full : Representative.Statement.{u} := Representative.proof DivCycleMul.full

theorem IntNumAddFirst.full : IntNumAddFirst.Statement.{u} :=
  IntNumAddFirst.proof FieldNumbers.IntNumAdd.full FieldNumbers.IntNumZeroSlot.full
    FieldNumbers.HilbDegreeBound.full

theorem EffectiveCase.of_steps (h₀ : NoCommonComponentCase.Statement.{u}) (h₁ : CommonFactorInduction.Statement.{u}) :
    EffectiveCase.Statement.{u} :=
  EffectiveCase.proof h₀ h₁

theorem CutByEffectiveDivisor.of_steps (h₀ : NoCommonComponentCase.Statement.{u})
    (h₁ : CommonFactorInduction.Statement.{u}) : CutByEffectiveDivisor.Statement.{u} :=
  CutByEffectiveDivisor.proof (EffectiveCase.of_steps h₀ h₁) UniformiserCase.full
    ShiftByUniformiser.full EffectiveShift.full

end GroundTheory.Heights₂.Heights.NumbersDVR
