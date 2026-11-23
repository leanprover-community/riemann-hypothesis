module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffLimit
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeLocalLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalFiniteRank
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ZeroLeDivCycle
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeLocalLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocFrac
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreFinite
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PLocalizedQuotientLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFiniteRank
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersLocalIntegralClosureFinite
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelUnbranchedPartConnected
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalLength.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalLength.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalLength.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.LocalizedQuotientLength.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalFlat

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFiniteRank.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFiniteRank.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.FibreFinite.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFinite GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocFrac.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpExcessDrop.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpExcessDecreases.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpExcessDecreases.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.ExcessPositive.full GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualCompare GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ExceptionalCompare

theorem GroundTheory.Heights₂.Heights.AutoClose.CutOffLimit : GroundTheory.Heights₂.Heights.CutOffLimit.Statement :=
  @GroundTheory.Heights₂.Heights.CutOffLimit.of_open GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SheetImageAreaSet GroundTheory.Heights₂.Heights.AutoClose.TubeEuclMass

theorem GroundTheory.Heights₂.Heights.AutoClose.StokesOnVariety : GroundTheory.Heights₂.Heights.StokesOnVariety.Statement :=
  @GroundTheory.Heights₂.Heights.StokesOnVariety.of_open GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SheetImageAreaSet GroundTheory.Heights₂.Heights.AutoClose.TubeEuclMass
