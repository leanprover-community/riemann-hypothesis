module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StStokesOnChart
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFibreNonempty
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalResidueLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOnChart
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocLocalize
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocResidue
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreNonempty
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalResidueLength
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersLocalIntegralClosureFinite
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelIrreducibleBasicOpenConnected
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

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_FibreNonempty.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.FibreNonempty.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.FibreNonempty.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocalRing

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalResidueLength.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalResidueLength.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalResidueLength.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocResidue.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocLocalize.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.StokesOnChart : GroundTheory.Heights₂.Heights.StokesOnChart.Statement :=
  @GroundTheory.Heights₂.Heights.StokesOnChart.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ComplexSets.DiscriminantCover GroundTheory.Heights₂.Heights.AutoClose.CutOffLimit
