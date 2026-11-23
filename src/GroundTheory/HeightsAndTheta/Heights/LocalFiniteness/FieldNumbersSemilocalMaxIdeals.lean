module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegFixedBallMass
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalMaxIdeals
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegDensNonneg
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegFixedBallMass
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocLocalize
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocSeparate
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocUnits
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreFinite
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreRelDim
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalMaxIdeals
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.CentredDiscCoverCurveHolds
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersSemilocalResidueLength
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

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalMaxIdeals.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalMaxIdeals.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalMaxIdeals.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.FibreFinite.proof GroundTheory.Heights₂.Heights.FieldNumbers.FibreRelDim.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_FibreNonempty GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocUnits.proof GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocSeparate.proof GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocLocalize.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalResidueLength

theorem GroundTheory.Heights₂.Heights.AutoClose.RegFixedBallMass : GroundTheory.Heights₂.Heights.RegFixedBallMass.Statement :=
  @GroundTheory.Heights₂.Heights.RegFixedBallMass.proof GroundTheory.Heights₂.Heights.RegDensNonneg.proof GroundTheory.Heights₂.Heights.AutoClose.StokesOnChart GroundTheory.Heights₂.Heights.AutoClose.LogIntegrable GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact
