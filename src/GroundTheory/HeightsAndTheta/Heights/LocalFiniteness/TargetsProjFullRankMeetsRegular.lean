module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisorLength
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowDegreePos
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeAverage
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogMeasurable
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.ObjectsChowIntChowFormExists
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.UniformIntegrabilityProportionalityHolds
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorLength
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartSectionNotMem
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorLength : GroundTheory.Heights₂.Heights.Targets.ChartDivisorLength.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.ChartDivisorLength.proof GroundTheory.Heights₂.Heights.Targets.ChartSectionNotMem.proof GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorComponents GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartSectionLength

theorem GroundTheory.Heights₂.Heights.AutoClose.ConeAverage : GroundTheory.Heights₂.Heights.ConeAverage.Statement :=
  @GroundTheory.Heights₂.Heights.ConeAverage.proof GroundTheory.Heights₂.Heights.ConeIntegralMass.full GroundTheory.Heights₂.Heights.ChowDegreePos.proof GroundTheory.Heights₂.Heights.AutoClose.ConeFubini GroundTheory.Heights₂.Heights.AutoClose.FsLogAverage GroundTheory.Heights₂.Heights.FsLogMeasurable.proof
