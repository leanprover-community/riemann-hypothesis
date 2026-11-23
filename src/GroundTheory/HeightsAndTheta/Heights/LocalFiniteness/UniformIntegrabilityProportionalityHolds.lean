module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartConeLength
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisorComponents
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StLelongWeightDiff
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.OfLeaves
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAdmissibleAE
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAdmissibleAENrm
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBallVolume
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFubini
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PEvalSpecFirst
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerAverageSplit
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerIntegrand
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSphereMeanFubini
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSphereMeanLinearBall
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartConeLength
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDehomIdeal
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorComponents
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartSectionNotMem
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeRingLaurent
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongWeightDiff
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

theorem GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorComponents : GroundTheory.Heights₂.Heights.Targets.ChartDivisorComponents.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.ChartDivisorComponents.proof GroundTheory.Heights₂.Heights.Targets.ChartSectionNotMem.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.Targets_LelongWeightDiff : GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact

theorem GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartConeLength : GroundTheory.Heights₂.Heights.Targets.ChartConeLength.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.ChartConeLength.proof GroundTheory.Heights₂.Heights.Targets.ConeRingLaurent.proof GroundTheory.Heights₂.Heights.Targets.ChartDehomIdeal.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.MahlerAverageSplit : GroundTheory.Heights₂.Heights.MahlerAverageSplit.Statement :=
  @GroundTheory.Heights₂.Heights.MahlerAverageSplit.proof GroundTheory.Heights₂.Heights.MahlerIntegrand.proof GroundTheory.Heights₂.Heights.SphereMeanFubini.proof GroundTheory.Heights₂.Heights.EvalSpecFirst.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.ConeFubini : GroundTheory.Heights₂.Heights.ConeFubini.Statement :=
  @GroundTheory.Heights₂.Heights.ConeFubini.proof GroundTheory.Heights₂.Heights.BallVolume.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.SphereMeanLinearBall : GroundTheory.Heights₂.Heights.SphereMeanLinearBall.Statement :=
  @GroundTheory.Heights₂.Heights.SphereMeanLinearBall.proof GroundTheory.Heights₂.Heights.SphereMeanLinear.full

theorem GroundTheory.Heights₂.Heights.AutoClose.AdmissibleAENrm : GroundTheory.Heights₂.Heights.AdmissibleAENrm.Statement :=
  @GroundTheory.Heights₂.Heights.AdmissibleAENrm.proof GroundTheory.Heights₂.Heights.AdmissibleAE.proof
