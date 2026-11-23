module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartChoiceAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartLengthAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartNormAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartNormSep
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartPointSeparable
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartResidueDegreeAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeClosedPoint
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsLocalSectionLengthSum
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionCycleReduced
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionLengthSum
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvdOfForallEmultiplicityLe
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.InhabitedChartFracSeparable
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartChoiceAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartFracSeparable
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartFreeParAlgIndep
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartLengthAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartNormAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartParAlgebraic
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartPointSeparable
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartResidueDegreeAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowDegreeClosedPoint
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormBirationalAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PClosedPointChartField
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PClosedPointConeCoord
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PLocalSectionLengthSum
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PNormOfDividedFormSep
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPiQuotCokerFiniteLength
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSectionComponents
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSectionLengthSum
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormMultiHomog
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimComponent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
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

open GroundTheory.Heights₂.Heights

theorem GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ObjectsChow_ChowDegreeClosedPoint : GroundTheory.Heights₂.Heights.ObjectsChow.ChowDegreeClosedPoint.Statement :=
  @GroundTheory.Heights₂.Heights.ObjectsChow.ChowDegreeClosedPoint.proof GroundTheory.Heights₂.Heights.ObjectsChow.ClosedPointChartField.proof GroundTheory.Heights₂.Heights.ObjectsChow.ClosedPointConeCoord.proof

theorem GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.NormOfDividedFormSep : GroundTheory.Heights₂.Heights.NormOfDividedFormSep.Statement :=
  @GroundTheory.Heights₂.Heights.NormOfDividedFormSep.proof GroundTheory.Heights₂.Heights.NormFormEval.full GroundTheory.Heights₂.Heights.NormFormDvd.full GroundTheory.Heights₂.Heights.PrimeMapFractionRing.full

theorem GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartFreeParAlgIndep : GroundTheory.Heights₂.Heights.ChartFreeParAlgIndep.Statement :=
  @GroundTheory.Heights₂.Heights.ChartFreeParAlgIndep.proof GroundTheory.Heights₂.Heights.ChartParAlgebraic.proof

theorem GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartPointSeparable : GroundTheory.Heights₂.Heights.ChartPointSeparable.Statement :=
  @GroundTheory.Heights₂.Heights.ChartPointSeparable.proof GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartFreeParAlgIndep

theorem GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartFracSeparable : GroundTheory.Heights₂.Heights.ChartFracSeparable.Statement :=
  @GroundTheory.Heights₂.Heights.ChartFracSeparable.proof GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartPointSeparable

theorem GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartNormAlgClosed : GroundTheory.Heights₂.Heights.ChartNormAlgClosed.Statement :=
  @GroundTheory.Heights₂.Heights.ChartNormAlgClosed.proof GroundTheory.Heights₂.Heights.IncIdealBelow.full GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.full GroundTheory.Heights₂.Heights.LocalizationPrimeDVR.full GroundTheory.Heights₂.Heights.ChartFinite.full GroundTheory.Heights₂.Heights.ChartFracSeparableInhabited.chartLocDomain GroundTheory.Heights₂.Heights.ChartFirstGroupPrime.full GroundTheory.Heights₂.Heights.ChartFirstGroupDvd.full GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.NormOfDividedFormSep GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartFracSeparable

theorem GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.LocalSectionLengthSum : GroundTheory.Heights₂.Heights.LocalSectionLengthSum.Statement :=
  @GroundTheory.Heights₂.Heights.LocalSectionLengthSum.proof GroundTheory.Heights₂.Heights.PiQuotCokerFiniteLength.proof

theorem GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.SectionLengthSum : GroundTheory.Heights₂.Heights.SectionLengthSum.Statement :=
  @GroundTheory.Heights₂.Heights.SectionLengthSum.proof GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.LocalSectionLengthSum

namespace GlobalTheory.CompanionTheory.Ar.Short.ChowClosing

theorem chartResidueDegreeAlgClosed_closed : ChartResidueDegreeAlgClosed.Statement :=
  ChartResidueDegreeAlgClosed.proof ChowFormBirationalAlgClosed.proof ChartFinite.full ChartKernel.full
    SectionPerfect.coneDimOfChowForm_full ConeDimComponent.proof_closed
    SectionPerfect.chowFormExists_full IncidenceGeneric.full ChartLocalOrder.full

theorem chartLengthAlgClosed_closed : ChartLengthAlgClosed.Statement :=
  ChartLengthAlgClosed.proof SpecFirstMemIncIdeal.full ChartFinite.full LengthFiniteAlgebra.full
    ChartMaxIdeals.full ChartLocalOrder.full chartResidueDegreeAlgClosed_closed

theorem chartChoiceAlgClosed_closed : ChartChoiceAlgClosed.Statement :=
  ChartChoiceAlgClosed.proof SectionPerfect.incIdealPrime_full chowFormMultiHomog

theorem sectionCycleReduced_closed : SectionCycleReduced.Statement :=
  sectionCycleReduced_of SectionComponents.proof_closed GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.SectionLengthSum

end GlobalTheory.CompanionTheory.Ar.Short.ChowClosing

namespace GlobalTheory.CompanionTheory.Ar.Short

end GlobalTheory.CompanionTheory.Ar.Short
