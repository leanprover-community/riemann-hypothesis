module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChart
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChartPointTrdeg
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsDerivSpanTrdeg
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFreeParAlgIndep
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsGenericFormsKer
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSecPointSeparable
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PAffineChartTrdeg
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimOfChowForm
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealDim
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Assembly
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.OfChartPointSecPointSpecChart
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChartPointTrdeg
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PDerivSpanTrdeg
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenSecSeparable
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenericFormsKer
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecPointSeparable
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecChart
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

namespace GroundTheory.Heights₂.Heights.Vertical

private theorem coneDim₃ : GroundTheory.Heights₂.Heights.ConeDimOfChowForm.Statement :=
  GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof
    (GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full
      GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof)
    GroundTheory.Heights₂.Heights.IncIdealPrime.full

theorem ChartPointTrdeg.full : ChartPointTrdeg.Statement :=
  ChartPointTrdeg.proof coneDim₃ GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof
theorem SpecChart.full : SpecChart.Statement := SpecChart.proof
theorem GenericFormsKer.full : GenericFormsKer.Statement := GenericFormsKer.proof
theorem DerivSpanTrdeg.full : DerivSpanTrdeg.Statement := DerivSpanTrdeg.proof

theorem SecPointSeparable.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) :
    SecPointSeparable.Statement :=
  SecPointSeparable.proof GenericFormsKer.full DerivSpanTrdeg.full h

theorem GenSecSeparable.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) :
    GenSecSeparable.Statement :=
  GenSecSeparable.proof SecAlgFinite.full GenSecDomain.full ChartPointTrdeg.full
    (SecPointSeparable.of_freeParAlgIndep h)

theorem ChowFormSectionVertical.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) :
    ChowFormSectionVertical.Statement :=
  ChowFormSectionVertical.of_chartPoint_secPoint_specChart ChartPointTrdeg.full
    (SecPointSeparable.of_freeParAlgIndep h) SpecChart.full

end GroundTheory.Heights₂.Heights.Vertical
