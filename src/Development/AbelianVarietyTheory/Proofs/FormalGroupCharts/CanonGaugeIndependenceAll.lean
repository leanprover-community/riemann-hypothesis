module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GaugeExp
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AxisPderivComp
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeSubIsBiadd
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermExpAddAndEvConst
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SecondOrderMonomial
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.WickVanishOfHalf
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.G2Assumption
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.NabTrans
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.TruncatedExpSecondEqFull

@[expose] public section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem gaugeExp_holds : GaugeExpSt :=
  GE.gauge_exp_identity germ_expAdd_and_evConst.1 germ_expAdd_and_evConst.2 canonGauge_sub_isBiadd
    quadDeriv_of_biadditive HalfIdentity.halfSt

theorem canonGauge_independence_all : AdmissibilitySecond ∧ GaugeExpSt ∧ GaugeIndependenceColumns ∧ NabTransSt :=
  ⟨G2.galois_twist_preserves_siegel_bound germ_expAdd_and_evConst.1 germ_expAdd_and_evConst.2 canonGauge_sub_isBiadd
      quadDeriv_of_biadditive (wickVanish_of_half HalfIdentity.halfSt),
    gaugeExp_holds, WickVanishing.gauge_second_columns_of_exp gaugeExp_holds, WickVanishing.connection_translation_of_poly ChartTrans.transPolySt⟩

end GlobalTheory
