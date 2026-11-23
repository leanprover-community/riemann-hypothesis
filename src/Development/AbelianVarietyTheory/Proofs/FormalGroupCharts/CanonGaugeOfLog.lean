module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeOfSteps
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.DerivationInnerOfSeparabilityElement
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.EqZeroOfAdditiveOfPderiv
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsActionGauge
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGaugeFirstLaw
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGaugeOfSymmetry
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalCompApplyEqMvPowerSeriesSubst
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSeriesSubstPointsStandardThree
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormallyUnramifiedOfIsReduced
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvGermEvThreePoints
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvRegaugedSecondLawFamily
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem canonGauge_of_log : LogSt → CanonGaugeSt := fun hlog =>
  have hcob := FormalCocycle.exists_coboundary_of_symm_cocycle hlog ChartInv.exists_isInvPair
  have huniq := AdditiveSeries.eq_zero_of_additive_of_pderiv
  canonGauge_of_steps exists_formalBiext_map exists_regauge
    (GaugeFirstLaw.exists_gauge_first_law hcob huniq)
    (SecondLawGauge.exists_gauge_second_law hcob huniq)
    (ActionGauge.exists_action_gauge
      (derivation_inner_of_reduced_order SepIdem.exists_separability_element))
    SymGauge.exists_gauge_of_symmetry

end GlobalTheory
