module

public import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut
public import Development.EtaleCohomology.CohomologicalPurity.LeafCoordPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafEtPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafLocPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafNbhdPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafPickPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafPolyPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafRankPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafSecPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafShrinkPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafSpanPf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace LateralTheory.Fin.LeafChart
theorem etale_chart_localization_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafLoc := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafLoc_of
theorem etale_chart_shrinking_open_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafShrink := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafShrink_of
theorem etale_chart_conormal_rank_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafRank := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafRank_of
theorem etale_chart_generator_choice_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafPick := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafPick_of
theorem etale_chart_ideal_span_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafSpan := by
  apply LateralTheory.CohomologicalPurity.LeafSpanPf.LeafSpan_of
theorem etale_chart_etaleness_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafEt := by
  apply LateralTheory.CohomologicalPurity.LeafEtPf.LeafEt_of
theorem etale_chart_coordinate_functions_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafCoord := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafCoord_of <;> first | exact etale_chart_conormal_rank_property_holds | exact etale_chart_generator_choice_property_holds | exact etale_chart_ideal_span_property_holds | exact etale_chart_etaleness_property_holds
theorem etale_chart_section_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafSec := by
  apply LateralTheory.CohomologicalPurity.LeafSecPf.LeafSec_of
theorem etale_chart_polynomial_algebra_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafPoly := by
  apply LateralTheory.CohomologicalPurity.LeafPolyPf.LeafPoly_of
theorem etale_chart_neighborhood_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafNbhd := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafNbhd_of <;> first | exact etale_chart_section_property_holds | exact etale_chart_polynomial_algebra_property_holds
theorem etale_coordinate_chart_existence : LateralTheory.CohomologicalPurity.LeafChart := by
  apply LateralTheory.CohomologicalPurity.ChartCut.goal_of <;> first | exact etale_chart_localization_property_holds | exact etale_chart_shrinking_open_property_holds | exact etale_chart_conormal_rank_property_holds | exact etale_chart_generator_choice_property_holds | exact etale_chart_ideal_span_property_holds | exact etale_chart_etaleness_property_holds | exact etale_chart_coordinate_functions_property_holds | exact etale_chart_section_property_holds | exact etale_chart_polynomial_algebra_property_holds | exact etale_chart_neighborhood_property_holds
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafChart := etale_coordinate_chart_existence
end LateralTheory.Fin.LeafChart
