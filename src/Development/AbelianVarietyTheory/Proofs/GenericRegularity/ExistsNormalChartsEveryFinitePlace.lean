module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteIntegralChartCoverFlagSpaceStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsNormalChartsOfCoveringChartsStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRefinedCoveringChartFamilyStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Valuation.AlgebraInstances
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem isDiscreteValuationRing_valuationSubring_place {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) : IsDiscreteValuationRing (la.valuation K).valuationSubring :=
  (la.valuation K).valuationSubring_isDiscreteValuationRing

theorem exists_sCharts : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → IntDiagUnit Xo c → ∀ la : HeightOneSpectrum (𝓞 c.F), ModelAt Xo c la → (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ := by
  intro hST E _ _ _ H Dw l Xo c hEv hDiag la hM
  obtain ⟨Y, hY⟩ := hM
  have := isDiscreteValuationRing_valuationSubring_place la

  obtain ⟨J, hJ, P, hP⟩ := GlobalTheory.T.exists_finite_integral_chart_cover_flagSpace hST E H Dw l Xo c hEv.bc (la.valuation c.F).valuationSubring Y hY
  have := hJ
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.exists_normal_charts_of_covering_charts E H Dw l Xo c hEv hDiag la J P hP
  refine ⟨⟨S, hS⟩, fun a n m ws hws hnz => ?_⟩

  obtain ⟨J', hJ', P', hP', hF⟩ := GlobalTheory.T.exists_refined_covering_chart_family E H Dw l Xo c hEv _ _ J P hP a n m ws hws hnz
  have := hJ'
  obtain ⟨S', hS', hW⟩ := GlobalTheory.T.exists_normal_charts_of_covering_charts E H Dw l Xo c hEv hDiag la J' P' hP'
  exact ⟨S', hW m ws hF, hS'⟩

end GlobalTheory.Reg
