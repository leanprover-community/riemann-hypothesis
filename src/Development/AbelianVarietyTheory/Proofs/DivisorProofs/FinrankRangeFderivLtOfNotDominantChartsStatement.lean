module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeFderivLtOfNotDominantCharts
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.finrank_range_fderiv_lt_of_not_dominant_charts : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (A : FinHolAtlas D (CxPts p σ)) (A' : FinHolAtlas D (CxPts q σ)), IsAlgAtlas A → IsAlgAtlas A' → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) ≠ genericPoint X → ∀ j l, ∀ y ∈ (A'.chart j).target, PtsOver.map π hπ (spMap σ) ((A'.chart j).symm y) ∈ (A.chart l).source → Module.finrank ℂ (LinearMap.range (fderiv ℂ (A.chart l ∘ PtsOver.map π hπ (spMap σ) ∘ (A'.chart j).symm) y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) < D := by
  first | exact @GlobalTheory.finrank_range_fderiv_lt_of_not_dominant | exact GlobalTheory.finrank_range_fderiv_lt_of_not_dominant | (intros; apply GlobalTheory.finrank_range_fderiv_lt_of_not_dominant <;> assumption)
