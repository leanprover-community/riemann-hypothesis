module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicInverseChartValue
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.holomorphic_inverse_chart_value : ∀ (e : ℕ) (X₁ X₂ V : Type) [TopologicalSpace X₁] [TopologicalSpace X₂] [NormedAddCommGroup V] [NormedSpace ℂ V] (A₁ : ReciprocityTheory.AnForm.M.FinHolAtlas e X₁) (A₂ : ReciprocityTheory.AnForm.M.FinHolAtlas e X₂) (π : X₁ → X₂) (inv : X₂ → X₁), ReciprocityTheory.AnForm.M.HoloMap A₁ A₂ π → ReciprocityTheory.AnForm.M.HoloMap A₂ A₁ inv → Function.Bijective π → (∀ x, inv (π x) = x) → ∀ (Φ : X₁ → V) (x : X₂) (j₁ : Fin A₁.n) (j₂ : Fin A₂.n), inv x ∈ (A₁.chart j₁).source → x ∈ (A₂.chart j₂).source → DifferentiableAt ℂ (fun v => Φ ((A₁.chart j₁).symm v)) (A₁.chart j₁ (inv x)) → (fderiv ℂ (fun v => Φ ((A₁.chart j₁).symm v)) (A₁.chart j₁ (inv x))).ker = ⊥ → (fderiv ℂ (fun v => Φ (inv ((A₂.chart j₂).symm v))) (A₂.chart j₂ x)).ker = ⊥ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ImmersionBiholo.ker_fderiv_comp_biholo | exact GlobalTheory.CompanionTheory.Ar.ImmersionBiholo.ker_fderiv_comp_biholo | (intros; apply GlobalTheory.CompanionTheory.Ar.ImmersionBiholo.ker_fderiv_comp_biholo <;> assumption)
