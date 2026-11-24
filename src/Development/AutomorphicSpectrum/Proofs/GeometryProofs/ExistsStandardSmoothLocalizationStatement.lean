module

public import Mathlib.RingTheory.Smooth.StandardSmooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStandardSmoothLocalization
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes

theorem _root_.GlobalTheory.T.exists_standard_smooth_localization : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (hA : IsArithVar (mCoordIdeal y) (e + 1)) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0), ∃ s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩), s ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SegreChart.exists_away_standardSmooth | exact GlobalTheory.CompanionTheory.Ar.SegreChart.exists_away_standardSmooth | (intros; apply GlobalTheory.CompanionTheory.Ar.SegreChart.exists_away_standardSmooth <;> assumption)
