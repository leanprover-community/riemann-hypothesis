module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodGramComparisonBound
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.period_gram_comparison_bound : ∀ (n a₀ g r a : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ) (U : Fin r → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ) (π : Equiv.Perm (Fin n)) (ρ : ℝ), 0 < ρ → ρ ≤ 1 → (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) → LinearIndependent ℂ (fun k => U k 0) → (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < a ∧ t₀ (π.symm i) = 0) → ∃ ε c C : ℝ, 0 < ε ∧ ε ≤ ρ ∧ 0 < c ∧ 0 < C ∧ ∀ t : Fin n → ℂ, ‖t - t₀‖ < ε → ‖t‖ < 1 → HodgeMetric.uncentre t₀ ρ π t ∈ Flat.punct n a₀ 1 → ((HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹ - (c : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).PosSemidef ∧ (((C * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - (HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹).PosSemidef ∧ ∀ p q, ‖fderiv ℝ (fun t' => HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t') p q) t‖ ≤ C * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) / 2) := by
  exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.logBound_recentred
