module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicFamilyOfHoms
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric


theorem _root_.GlobalTheory.T.holomorphic_family_of_homs : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] (D : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension D k A] (σ : k →+* ℂ) (ψ₀ : A →+* ℂ), ψ₀.comp (algebraMap k A) = σ → ∃ Ψ : (Fin D → ℂ) → (A →+* ℂ), IsHolPts (ball 0 1) Ψ ∧ Ψ 0 = ψ₀ ∧ (∀ z ∈ ball (0 : Fin D → ℂ) 1, (Ψ z).comp (algebraMap k A) = σ) ∧ ∀ a : A, (∀ z ∈ ball (0 : Fin D → ℂ) 1, Ψ z a = 0) → a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ChartRing.exists_polydisc_chart | exact GlobalTheory.CompanionTheory.ChartRing.exists_polydisc_chart | (intros; apply GlobalTheory.CompanionTheory.ChartRing.exists_polydisc_chart <;> assumption)
