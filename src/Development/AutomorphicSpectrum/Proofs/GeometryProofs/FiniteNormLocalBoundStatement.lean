module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormLocalBound
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLineGenOn

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.T.finite_norm_local_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c), (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t) → ∃ ρ : HeightOneSpectrum (𝓞 c.F) → ℝ, ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 c.F)) (π : c.F), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) → HasFinNorm U τ φ p κ (ρ la * Real.log ‖κ π‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.FinPlace.exists_rho | exact GlobalTheory.CompanionTheory.Ar.Br.FinPlace.exists_rho | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.FinPlace.exists_rho <;> assumption)
