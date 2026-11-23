module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.HermitianMetricLogNormFormula
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hermitian_metric_log_norm_formula : ∀ (k E : Type) [Field k] [NumberField k] [Field E] [NumberField E] (τ : E →+* k) (N : LogNorms k) (ρ : k) (a r : E) (p q d : ℕ) (n n' : (k →+* ℂ) → ℝ) (x : ℝ) (t t' : Nat.Primes → E), ρ ≠ 0 → a ≠ 0 → 0 < d → r ^ 2 = -(d : E) → -(∑ s, Real.log (n s)) / Module.finrank ℚ k = x → -(∑ s, Real.log (n' s)) / Module.finrank ℚ k = x → (∀ s, N.inf s = Real.log ‖s ρ‖ + ((p : ℝ) / 2 * (Real.log (n s) + Real.log d / 2) - (q : ℝ) / 2 * (Real.log (n' s) + Real.log d / 2)) + Real.log ‖s (τ a)‖ / 2) → (∀ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t' ℓ)‖ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖) → (∀ (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]), Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖ = -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite → (∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j + q * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖ - q * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((q : ℝ) - p) * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (τ r)‖)) → N.IsAdelic ∧ N.deg = ((p : ℝ) - q) / 2 * (x - Real.log (rootDiscr E) + Real.log (Real.sqrt d)) + q * (2 * Real.log (Real.sqrt d) - Real.log (rootDiscr E)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.deg_eq_of_local_two_curves | exact GlobalTheory.CompanionTheory.Ar.Fl.deg_eq_of_local_two_curves | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.deg_eq_of_local_two_curves <;> assumption)
