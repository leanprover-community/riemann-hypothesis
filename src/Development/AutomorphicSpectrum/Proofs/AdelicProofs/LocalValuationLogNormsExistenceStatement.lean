module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocalValuationLogNormsExistence
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.local_valuation_log_norms_existence : ∀ (K : Type) [Field K] [NumberField K] (r : (K →+* ℂ) → ℝ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ), (∀ (p : Nat.Primes) (κ : K →+* ℂ_[p]), ∃ (la : HeightOneSpectrum (𝓞 K)) (π : K), (∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1) ∧ la.valuation K π = WithZero.exp (-1 : ℤ)) ∧ (∃ N : LogNorms K, (∀ σ, N.inf σ = Real.log (r σ)) ∧ ∀ (p : Nat.Primes) (κ : K →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 K)) (π : K), (∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation K π = WithZero.exp (-1 : ℤ) → N.fin p κ = ρ la * Real.log ‖κ π‖) ∧ ∀ N : LogNorms K, (∀ σ, N.inf σ = Real.log (r σ)) → (∀ (p : Nat.Primes) (κ : K →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 K)) (π : K), (∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation K π = WithZero.exp (-1 : ℤ) → N.fin p κ = ρ la * Real.log ‖κ π‖) → (N.IsAdelic ↔ (Function.support ρ).Finite) ∧ (N.IsAdelic → N.deg = GlobalTheory.FlatLine.lineDeg r ρ) := by
  exact @GlobalTheory.CompanionTheory.Ar.Br.Dd.deg_dict
