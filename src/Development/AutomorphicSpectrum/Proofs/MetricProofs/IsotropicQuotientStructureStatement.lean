module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicQuotientStructure
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

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.isotropic_quotient_structure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsSaturated I → IsIsoSub R₀.form I → ∃ (g' k : ℕ) (Λ' : Type) (_ : AddCommGroup Λ') (_ : Module (𝓞 E) Λ') (e : Fin k → Λ) (form' : Λ' →ₗ[ℤ] Λ' →ₗ[ℤ] ℤ) (π : Λ → Λ'), k + g' = g ∧ (∀ x', ∃ x, (∀ y ∈ I, R₀.form x y = 0) ∧ π x = x') ∧ ∀ R : RiemLat E g Λ, R.form = R₀.form → LinearIndependent ℂ (fun i => R.P (e i)) ∧ Submodule.span ℂ (R.P '' I) = Submodule.span ℂ (Set.range fun i => R.P (e i)) ∧ ∀ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), Function.Surjective q → LinearMap.ker q = Submodule.span ℂ (R.P '' I) → ∃ R' : RiemLat E g' Λ', R'.form = form' ∧ (∀ x, (∀ y ∈ I, R.form x y = 0) → R'.P (π x) = q (R.P x)) ∧ ∀ x y, (∀ v ∈ I, R.ip (R.P v) x = 0) → R'.ip (q x) (q y) = R.ip x y := by
  exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.QuotLat.exists_univ_quot
