module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.RationalUnitsHaarCharacterOne
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lagrangian_invariant_functional_exists : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → ∀ L : Submodule F ((κ → F) × (κ → F)), (∀ w, w ∈ L ↔ ∀ w' ∈ L, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) → ∃ l ∈ (adeleClass F).adm κ, (∃ Φ ∈ schA F κ, l Φ ≠ 0) ∧ (∀ y ∈ Submodule.span (AdeleRing (𝓞 F) F) ((fun w : (κ → F) × (κ → F) => ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (w.1 i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (w.2 i)) : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))) '' L), ∀ Φ ∈ schA F κ, l (schr ψ y Φ) = l Φ) ∧ ∀ (s : ((κ → F) × (κ → F)) ≃ₗ[F] ((κ → F) × (κ → F))) (sA : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) →ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))) (T : Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)) (a : ℂ), (∀ w, sA (fun i => algebraMap F (AdeleRing (𝓞 F) F) (w.1 i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (w.2 i)) = (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((s w).1 i), fun i => algebraMap F (AdeleRing (𝓞 F) F) ((s w).2 i))) → (∀ w, s w ∈ L ↔ w ∈ L) → (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) → (∀ w, ∀ Φ ∈ schA F κ, T (schr ψ w Φ) = schr ψ (sA w) (T Φ)) → (∀ Φ ∈ schA F κ, thetaSum F (T Φ) = a * thetaSum F Φ) → ∀ Φ ∈ schA F κ, l (T Φ) = a * l Φ := by
  exact @GlobalTheory.CompanionTheory.ThetaAvg.theta_mean
