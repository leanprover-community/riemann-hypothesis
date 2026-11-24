module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepDualIsoOfCommonRepresentedFunctional
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

@[expose] public section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.cuspRep_dual_iso_of_common_represented_functional : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (s₁ s₂ : Op E a → Op E a), Function.Involutive s₁ → Function.Involutive s₂ → ∀ B₁ B₂ : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B₁ φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B₁ φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B₁ (π.op (.fin k) φ) (π.op (s₁ (.fin k)) ψ) = B₁ φ ψ) → (∀ k φ ψ, B₁ (π.op (.cpt k) φ) (π.op (s₁ (.cpt k)) ψ) = B₁ φ ψ) → (∀ X φ ψ, B₁ (π.op (.lie X) φ) ψ + B₁ φ (π.op (s₁ (.lie X)) ψ) = 0) → (∀ φ, (∀ ψ, B₂ φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B₂ φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B₂ (π.op (.fin k) φ) (π.op (s₂ (.fin k)) ψ) = B₂ φ ψ) → (∀ k φ ψ, B₂ (π.op (.cpt k) φ) (π.op (s₂ (.cpt k)) ψ) = B₂ φ ψ) → (∀ X φ ψ, B₂ (π.op (.lie X) φ) ψ + B₂ φ (π.op (s₂ (.lie X)) ψ) = 0) → ∀ ψ₁ ψ₂ : π.V, ψ₁ ≠ 0 → (∀ φ, B₁ φ ψ₁ = B₂ φ ψ₂) → ∃ S : π.V ≃ₗ[ℂ] π.V, ∀ o φ, S (π.op (s₁ o) φ) = π.op (s₂ o) (S φ) := by
  first | exact @GlobalTheory.ContraPair.iso_of_common_functional | exact GlobalTheory.ContraPair.iso_of_common_functional | (intros; apply GlobalTheory.ContraPair.iso_of_common_functional <;> assumption)
