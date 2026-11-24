module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AnalyticGerm
public import Mathlib.FieldTheory.Separable
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormMinimalFactorPoints.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ n + ∑ j, b j (A z) * ℓ z ^ (j : ℕ) = 0) ∧
        (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
          (Polynomial.X ^ n + ∑ j, Polynomial.C (b j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) ∧
        ∀ U ∈ 𝓝 w, ∀ᶠ y in 𝓝 (A w), δ y ≠ 0 → ∀ τ : ℂ, τ ^ n + ∑ j, b j y * τ ^ (j : ℕ) = 0 →
          (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) ∈ X ∩ U ∧
            A (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = y ∧
            ℓ (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = τ

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
