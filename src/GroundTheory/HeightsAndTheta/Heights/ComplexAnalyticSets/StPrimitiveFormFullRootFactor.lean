module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedIffRootFull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AnalyticGerm
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

def PrimitiveFormFullRootFactor.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∃ (W : Set (σ → ℂ)) (B : Set (Fin d → ℂ)) (C E : (Fin d → ℂ) → ℂ → ℂ),
        IsOpen W ∧ w ∈ W ∧ IsOpen B ∧ A w ∈ B ∧
        (∀ t ∈ B, ∀ T : ℂ, AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => C u.1 u.2) (t, T) ∧
          AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => E u.1 u.2) (t, T)) ∧
        (∀ t ∈ B, ∀ T : ℂ, C t T * E t T = T ^ N + ∑ j, a j t * T ^ (j : ℕ)) ∧
        ∀ t ∈ B, δ t ≠ 0 → ∀ τ : ℂ, τ ^ N + ∑ j, a j t * τ ^ (j : ℕ) = 0 →
          (C t τ = 0 ↔ PrimitiveFormRootFull X W A ℓ δ q t τ) ∧
          (E t τ = 0 ↔ ¬ PrimitiveFormRootFull X W A ℓ δ q t τ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
