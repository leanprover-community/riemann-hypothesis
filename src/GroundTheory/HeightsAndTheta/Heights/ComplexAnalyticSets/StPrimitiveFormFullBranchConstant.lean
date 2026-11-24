module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedIffRootFull
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

def PrimitiveFormFullBranchConstant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X W N' : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ)
    (δ : (Fin d → ℂ) → ℂ) (q : σ → Fin N → (Fin d → ℂ) → ℂ) (B O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ),
    IsOpen W → IsOpen N' → closure W ⊆ N' → (∀ i, AnalyticOnNhd ℂ (f i) N') →
    X ∩ N' = {z | z ∈ N' ∧ ∀ i, f i z = 0} →
    (∀ z ∈ X ∩ closure W, A z ∈ B → z ∈ W) →
    (∀ z ∈ X ∩ W, ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
    IsOpen B → (∀ j, AnalyticOnNhd ℂ (a j) B) → AnalyticOnNhd ℂ δ B → (∀ i j, AnalyticOnNhd ℂ (q i j) B) →
    IsOpen O → IsPreconnected O → O ⊆ B → (∀ s ∈ O, δ s ≠ 0) →
    (∀ s ∈ O, (Polynomial.X ^ N + ∑ j, Polynomial.C (a j s) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
    AnalyticOnNhd ℂ r O → (∀ s ∈ O, r s ^ N + ∑ j, a j s * r s ^ (j : ℕ) = 0) →
    ∀ s ∈ O, ∀ s' ∈ O,
      (PrimitiveFormRootFull X W A ℓ δ q s (r s) ↔ PrimitiveFormRootFull X W A ℓ δ q s' (r s'))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
