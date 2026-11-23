module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates

open scoped InnerProductSpace

def WeakAdj {E H₁ H₂ : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (ι : E →ₗ[ℂ] H₁) (t : E →ₗ[ℂ] H₂) (f : H₂) (w : H₁) : Prop :=
  ∀ g : E, ⟪t g, f⟫_ℂ = ⟪ι g, w⟫_ℂ

def CVXStatement (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Prop :=
  ∀ K : ℕ → Set H, Antitone K → (∀ n, (K n).Nonempty) → (∀ n, IsClosed (K n)) →
    (∀ n, ∀ x ∈ K n, ∀ y ∈ K n, (2 : ℂ)⁻¹ • (x + y) ∈ K n) → Bornology.IsBounded (K 0) →
    ∃ x : H, ∀ n, x ∈ K n

def RieszOnRangeStatement (E H : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ (θ : E →ₗ[ℂ] H) (ℓ : E →ₗ[ℂ] ℂ) (A : ℝ), 0 ≤ A →
    (∀ e : E, ‖ℓ e‖ ^ 2 ≤ A * ‖θ e‖ ^ 2) →
    ∃ u ∈ (LinearMap.range θ).topologicalClosure, ‖u‖ ^ 2 ≤ A ∧ ∀ e : E, ⟪u, θ e⟫_ℂ = ℓ e

def SplitStatement (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] : Prop :=
  ∀ (ι : E →ₗ[ℂ] H₁) (t : E →ₗ[ℂ] H₂) (K : Submodule ℂ H₂), IsClosed (K : Set H₂) →
    LinearMap.range t ≤ K → ∀ (f : H₂) (w : H₁), WeakAdj ι t f w →
    ∃ f₁ f₂ : H₂, f = f₁ + f₂ ∧ f₁ ∈ K ∧ f₂ ∈ Kᗮ ∧ WeakAdj ι t f₁ w ∧ WeakAdj ι t f₂ 0

def OntoWithBoundStatement (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] : Prop :=
  ∀ (G : H₁ →ₗ[ℂ] H₂) (Gs : H₂ →ₗ[ℂ] H₁) (θ : E →ₗ[ℂ] H₁) (Q : Submodule ℂ H₂) (c : ℝ), 0 < c →
    (∀ u ∈ Q, ∀ x : H₁, ⟪Gs u, x⟫_ℂ = ⟪u, G x⟫_ℂ) →
    (∀ u ∈ Q, ∀ e : E, c * ‖u‖ ^ 2 ≤ ‖Gs u + θ e‖ ^ 2) →
    ∀ f ∈ Q, ∃ h : H₁, (∀ u ∈ Q, ⟪u, G h⟫_ℂ = ⟪u, f⟫_ℂ) ∧ (∀ e : E, ⟪h, θ e⟫_ℂ = 0) ∧
      c * ‖h‖ ^ 2 ≤ ‖f‖ ^ 2

end ReciprocityTheory.L2DbarEstimates
