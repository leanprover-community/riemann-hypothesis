module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

def InterClass : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsSemiChar H Λ₂ α → ∀ F ∈ fixedBy H α Λ₁, ∀ x ∈ Λ₂, ∀ y ∈ Λ₂, y ∈ Λ₁ → ∀ z,
      α (x + y) * opU H (x + y) F z = α x * opU H x F z

def RepsExist : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Λ₁ Λ₂ : AddSubgroup V), relIdx Λ₁ Λ₂ ≠ 0 →
    (∃ S : Finset V, IsReps Λ₁ Λ₂ S) ∧ ∀ S : Finset V, IsReps Λ₁ Λ₂ S → S.card = relIdx Λ₁ Λ₂

def InterReps : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsSemiChar H Λ₂ α → ∀ F ∈ fixedBy H α Λ₁, ∀ S : Finset V, IsReps Λ₁ Λ₂ S → ∀ z,
      inter H α Λ₁ Λ₂ F z = ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ * sumU H α S F z

def InterFixed : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsSemiChar H Λ₂ α → relIdx Λ₁ Λ₂ ≠ 0 → ∀ F ∈ fixedBy H α Λ₁, inter H α Λ₁ Λ₂ F ∈ fixedBy H α Λ₂

def InterTh : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsHerm H →
    ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ), IsSemiChar H Λ₂ α → relIdx Λ₁ Λ₂ ≠ 0 →
      ∀ F ∈ Th H α Λ₁, inter H α Λ₁ Λ₂ F ∈ Th H α Λ₂

def IndexEq : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V),
    IsSelfDual H Λ₁ → IsSelfDual H Λ₂ → relIdx Λ₁ Λ₂ ≠ 0 → relIdx Λ₂ Λ₁ ≠ 0 → relIdx Λ₁ Λ₂ = relIdx Λ₂ Λ₁

def CharSum : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V),
    IsSelfDual H Λ₁ → IsSelfDual H Λ₂ → ∀ S : Finset V, IsReps Λ₂ Λ₁ S → ∀ y ∈ Λ₂,
      ∑ x ∈ S, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ))
        = by classical exact if y ∈ Λ₁ then (S.card : ℂ) else 0

def InterInv : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsSelfDual H Λ₁ → IsSelfDual H Λ₂ → IsSemiChar H Λ₁ α → IsSemiChar H Λ₂ α →
    relIdx Λ₁ Λ₂ ≠ 0 → relIdx Λ₂ Λ₁ ≠ 0 → ∀ F ∈ fixedBy H α Λ₁, ∀ z,
      inter H α Λ₂ Λ₁ (inter H α Λ₁ Λ₂ F) z = F z

def LineTransport : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsHerm H →
    ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsSelfDual H Λ₁ → IsSelfDual H Λ₂ → IsSemiChar H Λ₁ α → IsSemiChar H Λ₂ α →
    relIdx Λ₁ Λ₂ ≠ 0 → relIdx Λ₂ Λ₁ ≠ 0 → ∀ θ₁ ∈ Th H α Λ₁, θ₁ ≠ 0 → (∀ F ∈ Th H α Λ₁, ∃ c : ℂ, F = c • θ₁) →
      inter H α Λ₁ Λ₂ θ₁ ≠ 0 ∧ ∀ F ∈ Th H α Λ₂, ∃ c : ℂ, F = c • inter H α Λ₁ Λ₂ θ₁

def ThIsom : Prop :=
  ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] [FiniteDimensional ℂ W] (H : Sesq V) (H' : Sesq W) (g : V ≃ₗ[ℂ] W),
    IsIsom H H' (g : V →ₗ[ℂ] W) → ∀ (Λ : AddSubgroup V) (α' : W → ℂ) (G : W → ℂ),
      G ∈ Th H' α' (imgLat (g : V →ₗ[ℂ] W) Λ) ↔ (fun v => G (g v)) ∈ Th H (fun v => α' (g v)) Λ

end Formalism.L2.Th1.H
