module

public import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.GoodLat
public import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
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

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

open Formalism.L2.Th1.H

def HeisU : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B : AddSubgroup V), IsHerm H →
    IsSemiChar H A α → IsSemiChar H B α → IsBichar (cU H A B) ∧ IsHeis (cU H A B) (wA H α A) (wB H α B)

def InterSelf : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ : AddSubgroup V), IsHerm H →
    IsSemiChar H Λ α → ∀ θ ∈ fixedBy H α Λ, inter H α Λ Λ θ = θ

def MovesU : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ₀ Λ₁ : AddSubgroup V), IsHerm H →
    IsSemiChar H A α → IsSemiChar H B α → GoodLat H α A B Λ₀ → GoodLat H α A B Λ₁ → relIdx Λ₀ Λ₁ ≠ 0 →
    ∀ θ ∈ fixedBy H α Λ₀, ∀ Xi : Sch (cU H A B) (Λ₀.addSubgroupOf A) →ₗ[ℂ] (V → ℂ),
      IsXi (cU H A B) (wA H α A) (wB H α B) (Λ₀.addSubgroupOf A) θ Xi →
      ∃ h : ind ((Λ₁.addSubgroupOf A : AddSubgroup A) : Set A) ∈ Sch (cU H A B) (Λ₀.addSubgroupOf A),
        0 < volA A Λ₀ Λ₁ ∧
        inter H α Λ₀ Λ₁ θ = (((Real.sqrt (volA A Λ₀ Λ₁))⁻¹ : ℝ) : ℂ) • Xi ⟨_, h⟩

def MovesComposeU : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ₀ Λ₁ Λ₂ : AddSubgroup V), IsHerm H →
    IsSemiChar H A α → IsSemiChar H B α → GoodLat H α A B Λ₀ → GoodLat H α A B Λ₁ → GoodLat H α A B Λ₂ →
    relIdx Λ₀ Λ₁ ≠ 0 → relIdx Λ₁ Λ₂ ≠ 0 → relIdx Λ₀ Λ₂ ≠ 0 →
    ∀ θ ∈ fixedBy H α Λ₀, inter H α Λ₁ Λ₂ (inter H α Λ₀ Λ₁ θ) = inter H α Λ₀ Λ₂ θ

def GenModelXi : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₀ : AddSubgroup V) (M ι : Type)
    (Λ : ι → AddSubgroup V) (Y : ι → Set M) (vol : ι → ℝ), IsHerm H →
    ∀ θ ∈ fixedBy H α Λ₀,
    (∀ s : Finset ι, ∃ (A B : AddSubgroup V) (φ : A → M), IsSemiChar H A α ∧ IsSemiChar H B α ∧
      GoodLat H α A B Λ₀ ∧ ∀ i ∈ s, GoodLat H α A B (Λ i) ∧ relIdx Λ₀ (Λ i) ≠ 0 ∧
        (∀ a : A, (a : V) ∈ Λ i ↔ φ a ∈ Y i) ∧ vol i = volA A Λ₀ (Λ i)) →
    ∃ Xi : (M → ℂ) →ₗ[ℂ] (V → ℂ), ∀ i, Xi (Set.indicator (Y i) 1) = ((Real.sqrt (vol i) : ℝ) : ℂ) • inter H α Λ₀ (Λ i) θ

end Formalism.L2.PairingIndexBounds.Mv
