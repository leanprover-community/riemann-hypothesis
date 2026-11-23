module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem cocycle_isCoboundary_of_neg_central : ∀ (G : Type) [Group G] (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (ρ : G → V →ₗ[R] V), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → IsUnit (2 : R) → ∀ (S : Submodule R V), (∀ g, ∀ v ∈ S, ρ g v ∈ S) → ∀ (Δ : Subgroup G), Δ.Normal → (∀ δ ∈ Δ, ∀ v, ρ δ v = v) → ∀ c : G, (∀ v ∈ S, ρ c v = -v) → (∀ g, c * g * c⁻¹ * g⁻¹ ∈ Δ) → ∀ z : G → V, (∀ g, z g ∈ S) → (∀ g h, z (g * h) = ρ h (z g) + z h) → (∀ δ ∈ Δ, z δ = 0) → ∃ p ∈ S, ∀ g, z g = ρ g p - p := by
  intro G _ R _ V _ _ ρ hmul hone h2 S hS Δ hΔ hΔρ c hc hcomm z hzS hz hzΔ
  obtain ⟨u, hu⟩ := h2
  refine ⟨-((↑u⁻¹ : R) • z c), S.neg_mem (S.smul_mem _ (hzS c)), fun g => ?_⟩
  have key : ρ g (z c) + z g = -z g + z c := by
    have e1 : z (c * g) = z (g * c) := by
      have : c * g = (c * g * c⁻¹ * g⁻¹) * (g * c) := by group
      rw [this, hz, hzΔ _ (hcomm g), map_zero, zero_add]
    rw [hz, hz, hc _ (hzS g)] at e1
    exact e1
  have h2z : (2 : R) • z g = z c - ρ g (z c) := by
    rw [two_smul, ← sub_eq_zero]
    calc z g + z g - (z c - ρ g (z c)) = (ρ g (z c) + z g) - (-z g + z c) := by abel
      _ = 0 := sub_eq_zero.mpr key
  calc z g = ((↑u⁻¹ : R) * 2) • z g := by rw [← hu, Units.inv_mul, one_smul]
    _ = ρ g (-((↑u⁻¹ : R) • z c)) - -((↑u⁻¹ : R) • z c) := by
      rw [mul_smul, h2z, map_neg, map_smul, smul_sub]; abel

end GlobalTheory.KZ.H3
