module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CobOn
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle

@[expose] public section

open GlobalTheory.KEdge GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KEdge

theorem edge_cup_props : ∀ (Γ : Type) [Group Γ] (N : ℕ) (Δ : Subgroup Γ) [Δ.Normal] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N),
  CobOn Δ x y η →
  (∀ σ, ∀ h ∈ Δ, ∀ h' ∈ Δ, edge x y η σ (h * h') = edge x y η σ h + edge x y η σ h') ∧
  (∀ σ τ, ∀ h ∈ Δ, edge x y η (σ * τ) h = edge x y η σ (τ * h * τ⁻¹) + edge x y η τ h) ∧
  (∀ σ ∈ Δ, ∀ h ∈ Δ, edge x y η σ h = 0) := by
  intro Γ _ N Δ hN x y η hC
  have hmul : ∀ (z : Γ →* Multiplicative (ZMod N)) (a b : Γ), (z (a * b)).toAdd = (z a).toAdd + (z b).toAdd := by
    intro z a b; rw [z.map_mul]; rfl
  have hconj : ∀ (z : Γ →* Multiplicative (ZMod N)) (s a : Γ), (z (s * a * s⁻¹)).toAdd = (z a).toAdd := by
    intro z s a
    rw [hmul, hmul, z.map_inv, toAdd_inv]; ring
  refine ⟨?_, ?_, ?_⟩
  · intro σ h hh h' hh'
    have m1 : σ * h * σ⁻¹ ∈ Δ := hN.conj_mem h hh σ
    have m2 : σ * h' * σ⁻¹ ∈ Δ := hN.conj_mem h' hh' σ
    have e1 := hC _ m1 _ m2
    have e2 := hC h hh h' hh'
    have g : σ * (h * h') * σ⁻¹ = (σ * h * σ⁻¹) * (σ * h' * σ⁻¹) := by group
    simp only [edge]
    rw [g, hmul x h h', hmul y h h']
    rw [hconj x, hconj y] at e1
    linear_combination e1 - e2
  · intro σ τ h _
    have g : σ * τ * h * (σ * τ)⁻¹ = σ * (τ * h * τ⁻¹) * σ⁻¹ := by group
    simp only [edge]
    rw [g, hmul x σ τ, hmul y σ τ, hconj x τ h, hconj y τ h]
    ring
  · intro σ hσ h hh
    have m1 : σ * h * σ⁻¹ ∈ Δ := hN.conj_mem h hh σ
    have e1 := hC _ m1 σ hσ
    have e2 := hC σ hσ h hh
    have g : σ * h * σ⁻¹ * σ = σ * h := by group
    rw [g, hconj x] at e1
    simp only [edge]
    linear_combination e2 - e1

end GlobalTheory.KEdge
