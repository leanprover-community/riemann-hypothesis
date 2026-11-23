module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Matched
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchLift

theorem exists_ratio_unit : ∀ (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (O₁ O₂ : Y.Opens) (s₁ : ∀ k, Γ(Y, L.U k ⊓ O₁)ˣ) (s₂ : ∀ k, Γ(Y, L.U k ⊓ O₂)ˣ), GlobalTheory.PinchLift.GenOn L O₁ s₁ → GlobalTheory.PinchLift.GenOn L O₂ s₂ → ∃ r : Γ(Y, O₁ ⊓ O₂)ˣ, ∀ (T : Scheme.{0}) (f : T ⟶ Y) (t : T) (k : L.ι), f t ∈ L.U k → f t ∈ O₁ → f t ∈ O₂ → gm f t (O₁ ⊓ O₂) r = gm f t (L.U k ⊓ O₁) (s₁ k) * (gm f t (L.U k ⊓ O₂) (s₂ k))⁻¹ := by
  intro Y L hL O₁ O₂ s₁ s₂ h₁ h₂
  have hW : ∀ k, L.U k ⊓ (O₁ ⊓ O₂) ≤ O₁ ⊓ O₂ := fun k => inf_le_right
  have hc : O₁ ⊓ O₂ ≤ ⨆ k, L.U k ⊓ (O₁ ⊓ O₂) := fun y hy => by
    obtain ⟨k, hk⟩ := exists_chart hL y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk, hy⟩
  have i₁ : ∀ k, L.U k ⊓ (O₁ ⊓ O₂) ≤ L.U k ⊓ O₁ := fun k => inf_le_inf_left _ inf_le_left
  have i₂ : ∀ k, L.U k ⊓ (O₁ ⊓ O₂) ≤ L.U k ⊓ O₂ := fun k => inf_le_inf_left _ inf_le_right
  let u : ∀ k, Γ(Y, L.U k ⊓ (O₁ ⊓ O₂))ˣ := fun k => res (i₁ k) (s₁ k) * (res (i₂ k) (s₂ k))⁻¹
  have hu : ∀ (T : Scheme.{0}) (f : T ⟶ Y) (t : T) (k : L.ι), f t ∈ L.U k ⊓ (O₁ ⊓ O₂) →
      gm f t (L.U k ⊓ (O₁ ⊓ O₂)) (u k) = gm f t (L.U k ⊓ O₁) (s₁ k) * (gm f t (L.U k ⊓ O₂) (s₂ k))⁻¹ := by
    intro T f t k hy
    simp only [u, map_mul, map_inv, gm_res f t (i₁ k) hy, gm_res f t (i₂ k) hy]
  obtain ⟨r, hr⟩ := glue_unit (O₁ ⊓ O₂) (fun k => L.U k ⊓ (O₁ ⊓ O₂)) hW hc u (by
    intro k l y hy
    have hk : y ∈ L.U k ⊓ (O₁ ⊓ O₂) := hy.1
    have hl : y ∈ L.U l ⊓ (O₁ ⊓ O₂) := hy.2
    show gm (𝟙 Y) y (L.U k ⊓ (O₁ ⊓ O₂)) (u k) = gm (𝟙 Y) y (L.U l ⊓ (O₁ ⊓ O₂)) (u l)
    rw [hu Y (𝟙 Y) y k hk, hu Y (𝟙 Y) y l hl, h₁ k l y hk.1 hl.1 hk.2.1, h₂ k l y hk.1 hl.1 hk.2.2,
      ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div])
  refine ⟨r, fun T f t k hk ht₁ ht₂ => ?_⟩
  have hy : f t ∈ L.U k ⊓ (O₁ ⊓ O₂) := ⟨hk, ht₁, ht₂⟩
  rw [← gm_res f t (hW k) hy r, hr k, hu T f t k hy]

end GlobalTheory.PinchLift
