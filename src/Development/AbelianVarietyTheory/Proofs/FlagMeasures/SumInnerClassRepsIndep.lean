module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.RepresentationTheory.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem sum_inner_classReps_indep : ∀ (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* ℂˣ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Representation ℂ Gi W), (∀ h v w, ⟪π h v, π h w⟫_ℂ = ⟪v, w⟫_ℂ) → (∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) → ∀ (C C' : Type) [Fintype C] [Fintype C'] (s : C → Gf) (s' : C' → Gf), (∀ h : Gf, ∃! c, ∃ (γ : Γ) (κ : K), h = ιf γ * s c * (κ : Gf)) → (∀ h : Gf, ∃! c, ∃ (γ : Γ) (κ : K), h = ιf γ * s' c * (κ : Gf)) → ∀ φ φ' : Gf → W, (∀ (γ : Γ) (x : Gf) (κ : K), φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) → (∀ (γ : Γ) (x : Gf) (κ : K), φ' (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ' x)) → ∑ c, ⟪φ (s c), φ' (s c)⟫_ℂ = ∑ c, ⟪φ (s' c), φ' (s' c)⟫_ℂ := by
  intro Γ Gi Gf _ _ _ ιi ιf K ψ W _ _ π hπ hψ C C' _ _ s s' hs hs' φ φ' hφ hφ'
  have hf : ∀ (γ : Γ) (x : Gf) (κ : K),
      ⟪φ (ιf γ * x * κ), φ' (ιf γ * x * κ)⟫_ℂ = ⟪φ x, φ' x⟫_ℂ := by
    intro γ x κ
    rw [hφ, hφ', inner_smul_left, inner_smul_right, hπ, ← mul_assoc]
    have hn : ‖(((ψ κ)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, hψ κ, inv_one]
    have : (starRingEnd ℂ) (((ψ κ)⁻¹ : ℂˣ) : ℂ) * (((ψ κ)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [RCLike.conj_mul, hn]; simp
    rw [this, one_mul]
  obtain ⟨g, hg⟩ : ∃ g : C → C', ∀ c, ∃ (γ : Γ) (κ : K), s c = ιf γ * s' (g c) * (κ : Gf) :=
    ⟨fun c => (hs' (s c)).exists.choose, fun c => (hs' (s c)).exists.choose_spec⟩
  have hbij : Function.Bijective g := by
    constructor
    · intro c1 c2 h
      obtain ⟨γ1, κ1, h1⟩ := hg c1
      obtain ⟨γ2, κ2, h2⟩ := hg c2
      rw [h] at h1
      refine (hs (s c2)).unique ?_ ⟨1, 1, by simp⟩
      refine ⟨γ2 * γ1⁻¹, κ1⁻¹ * κ2, ?_⟩
      rw [h2, h1]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · intro c'
      obtain ⟨c, ⟨γ, κ, h⟩, -⟩ := hs (s' c')
      refine ⟨c, (hs' (s c)).unique (hg c) ⟨γ⁻¹, κ⁻¹, ?_⟩⟩
      rw [h]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
  refine Fintype.sum_bijective g hbij _ _ (fun c => ?_)
  obtain ⟨γ, κ, h⟩ := hg c
  have := hf γ (s' (g c)) κ
  rw [← h] at this
  exact this

end GlobalTheory
