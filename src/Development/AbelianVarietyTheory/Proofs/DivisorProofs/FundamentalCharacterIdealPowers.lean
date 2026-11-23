module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx

variable {p : ℕ} [Fact p.Prime]

theorem continuous_gAf_fst (G : HTGroup p) :
    @Continuous G.GAf (AfP p ⊗[ℚ] G.C) _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C))
      (fun g => (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)

theorem continuous_gAf_snd_inv (G : HTGroup p) :
    Continuous (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p)) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_val.comp (continuous_inv.comp (continuous_snd.comp continuous_subtype_val))

theorem exists_compact_of_isTest (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) (h₁ : G.GAf) :
    ∃ Q : Set G.GAf, IsCompact Q ∧ ∀ g, f (h₁⁻¹ * g * h₁) ≠ 0 → g ∈ Q := by
  obtain ⟨S, hS⟩ := hf.2.2.2
  have hK : IsCompact (L.K : Set G.GAf) := L.compact
  refine ⟨⋃ s ∈ S, (fun q : G.GAf × G.GAf => h₁ * (q.1 * s * q.2) * h₁⁻¹) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)),
    S.isCompact_biUnion fun s _ => (hK.prod hK).image (by fun_prop), fun g hg => ?_⟩
  obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, he⟩ := hS _ hg
  refine Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, ?_⟩
  show h₁ * (k₁ * s * k₂) * h₁⁻¹ = g
  rw [← he]; group

theorem exists_compact_toAfF : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (h₁ : G.GAf), ∃ (Ω : Set (AfP p ⊗[ℚ] G.C)) (Ω' : Set (AfP p)),
    @IsCompact _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)) Ω ∧ IsCompact Ω' ∧ ∀ y : grp G β,
    f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∈ Ω ∧
    algebraMap ℚ (AfP p) ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹) ∈ Ω' := by
  intro p _ G L f hf β x t hx h₁
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) (AfP p ⊗[ℚ] G.C)
  obtain ⟨Q, hQ, hmem⟩ := exists_compact_of_isTest G L f hf h₁
  refine ⟨(fun g : G.GAf => ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * x) '' Q,
    (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p)) '' Q,
    hQ.image ((continuous_const.mul (continuous_gAf_fst G)).mul continuous_const),
    hQ.image (continuous_gAf_snd_inv G), fun y hy => ⟨⟨_, hmem _ hy, ?_⟩, ⟨_, hmem _ hy, ?_⟩⟩⟩
  · show ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
      ((x * Units.map (inC G (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).1) * x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) :
        AfP p ⊗[ℚ] G.C) * x = _
    simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
  · show (((Units.map (algebraMap ℚ (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).2))⁻¹ : (AfP p)ˣ) : AfP p) = _
    rw [← map_inv, Units.coe_map, Units.val_inv_eq_inv_val]
    rfl

end GlobalTheory.LKCx
