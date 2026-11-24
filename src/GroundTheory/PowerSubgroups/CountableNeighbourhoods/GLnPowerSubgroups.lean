module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Field.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Constructions

@[expose] public section

namespace GroundTheory.Variant₂.N1

open NumberField

section Splitting

variable {G P : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup P] [TopologicalSpace P]

def centralSplitting (φ : G →* P) (hφ : Continuous φ) (s : P →* G) (hs : Continuous s)
    (hsφ : ∀ p, φ (s p) = p) (hc : ∀ p g, s p * g = g * s p) (H : Subgroup G)
    (hH : ∀ g, g ∈ H ↔ φ g = 1) : G ≃ₜ* H × P where
  toFun g := (⟨g * (s (φ g))⁻¹, (hH _).2 (by rw [map_mul, map_inv, hsφ, mul_inv_cancel])⟩, φ g)
  invFun x := (x.1 : G) * s x.2
  left_inv g := by simp
  right_inv x := by
    obtain ⟨⟨h, hh⟩, p⟩ := x
    have h1 : φ h = 1 := (hH h).1 hh
    have h2 : φ (h * s p) = p := by rw [map_mul, h1, hsφ, one_mul]
    refine Prod.ext (Subtype.ext ?_) h2
    simp [h2]
  map_mul' g g' := by
    have hci : ∀ p g, (s p)⁻¹ * g = g * (s p)⁻¹ := fun p g => by
      rw [← map_inv]; exact hc p⁻¹ g
    refine Prod.ext (Subtype.ext ?_) (map_mul φ g g')
    simp only [map_mul, mul_inv_rev]
    rw [hci (φ g') (s (φ g))⁻¹]
    calc g * g' * ((s (φ g))⁻¹ * (s (φ g'))⁻¹)
        = g * (g' * (s (φ g))⁻¹) * (s (φ g'))⁻¹ := by simp only [mul_assoc]
      _ = g * ((s (φ g))⁻¹ * g') * (s (φ g'))⁻¹ := by rw [hci]
      _ = g * (s (φ g))⁻¹ * (g' * (s (φ g'))⁻¹) := by simp only [mul_assoc]
  continuous_toFun :=
    (Continuous.subtype_mk (continuous_id.mul ((hs.comp hφ).inv)) _).prodMk hφ
  continuous_invFun := (continuous_subtype_val.comp continuous_fst).mul (hs.comp continuous_snd)

end Splitting

section Section

variable {K : Type*} [Field K]


variable [NumberField K]





end Section

end GroundTheory.Variant₂.N1
