module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

lemma resLE_self_preimage_image_eq {Z Z₁ : Scheme.{0}} (e₁ : Z₁ ⟶ Z) (V : Z.Opens)
    (W : V.toScheme.Opens) :
    (e₁ ⁻¹ᵁ V).ι ''ᵁ ((e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl) ⁻¹ᵁ W) = e₁ ⁻¹ᵁ (V.ι ''ᵁ W) := by
  rw [Scheme.Hom.resLE_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr (fun x hx => V.ι_image_le W hx)

lemma resLE_self_app_eq {Z Z₁ : Scheme.{0}} (e₁ : Z₁ ⟶ Z) (V : Z.Opens) (W : V.toScheme.Opens)
    (a b : Γ(V.toScheme, W))
    (h : (e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl).app W a = (e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl).app W b) :
    e₁.app (V.ι ''ᵁ W) a = e₁.app (V.ι ''ᵁ W) b := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE] at h
  have hS := resLE_self_preimage_image_eq e₁ V W
  have key := Scheme.Hom.appLE_map' (f := e₁) (U := V.ι ''ᵁ W)
    (e := le_refl (e₁ ⁻¹ᵁ (V.ι ''ᵁ W))) (i := hS.symm)
  rw [Scheme.Hom.appLE_eq_app] at key
  rw [← key]
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact congrArg _ h

theorem cover_and_joint_inj_restrict : ∀ (Z Z₁ Z₂ : Scheme.{0}) (e₁ : Z₁ ⟶ Z) (e₂ : Z₂ ⟶ Z),
    (∀ z : Z, (∃ z₁, e₁ z₁ = z) ∨ ∃ z₂, e₂ z₂ = z) →
    (∀ (W : Z.Opens) (a b : Γ(Z, W)), e₁.app W a = e₁.app W b → e₂.app W a = e₂.app W b → a = b) →
    ∀ V : Z.Opens, (∀ z : V.toScheme, (∃ z₁, e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl z₁ = z) ∨
      ∃ z₂, e₂.resLE V (e₂ ⁻¹ᵁ V) le_rfl z₂ = z) ∧
    ∀ (W : V.toScheme.Opens) (a b : Γ(V.toScheme, W)),
      (e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl).app W a = (e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl).app W b →
      (e₂.resLE V (e₂ ⁻¹ᵁ V) le_rfl).app W a = (e₂.resLE V (e₂ ⁻¹ᵁ V) le_rfl).app W b → a = b := by
  intro Z Z₁ Z₂ e₁ e₂ hcov hinj V
  refine ⟨fun z => ?_, fun W a b h₁ h₂ =>
    hinj _ a b (resLE_self_app_eq e₁ V W a b h₁) (resLE_self_app_eq e₂ V W a b h₂)⟩
  rcases hcov z.1 with ⟨z₁, hz⟩ | ⟨z₂, hz⟩
  · refine Or.inl ⟨⟨z₁, show e₁ z₁ ∈ V from hz ▸ z.2⟩, Subtype.ext ?_⟩
    rw [Scheme.Hom.coe_resLE_apply]; exact hz
  · refine Or.inr ⟨⟨z₂, show e₂ z₂ ∈ V from hz ▸ z.2⟩, Subtype.ext ?_⟩
    rw [Scheme.Hom.coe_resLE_apply]; exact hz

end GlobalTheory
