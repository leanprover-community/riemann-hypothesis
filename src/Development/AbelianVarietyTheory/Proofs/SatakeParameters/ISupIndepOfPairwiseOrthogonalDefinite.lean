import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumEqConstMulPeterssonStatement

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem petersson_form_classSum_comparison :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n)
      (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ), GlobalTheory.CoefDuty.IsInvForm a β → ∃ B, GlobalTheory.CoefDuty.IsPetersson a B ∧
      ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (T : Finset (GAf L n)), GlobalTheory.CoefDuty.IsBounded J →
        (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) →
        GlobalTheory.CoefDuty.IsClassReps J T → ∃ c : ℝ, 0 < c ∧ ∀ f ∈ NG.TypeSp a.ρ J χ,
          ∀ f' ∈ NG.TypeSp a.ρ J χ, GlobalTheory.CoefDuty.classSum a β J T f f' = (c : ℂ) * B f f' :=
  GlobalTheory.T.class_sum_eq_const_mul_petersson

end GlobalTheory
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_classSum_eq_mul_invariantForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ), GlobalTheory.CoefDuty.IsInvForm a β → ∃ B, GlobalTheory.CoefDuty.IsPetersson a B ∧ ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (T : Finset (GAf L n)), GlobalTheory.CoefDuty.IsBounded J → (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → GlobalTheory.CoefDuty.IsClassReps J T → ∃ c : ℝ, 0 < c ∧ ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ f' ∈ NG.TypeSp a.ρ J χ, GlobalTheory.CoefDuty.classSum a β J T f f' = (c : ℂ) * B f f' := by
  atlas_forward_decl GlobalTheory.petersson_form_classSum_comparison
