import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkAesmTsum

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

section Alg

variable {G : Type*} [Group G] {Γ : Subgroup G} {φ : G → ℂ}

theorem rrka_Kab_symm (hsa : ∀ z, φ z⁻¹ = star (φ z)) (x y : G) : rrk_Kab Γ φ y x = rrk_Kab Γ φ x y := by
  unfold rrk_Kab
  rw [← (Equiv.inv Γ).tsum_eq (fun γ : Γ => ‖φ (y⁻¹ * (γ : G) * x)‖ₑ)]
  refine tsum_congr fun γ => ?_
  show ‖φ (y⁻¹ * ((γ⁻¹ : Γ) : G) * x)‖ₑ = _
  have e : y⁻¹ * ((γ⁻¹ : Γ) : G) * x = (x⁻¹ * (γ : G) * y)⁻¹ := by simp [mul_assoc]
  rw [e, hsa, enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]


theorem rrka_Kab_smul (δ : Γ) (x y : G) : rrk_Kab Γ φ ((δ : G) * y) x = rrk_Kab Γ φ y x := by
  unfold rrk_Kab
  rw [← (Equiv.mulLeft δ).tsum_eq (fun γ : Γ => ‖φ (((δ : G) * y)⁻¹ * (γ : G) * x)‖ₑ)]
  refine tsum_congr fun γ => ?_
  show ‖φ (((δ : G) * y)⁻¹ * ((δ * γ : Γ) : G) * x)‖ₑ = _
  have e : ((δ : G) * y)⁻¹ * ((δ * γ : Γ) : G) * x = y⁻¹ * (γ : G) * x := by simp [mul_assoc]
  rw [e]


end Alg

section Meas

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable {μ : Measure G} {Γ : Subgroup G} [Countable Γ] {D : Set G} {φ : G → ℂ}

theorem rrka_meas_Kab_right (hφm : Measurable φ) (x : G) : Measurable fun y => rrk_Kab Γ φ x y :=
  Measurable.tsum fun γ => (hφm.comp (measurable_const_mul (x⁻¹ * (γ : G)))).enorm

theorem rrka_lint [μ.IsMulLeftInvariant] (h : rr_FD μ Γ D) (hφm : Measurable φ) (hsa : ∀ z, φ z⁻¹ = star (φ z)) (x : G) :
    ∫⁻ y, ‖φ (x⁻¹ * y)‖ₑ * rrk_Kab Γ φ y x ∂μ = ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ := by
  rw [(rr_isFD h).lintegral_eq_tsum'']
  have e : ∀ δ : Γ, ∫⁻ y in D, ‖φ (x⁻¹ * (δ • y))‖ₑ * rrk_Kab Γ φ (δ • y) x ∂μ =
      ∫⁻ y in D, ‖φ (x⁻¹ * (δ : G) * y)‖ₑ * rrk_Kab Γ φ x y ∂μ := by
    intro δ
    refine lintegral_congr fun y => ?_
    rw [Subgroup.smul_def, smul_eq_mul, rrka_Kab_smul, rrka_Kab_symm hsa, ← mul_assoc]
  rw [tsum_congr e, ← lintegral_tsum (μ := μ.restrict D)
    (f := fun (δ : Γ) y => ‖φ (x⁻¹ * (δ : G) * y)‖ₑ * rrk_Kab Γ φ x y) (fun δ =>
    ((hφm.comp (measurable_const_mul (x⁻¹ * (δ : G)))).enorm.mul (rrka_meas_Kab_right hφm x)).aemeasurable)]
  refine lintegral_congr fun y => ?_
  rw [ENNReal.tsum_mul_right, sq]
  rfl



end Meas

end Formalism.MainNotions.LeviCoordinates

end
