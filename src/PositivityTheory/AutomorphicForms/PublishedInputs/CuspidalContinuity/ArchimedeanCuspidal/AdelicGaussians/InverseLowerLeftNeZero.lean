import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.HeisenbergLowerCommuteMiddle

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace Ad3.GA.CtvP

open Ad3.GA.unipotentTranslateContinuity

local notation "𝔞" => algebraMap ℚ 𝔸[ℚ]

theorem W_shift {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) {W : G3 → ℂ} (hW : W ∈ V) {D L X : G3}
    {a b z : 𝔸[ℚ]} (hDL : D * L = uni a b z * D) (g : G3) :
    W (D * (L * X * g)) = (adelicChar ℚ (a + z) : ℂ) * W (D * (X * g)) := by
  have e : D * (L * X * g) = uni a b z * (D * (X * g)) := by
    calc D * (L * X * g) = D * L * (X * g) := by simp only [mul_assoc]
      _ = uni a b z * D * (X * g) := by rw [hDL]
      _ = uni a b z * (D * (X * g)) := mul_assoc _ _ _
  rw [e, hV.psi W hW]






theorem out_rel (γ : GL (Fin 2) ℚ) : γ * ((Quotient.mk _ γ : NQ).out)⁻¹ ∈ nU :=
  QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk _ γ : NQ)))


theorem inv_rel_q (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (γ⁻¹).val i 0 * γ.val 0 j + (γ⁻¹).val i 1 * γ.val 1 j = if i = j then 1 else 0 := by
  have := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℚ => X i j) (Units.inv_mul γ)
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using this


theorem inverse_lower_left_ne_zero (γ : GL (Fin 2) ℚ) (h10 : γ.val 1 0 ≠ 0) : (γ⁻¹).val 1 0 ≠ 0 := by
  intro hN
  have r10 := inv_rel_q γ 1 0
  have r11 := inv_rel_q γ 1 1
  rw [hN, zero_mul, zero_add] at r10 r11
  simp only [Fin.isValue, one_ne_zero, if_false, if_true, mul_eq_zero] at r10 r11
  rcases r10 with h | h
  · rw [h, zero_mul] at r11; exact zero_ne_one r11
  · exact h10 h

theorem diag_ne_zero (γ : GL (Fin 2) ℚ) (h10 : γ.val 1 0 = 0) :
    γ.val 0 0 ≠ 0 ∧ γ.val 1 1 ≠ 0 := by
  have hd := det_ne_zero2 γ
  rw [h10, mul_zero, sub_zero] at hd
  exact mul_ne_zero_iff.1 hd

theorem inv_upper (γ : GL (Fin 2) ℚ) (h10 : γ.val 1 0 = 0) :
    (γ⁻¹).val 1 0 = 0 ∧ (γ⁻¹).val 0 0 * γ.val 0 0 = 1 := by
  have r10 := inv_rel_q γ 1 0
  have r00 := inv_rel_q γ 0 0
  rw [h10, mul_zero, add_zero] at r10 r00
  simp only [Fin.isValue, one_ne_zero, if_false, if_true, mul_eq_zero] at r10 r00
  exact ⟨r10.resolve_right (diag_ne_zero γ h10).1, r00⟩




def chiH (ξ : Fin 2 → ℚ) (y : Fin 3 → 𝔸[ℚ]) : ℂ :=
  (adelicChar ℚ (-(𝔞 (ξ 0) * y 0 + 𝔞 (ξ 1) * y 1)) : ℂ)

theorem continuous_chiH (ξ : Fin 2 → ℚ) : Continuous (chiH ξ) :=
  continuous_subtype_val.comp (continuous_adelicChar.comp (by fun_prop))

theorem continuous_hH : Continuous fun y : Fin 3 → 𝔸[ℚ] => lowM (y 0) * uni 0 (y 1) (y 2) :=
  (continuous_lowM (continuous_apply 0)).mul
    (continuous_uni continuous_const (continuous_apply 1) (continuous_apply 2))

def fU (W : G3 → ℂ) (g : G3) (ξ : Fin 2 → ℚ) (γ : GL (Fin 2) ℚ) (y : Fin 3 → 𝔸[ℚ]) : ℂ :=
  W (dia (e1 γ) * (lowM (y 0) * uni 0 (y 1) (y 2) * g)) * chiH ξ y

def fV (W : G3 → ℂ) (g : G3) (ξ : Fin 2 → ℚ) (γ : GL (Fin 2) ℚ) (y : Fin 3 → 𝔸[ℚ]) : ℂ :=
  W (dia (e2 γ * sw) * (lowM (y 0) * uni 0 (y 1) (y 2) * g)) * chiH ξ y

theorem continuous_fU {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) (hC : ContW) {W : G3 → ℂ}
    (hW : W ∈ V) (g : G3) (ξ : Fin 2 → ℚ) (γ : GL (Fin 2) ℚ) : Continuous (fU W g ξ γ) :=
  ((hC V hV W hW).comp (continuous_const.mul (continuous_hH.mul continuous_const))).mul
    (continuous_chiH ξ)

theorem continuous_fV {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) (hC : ContW) {W : G3 → ℂ}
    (hW : W ∈ V) (g : G3) (ξ : Fin 2 → ℚ) (γ : GL (Fin 2) ℚ) : Continuous (fV W g ξ γ) :=
  ((hC V hV W hW).comp (continuous_const.mul (continuous_hH.mul continuous_const))).mul
    (continuous_chiH ξ)

section shifts

variable {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) {W : G3 → ℂ} (hW : W ∈ V) (g : G3)
  (ξ : Fin 2 → ℚ) (γ : GL (Fin 2) ℚ)
include hV hW

theorem shiftU_alt_alt (y : Fin 3 → 𝔸[ℚ]) (s : 𝔸[ℚ]) :
    fU W g ξ γ (y + Pi.single 2 s) = (adelicChar ℚ (𝔞 (γ.val 1 1) * s) : ℂ) * fU W g ξ γ y := by
  have e0 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 0 = y 0 := by simp
  have e1 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 1 = y 1 := by simp
  have e2 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 2 = y 2 + s := by simp
  simp only [fU, chiH]
  rw [e0, e1, e2, heisenberg_lower_commute_corner, W_shift hV hW (GL2_embed_commute_corner γ s)]
  exact psi_comb (by ring) _

theorem shiftU_alt (h11 : γ.val 1 1 = 0) (y : Fin 3 → 𝔸[ℚ]) (s : 𝔸[ℚ]) :
    fU W g ξ γ (y + Pi.single 1 s) =
      (adelicChar ℚ (𝔞 (γ.val 1 0 - ξ 1) * s) : ℂ) * fU W g ξ γ y := by
  have e0 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 0 = y 0 := by simp
  have e1 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 1 = y 1 + s := by simp
  have e2 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 2 = y 2 := by simp
  simp only [fU, chiH]
  rw [e0, e1, e2, heisenberg_lower_commute_middle, W_shift hV hW (GL2_embed_commute_middle γ s (y 0 * s))]
  refine psi_comb ?_ _
  rw [h11, map_sub, map_zero]
  ring

theorem shiftU_c (h11 : γ.val 1 1 = 0) (y : Fin 3 → 𝔸[ℚ]) (s : 𝔸[ℚ]) :
    fU W g ξ γ (y + Pi.single 0 s) =
      (adelicChar ℚ (𝔞 (γ.val 0 1 / γ.val 1 0 - ξ 0) * s) : ℂ) * fU W g ξ γ y := by
  have e0 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 0 = y 0 + s := by simp
  have e1 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 1 = y 1 := by simp
  have e2 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 2 = y 2 := by simp
  simp only [fU, chiH]
  rw [e0, e1, e2, hH_c, W_shift hV hW (dU_c γ h11 s)]
  refine psi_comb ?_ _
  rw [map_sub]
  ring

theorem shiftV_alt (y : Fin 3 → 𝔸[ℚ]) (s : 𝔸[ℚ]) :
    fV W g ξ γ (y + Pi.single 2 s) = (adelicChar ℚ (𝔞 ((γ⁻¹).val 1 0) * s) : ℂ) * fV W g ξ γ y := by
  have e0 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 0 = y 0 := by simp
  have e1 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 1 = y 1 := by simp
  have e2 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 2 = y 2 + s := by simp
  simp only [fV, chiH]
  rw [e0, e1, e2, heisenberg_lower_commute_corner, W_shift hV hW (GL2_swap_embed_commute_corner γ s)]
  exact psi_comb (by ring) _

theorem shiftV_c (y : Fin 3 → 𝔸[ℚ]) (s : 𝔸[ℚ]) :
    fV W g ξ γ (y + Pi.single 0 s) =
      (adelicChar ℚ (𝔞 ((γ⁻¹).val 0 0 - ξ 0) * s) : ℂ) * fV W g ξ γ y := by
  have e0 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 0 = y 0 + s := by simp
  have e1 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 1 = y 1 := by simp
  have e2 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 2 = y 2 := by simp
  simp only [fV, chiH]
  rw [e0, e1, e2, hH_c, W_shift hV hW (dV_c γ s)]
  refine psi_comb ?_ _
  rw [map_sub]
  ring

theorem shiftV_alt_alt (h10 : γ.val 1 0 = 0) (y : Fin 3 → 𝔸[ℚ]) (s : 𝔸[ℚ]) :
    fV W g ξ γ (y + Pi.single 1 s) =
      (adelicChar ℚ (𝔞 (γ.val 0 0 / γ.val 1 1 - ξ 1) * s) : ℂ) * fV W g ξ γ y := by
  have e0 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 0 = y 0 := by simp
  have e1 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 1 = y 1 + s := by simp
  have e2 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 2 = y 2 := by simp
  simp only [fV, chiH]
  rw [e0, e1, e2, heisenberg_lower_commute_middle, W_shift hV hW (GL2_swap_embed_commute_middle γ h10 s (y 0 * s))]
  refine psi_comb ?_ _
  rw [map_sub]
  ring

end shifts

theorem intU {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) (hC : ContW) {W : G3 → ℂ} (hW : W ∈ V)
    {ξ : Fin 2 → ℚ} (hξ1 : ξ 1 ≠ 0) (g : G3) (γ : GL (Fin 2) ℚ) :
    ∫ y in vecDomain ℚ (Fin 3), W (dia (e1 γ) * (lowM (y 0) * uni 0 (y 1) (y 2) * g)) * chiH ξ y
      ∂vecMeasure ℚ (Fin 3) =
      if γ.val 1 1 = 0 ∧ γ.val 1 0 = ξ 1 ∧ γ.val 0 1 = ξ 0 * ξ 1 then W (dia (e1 γ) * g) else 0 := by
  show ∫ y in vecDomain ℚ (Fin 3), fU W g ξ γ y ∂vecMeasure ℚ (Fin 3) = _
  have hc := continuous_fU hV hC hW g ξ γ
  split_ifs with hs
  · obtain ⟨h11, h10, h01⟩ := hs
    have hr : γ.val 0 1 / γ.val 1 0 - ξ 0 = 0 := by
      rw [h01, h10, mul_div_cancel_right₀ _ hξ1, sub_self]
    rw [setIntegral_eq_of_shift]
    · simp [fU, chiH, lowM_zero, uni_zero]
    · intro y i s
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
      rcases hi with rfl | rfl | rfl
      · rw [shiftU_c hV hW g ξ γ h11, hr, map_zero, zero_mul, psi_zero, one_mul]
      · rw [shiftU_alt hV hW g ξ γ h11, h10, sub_self, map_zero, zero_mul, psi_zero, one_mul]
      · rw [shiftU_alt_alt hV hW g ξ γ, h11, map_zero, zero_mul, psi_zero, one_mul]
  · by_cases h11 : γ.val 1 1 = 0
    · by_cases h10 : γ.val 1 0 = ξ 1
      · have h01 : γ.val 0 1 ≠ ξ 0 * ξ 1 := fun h => hs ⟨h11, h10, h⟩
        refine setIntegral_eq_zero_of_shift hc 0 ?_ (shiftU_c hV hW g ξ γ h11)
        rw [h10, sub_ne_zero, Ne, div_eq_iff hξ1]
        exact h01
      · exact setIntegral_eq_zero_of_shift hc 1 (sub_ne_zero.2 h10) (shiftU_alt hV hW g ξ γ h11)
    · exact setIntegral_eq_zero_of_shift hc 2 h11 (shiftU_alt_alt hV hW g ξ γ)

theorem intV {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) (hC : ContW) {W : G3 → ℂ} (hW : W ∈ V)
    {ξ : Fin 2 → ℚ} (g : G3) (γ : GL (Fin 2) ℚ) :
    ∫ y in vecDomain ℚ (Fin 3), W (dia (e2 γ * sw) * (lowM (y 0) * uni 0 (y 1) (y 2) * g)) *
      chiH ξ y ∂vecMeasure ℚ (Fin 3) =
      if γ.val 1 0 = 0 ∧ (γ⁻¹).val 0 0 = ξ 0 ∧ γ.val 0 0 / γ.val 1 1 = ξ 1 then
        W (dia (e2 γ * sw) * g) else 0 := by
  show ∫ y in vecDomain ℚ (Fin 3), fV W g ξ γ y ∂vecMeasure ℚ (Fin 3) = _
  have hc := continuous_fV hV hC hW g ξ γ
  split_ifs with hs
  · obtain ⟨h10, hN, hd⟩ := hs
    have hN10 := (inv_upper γ h10).1
    rw [setIntegral_eq_of_shift]
    · simp [fV, chiH, lowM_zero, uni_zero]
    · intro y i s
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
      rcases hi with rfl | rfl | rfl
      · rw [shiftV_c hV hW g ξ γ, hN, sub_self, map_zero, zero_mul, psi_zero, one_mul]
      · rw [shiftV_alt_alt hV hW g ξ γ h10, hd, sub_self, map_zero, zero_mul, psi_zero, one_mul]
      · rw [shiftV_alt hV hW g ξ γ, hN10, map_zero, zero_mul, psi_zero, one_mul]
  · by_cases h10 : γ.val 1 0 = 0
    · by_cases hN : (γ⁻¹).val 0 0 = ξ 0
      · have hd : γ.val 0 0 / γ.val 1 1 ≠ ξ 1 := fun h => hs ⟨h10, hN, h⟩
        exact setIntegral_eq_zero_of_shift hc 1 (sub_ne_zero.2 hd) (shiftV_alt_alt hV hW g ξ γ h10)
      · exact setIntegral_eq_zero_of_shift hc 0 (sub_ne_zero.2 hN) (shiftV_c hV hW g ξ γ)
    · exact setIntegral_eq_zero_of_shift hc 2 (inverse_lower_left_ne_zero γ h10) (shiftV_alt hV hW g ξ γ)

section reps

variable {ξ : Fin 2 → ℚ} (hξ0 : ξ 0 ≠ 0) (hξ1 : ξ 1 ≠ 0)

def gU : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, ξ 0 * ξ 1; ξ 1, 0] (by
    simp [Matrix.det_fin_two_of, hξ0, hξ1])

def gV : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(ξ 0)⁻¹, 0; 0, (ξ 0 * ξ 1)⁻¹] (by
    simp [Matrix.det_fin_two_of, hξ0, hξ1])








end reps

theorem final_eq {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) {W : G3 → ℂ} (hW : W ∈ V)
    {ξ : Fin 2 → ℚ} (hξ0 : ξ 0 ≠ 0) (hξ1 : ξ 1 ≠ 0) (γ δ : GL (Fin 2) ℚ)
    (hγ : γ.val 1 1 = 0 ∧ γ.val 1 0 = ξ 1 ∧ γ.val 0 1 = ξ 0 * ξ 1)
    (hδ : δ.val 1 0 = 0 ∧ δ.val 0 0 = (ξ 0)⁻¹ ∧ δ.val 1 1 = (ξ 0 * ξ 1)⁻¹) (g : G3) :
    W (dia (e1 γ) * g) = W (dia (e2 δ * sw) * g) := by
  obtain ⟨g11, g10, g01⟩ := hγ
  obtain ⟨d10, d00, d11⟩ := hδ
  set s : ℚˣ := Units.mk0 (ξ 0 * ξ 1) (mul_ne_zero hξ0 hξ1) with hs
  set a : ℚ := γ.val 0 0 / ξ 1 with ha
  set z : ℚ := -(ξ 0 * ξ 1 * δ.val 0 1) with hz
  set b : ℚ := -(a * (ξ 0 * ξ 1) * δ.val 0 1) with hb
  have hQ : e1 γ = uni a b z * (dg s s s * (e2 δ * sw)) := by
    apply Units.ext
    simp only [Units.val_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e1, e2, b1M, b2M, sw, uni, dg, s, a, b, z, Matrix.mul_apply, Fin.sum_univ_three, g11,
        g10, g01, d10, d00, d11] <;>
      first | ring1 | (field_simp; ring1) | field_simp
  set S : (𝔸[ℚ])ˣ := Units.map (algebraMap ℚ 𝔸[ℚ]).toMonoidHom s with hS
  have hdu : ∀ a b z : ℚ, dia (uni a b z) = uni (𝔞 a) (𝔞 b) (𝔞 z) := by
    intro a b z
    apply Units.ext
    rw [val_uni]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uni]
  have hdd : dia (dg s s s) = dg S S S := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg, S]
  have key : dia (e1 γ) * g = uni (𝔞 a) (𝔞 b) (𝔞 z) * (dg S S S * (dia (e2 δ * sw) * g)) := by
    have hm : dia (uni a b z * (dg s s s * (e2 δ * sw))) =
        dia (uni a b z) * (dia (dg s s s) * dia (e2 δ * sw)) := by
      simp only [dia, map_mul]
    rw [hQ, hm, hdu, hdd]
    simp only [mul_assoc]
  rw [key, hV.psi W hW, hV.cen W hW, ← map_add, psi_rat, one_mul]


end Ad3.GA.CtvP

namespace Ad3.GA



end Ad3.GA
