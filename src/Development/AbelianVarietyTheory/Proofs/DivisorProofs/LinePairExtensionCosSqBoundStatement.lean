import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarDensityOfTransition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMeasureDensityExists
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveDens

theorem angleForm_alg (n : ℕ) (q P D H β β' L L' : ℂ) (a a' : ℝ) (ha : 0 < a) (ha' : 0 < a')
    (Qi dQi dv R dR : ℂ)
    (hQi : Qi = (((a * a')⁻¹ : ℝ) : ℂ))
    (hdQi : dQi = (((-((a * a') ^ 2)⁻¹ : ℝ) : ℂ)) *
      ((a : ℂ) * ((a' : ℂ) * starRingEnd ℂ β') + (a : ℂ) * starRingEnd ℂ β * (a' : ℂ)))
    (hdv : dv = q * starRingEnd ℂ q * dQi + (q * starRingEnd ℂ P + D * starRingEnd ℂ q) * Qi)
    (hR : R = starRingEnd ℂ q * (P - q * β') - q * (starRingEnd ℂ D - starRingEnd ℂ q * β))
    (hdR : dR = (starRingEnd ℂ q * (H - (q * L' + D * β')) + starRingEnd ℂ P * (P - q * β')) -
          (q * (starRingEnd ℂ H - (starRingEnd ℂ q * L + starRingEnd ℂ P * β)) +
            D * (starRingEnd ℂ D - starRingEnd ℂ q * β))) :
    ((((‖q‖ ^ 2 / (a * a')) ^ n : ℝ) : ℂ) * (R * dQi + dR * Qi) +
      (((n : ℝ) * (‖q‖ ^ 2 / (a * a')) ^ (n - 1) : ℝ) : ℂ) * dv * (R * Qi)).re =
    (n + 1) * (‖q‖ ^ 2 / (a * a')) ^ n * ((‖P - q * β'‖ ^ 2 - ‖D - q * starRingEnd ℂ β‖ ^ 2) / (a * a')) +
      (‖q‖ ^ 2 / (a * a')) ^ (n + 1) * (L.re - L'.re) := by
  subst hQi hdQi hdv hR hdR
  have hQ : (0:ℝ) < a * a' := mul_pos ha ha'
  have ha0 : a ≠ 0 := ha.ne'
  have ha0' : a' ≠ 0 := ha'.ne'
  obtain ⟨K, m, hK, hn⟩ : ∃ K m, K = (‖q‖ ^ 2 / (a * a')) ^ m ∧
      ((‖q‖ ^ 2 / (a * a')) ^ n = K * (‖q‖ ^ 2 / (a * a')) ∧
        ((n : ℝ) * (‖q‖ ^ 2 / (a * a')) ^ (n - 1)) = n * K ∧ (n:ℝ) ≠ 0 ∨
       (‖q‖ ^ 2 / (a * a')) ^ n = 1 ∧ ((n : ℝ) * (‖q‖ ^ 2 / (a * a')) ^ (n - 1)) = 0 ∧ n = 0) := by
    rcases n with _ | m
    · exact ⟨1, 0, by simp, Or.inr ⟨by simp, by simp, rfl⟩⟩
    · refine ⟨_, m, rfl, Or.inl ⟨pow_succ _ _, by simp, by positivity⟩⟩
  have hpow : (‖q‖ ^ 2 / (a * a')) ^ (n + 1) = (‖q‖ ^ 2 / (a * a')) ^ n * (‖q‖ ^ 2 / (a * a')) := pow_succ _ _
  rw [hpow]
  rcases hn with ⟨h1, h2, -⟩ | ⟨h1, h2, rfl⟩
  · rw [h1, h2]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
    field_simp
    ring
  · rw [h1]
    simp only [Nat.cast_zero, zero_mul, Complex.ofReal_zero, add_zero, zero_add, one_mul,
      Complex.ofReal_one]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
    field_simp
    ring

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem differentiableAt_del_apply_of_contDiffAt_two {f : E → ℂ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (w : E) : DifferentiableAt ℝ (fun x => del f x w) z := by
  have h := differentiableAt_fderiv_of_contDiffAt_two hf
  simp only [del_apply]
  exact ((h.clm_apply (differentiableAt_const _)).sub
    ((h.clm_apply (differentiableAt_const _)).const_smul Complex.I)).const_smul (1 / 2 : ℂ)

theorem re_dbar_angleForm (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E)
    (ha : ContDiffAt ℝ 2 a z) (ha' : ContDiffAt ℝ 2 a' z) (hq : ContDiffAt ℝ 2 q z)
    (h0 : 0 < a z) (h0' : 0 < a' z) :
    (dbar (angleForm n a a' q ξ) z ξ).re = (n + 1) * (‖q z‖ ^ 2 / (a z * a' z)) ^ n *
      ((‖del q z ξ - q z * del (fun x => (Real.log (a' x) : ℂ)) z ξ‖ ^ 2 -
        ‖dbar q z ξ - q z * dbar (fun x => (Real.log (a x) : ℂ)) z ξ‖ ^ 2) / (a z * a' z)) +
      (‖q z‖ ^ 2 / (a z * a' z)) ^ (n + 1) *
        ((leviForm (fun x => Real.log (a x)) z ξ ξ).re -
          (leviForm (fun x => Real.log (a' x)) z ξ ξ).re) := by
  have hq1 : DifferentiableAt ℝ q z := hq.differentiableAt (by norm_num)
  have ha1 : DifferentiableAt ℝ a z := ha.differentiableAt (by norm_num)
  have ha1' : DifferentiableAt ℝ a' z := ha'.differentiableAt (by norm_num)
  have hαC : ContDiffAt ℝ 2 (fun x => (Real.log (a x) : ℂ)) z :=
    contDiffAt_ofReal_comp (ha.log h0.ne')
  have hαC' : ContDiffAt ℝ 2 (fun x => (Real.log (a' x) : ℂ)) z :=
    contDiffAt_ofReal_comp (ha'.log h0'.ne')
  have hqc : ContDiffAt ℝ 2 (fun x => starRingEnd ℂ (q x)) z :=
    (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.contDiffAt.comp z hq
  have dP := differentiableAt_del_apply_of_contDiffAt_two hq ξ
  have dPt := differentiableAt_del_apply_of_contDiffAt_two hqc ξ
  have dB := differentiableAt_del_apply_of_contDiffAt_two hαC ξ
  have dB' := differentiableAt_del_apply_of_contDiffAt_two hαC' ξ
  have dqc : DifferentiableAt ℝ (fun x => starRingEnd ℂ (q x)) z := hqc.differentiableAt (by norm_num)
  have daC : DifferentiableAt ℝ (fun x => (a x : ℂ)) z :=
    (contDiffAt_ofReal_comp ha).differentiableAt (by norm_num)
  have daC' : DifferentiableAt ℝ (fun x => (a' x : ℂ)) z :=
    (contDiffAt_ofReal_comp ha').differentiableAt (by norm_num)
  have hQ1 : DifferentiableAt ℝ (fun x => a x * a' x) z := ha1.mul ha1'
  have hQ0 : a z * a' z ≠ 0 := (mul_pos h0 h0').ne'
  have hv1 : DifferentiableAt ℝ (fun x => ‖q x‖ ^ 2 / (a x * a' x)) z :=
    ((hq1.norm_sq (𝕜 := ℂ)).mul (hQ1.inv hQ0)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by simp only [div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply])
  have dQi : DifferentiableAt ℝ (fun x => (((a x * a' x)⁻¹ : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z (hQ1.inv hQ0)
  have dW : DifferentiableAt ℝ (fun x => (((‖q x‖ ^ 2 / (a x * a' x)) ^ n : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z (hv1.pow n)
  have dR : DifferentiableAt ℝ (fun x => starRingEnd ℂ (q x) *
      (del q x ξ - q x * del (fun y => (Real.log (a' y) : ℂ)) x ξ) -
      q x * (del (fun y => starRingEnd ℂ (q y)) x ξ -
        starRingEnd ℂ (q x) * del (fun y => (Real.log (a y) : ℂ)) x ξ)) z :=
    (dqc.mul (dP.sub (hq1.mul dB'))).sub (hq1.mul (dPt.sub (dqc.mul dB)))
  have hG : angleForm n a a' q ξ = fun x =>
      (((‖q x‖ ^ 2 / (a x * a' x)) ^ n : ℝ) : ℂ) *
        ((starRingEnd ℂ (q x) * (del q x ξ - q x * del (fun y => (Real.log (a' y) : ℂ)) x ξ) -
            q x * (del (fun y => starRingEnd ℂ (q y)) x ξ -
              starRingEnd ℂ (q x) * del (fun y => (Real.log (a y) : ℂ)) x ξ)) *
          (((a x * a' x)⁻¹ : ℝ) : ℂ)) := by
    funext x
    rw [angleForm, map_sub, map_mul, dbar_ofReal (fun y => Real.log (a y)), Complex.conj_conj,
      ← del_conj]
    push_cast
    ring
  rw [dbar_ofReal (fun x => Real.log (a x)) z ξ, hG, dbar_mul dW (dR.fun_mul dQi) ξ, dbar_mul dR dQi ξ]
  beta_reduce
  have hW := dbar_ofReal_comp (h := fun s : ℝ => s ^ n) (hasDerivAt_pow n _) hv1 ξ
  beta_reduce at hW
  rw [hW, del_conj q z ξ]
  refine angleForm_alg n (q z) (del q z ξ) (dbar q z ξ) (ddbar q z ξ ξ)
    (del (fun x => (Real.log (a x) : ℂ)) z ξ) (del (fun x => (Real.log (a' x) : ℂ)) z ξ)
    (leviForm (fun x => Real.log (a x)) z ξ ξ) (leviForm (fun x => Real.log (a' x)) z ξ ξ)
    (a z) (a' z) h0 h0' _ _ _ _ _ rfl ?_ ?_ rfl ?_
  · have h1 := dbar_ofReal_comp (t := fun x => a x * a' x) (h := fun s : ℝ => s⁻¹)
      (hasDerivAt_inv (x := a z * a' z) hQ0) hQ1 ξ
    beta_reduce at h1
    have h2 : (fun x => ((a x * a' x : ℝ) : ℂ)) = fun x => (a x : ℂ) * (a' x : ℂ) := by
      funext x; push_cast; rfl
    have hda := dbar_ofReal_comp (h := Real.log) (Real.hasDerivAt_log h0.ne') ha1 ξ
    have hda' := dbar_ofReal_comp (h := Real.log) (Real.hasDerivAt_log h0'.ne') ha1' ξ
    rw [dbar_ofReal] at hda hda'
    have hz : (a z : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    have hz' : (a' z : ℂ) ≠ 0 := by exact_mod_cast h0'.ne'
    have e1 : dbar (fun x => (a x : ℂ)) z ξ =
        (a z : ℂ) * starRingEnd ℂ (del (fun x => (Real.log (a x) : ℂ)) z ξ) := by
      rw [hda]; push_cast; field_simp
    have e2 : dbar (fun x => (a' x : ℂ)) z ξ =
        (a' z : ℂ) * starRingEnd ℂ (del (fun x => (Real.log (a' x) : ℂ)) z ξ) := by
      rw [hda']; push_cast; field_simp
    rw [h1, h2, dbar_mul daC daC' ξ, e1, e2]
  · have h3 : (fun x => ((‖q x‖ ^ 2 / (a x * a' x) : ℝ) : ℂ)) =
        fun x => q x * starRingEnd ℂ (q x) * (((a x * a' x)⁻¹ : ℝ) : ℂ) := by
      funext x; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [h3, dbar_mul (hq1.fun_mul dqc) dQi ξ, dbar_mul hq1 dqc ξ, dbar_conj]
  · rw [dbar_sub (dqc.fun_mul (dP.fun_sub (hq1.fun_mul dB')))
        (hq1.fun_mul (dPt.fun_sub (dqc.fun_mul dB))),
      ContinuousLinearMap.sub_apply, dbar_mul dqc (dP.fun_sub (hq1.fun_mul dB')) ξ,
      dbar_mul hq1 (dPt.fun_sub (dqc.fun_mul dB)) ξ,
      dbar_sub dP (hq1.fun_mul dB'), dbar_sub dPt (dqc.fun_mul dB),
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      dbar_mul hq1 dB' ξ, dbar_mul dqc dB ξ, dbar_conj,
      ← ddbar_eq_dbar_del hq, ← ddbar_eq_dbar_del hqc, ← ddbar_eq_dbar_del hαC,
      ← ddbar_eq_dbar_del hαC', ddbar_conj hq, del_conj q z ξ]
    rfl

end GlobalTheory.CurveDens
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_angleForm_re_eq : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E), ContDiffAt ℝ 2 a z → ContDiffAt ℝ 2 a' z → ContDiffAt ℝ 2 q z → 0 < a z → 0 < a' z → (dbar (angleForm n a a' q ξ) z ξ).re = (n + 1) * (‖q z‖ ^ 2 / (a z * a' z)) ^ n * ((‖del q z ξ - q z * del (fun x => (Real.log (a' x) : ℂ)) z ξ‖ ^ 2 - ‖dbar q z ξ - q z * dbar (fun x => (Real.log (a x) : ℂ)) z ξ‖ ^ 2) / (a z * a' z)) + (‖q z‖ ^ 2 / (a z * a' z)) ^ (n + 1) * ((leviForm (fun x => Real.log (a x)) z ξ ξ).re - (leviForm (fun x => Real.log (a' x)) z ξ ξ).re) := by
  first | exact @GlobalTheory.CurveDens.re_dbar_angleForm | exact GlobalTheory.CurveDens.re_dbar_angleForm | (intros; apply GlobalTheory.CurveDens.re_dbar_angleForm <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CurveDens
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem angleForm_smul (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E) (c : ℂ) :
    angleForm n a a' q (c • ξ) z = c * angleForm n a a' q ξ z := by
  simp only [angleForm, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smulₛₗ, smul_eq_mul,
    map_sub, map_mul, Complex.conj_conj, RingHom.id_apply]
  ring

theorem contDiffAt_del_apply {q : E → ℂ} {z : E} (hq : ContDiffAt ℝ 2 q z) (ξ : E) :
    ContDiffAt ℝ 1 (fun x => del q x ξ) z ∧ ContDiffAt ℝ 1 (fun x => dbar q x ξ) z := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ q) z := hq.fderiv_right (by norm_num)
  have hv : ∀ w : E, ContDiffAt ℝ 1 (fun x => fderiv ℝ q x w) z := fun w =>
    h1.clm_apply contDiffAt_const
  constructor
  · simp only [del_apply, smul_eq_mul]
    exact contDiffAt_const.mul ((hv ξ).sub (contDiffAt_const.mul (hv _)))
  · simp only [dbar_apply, smul_eq_mul]
    exact contDiffAt_const.mul ((hv ξ).add (contDiffAt_const.mul (hv _)))

theorem contDiffAt_angleForm (n : ℕ) {a a' : E → ℝ} {q : E → ℂ} (ξ : E) {z : E}
    (ha : ContDiffAt ℝ 2 a z) (ha' : ContDiffAt ℝ 2 a' z) (hq : ContDiffAt ℝ 2 q z)
    (h0 : 0 < a z) (h0' : 0 < a' z) : ContDiffAt ℝ 1 (angleForm n a a' q ξ) z := by
  have hla : ContDiffAt ℝ 2 (fun x => (Real.log (a x) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (ha.log h0.ne')
  have hla' : ContDiffAt ℝ 2 (fun x => (Real.log (a' x) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (ha'.log h0'.ne')
  have hq1 : ContDiffAt ℝ 1 q z := hq.of_le (by norm_num)
  have hA : ContDiffAt ℝ 1 (fun x => a x * a' x) z := (ha.mul ha').of_le (by norm_num)
  have hA0 : a z * a' z ≠ 0 := (mul_pos h0 h0').ne'
  have hN : ContDiffAt ℝ 1 (fun x => ‖q x‖ ^ 2) z := hq1.norm_sq ℝ
  have hR : ContDiffAt ℝ 1 (fun x => (((‖q x‖ ^ 2 / (a x * a' x)) ^ n : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z ((hN.div hA hA0).pow n)
  have hD : ContDiffAt ℝ 1 (fun x => ((a x * a' x : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z hA
  have hconj : ∀ {f : E → ℂ}, ContDiffAt ℝ 1 f z →
      ContDiffAt ℝ 1 (fun x => starRingEnd ℂ (f x)) z :=
    fun hf => Complex.conjCLE.contDiff.contDiffAt.comp z hf
  have e1 := contDiffAt_del_apply hq ξ
  have e2 := contDiffAt_del_apply hla ξ
  have e3 := contDiffAt_del_apply hla' ξ
  have hD0 : ((a z * a' z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA0
  have key : ContDiffAt ℝ 1 (fun x => (((‖q x‖ ^ 2 / (a x * a' x)) ^ n : ℝ) : ℂ) *
      (starRingEnd ℂ (q x) * (del q x ξ - q x * del (fun x => (Real.log (a' x) : ℂ)) x ξ) -
        q x * starRingEnd ℂ (dbar q x ξ - q x * dbar (fun x => (Real.log (a x) : ℂ)) x ξ)) *
      (((a x * a' x : ℝ) : ℂ))⁻¹) z :=
    (hR.mul (((hconj hq1).mul (e1.1.sub (hq1.mul e3.1))).sub
      (hq1.mul (hconj (e1.2.sub (hq1.mul e2.2)))))).mul (hD.inv hD0)
  unfold angleForm
  simpa only [div_eq_mul_inv] using key

theorem angleForm_comp_holo (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E) (φ : E → E)
    (hφ : DifferentiableAt ℂ φ z) (ha : DifferentiableAt ℝ a (φ z))
    (ha' : DifferentiableAt ℝ a' (φ z)) (hq : DifferentiableAt ℝ q (φ z))
    (h0 : 0 < a (φ z)) (h0' : 0 < a' (φ z)) :
    angleForm n (fun x => a (φ x)) (fun x => a' (φ x)) (fun x => q (φ x)) ξ z =
      angleForm n a a' q (fderiv ℂ φ z ξ) (φ z) := by
  have hla : DifferentiableAt ℝ (fun y => (Real.log (a y) : ℂ)) (φ z) :=
    Complex.ofRealCLM.differentiableAt.comp _ (ha.log h0.ne')
  have hla' : DifferentiableAt ℝ (fun y => (Real.log (a' y) : ℂ)) (φ z) :=
    Complex.ofRealCLM.differentiableAt.comp _ (ha'.log h0'.ne')
  unfold angleForm
  rw [del_comp_holo (u := q) hq hφ, dbar_comp_holo (u := q) hq hφ,
    del_comp_holo (u := fun y => (Real.log (a' y) : ℂ)) hla' hφ,
    dbar_comp_holo (u := fun y => (Real.log (a y) : ℂ)) hla hφ]

theorem angleForm_props : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E), (∀ c : ℂ, angleForm n a a' q (c • ξ) z = c * angleForm n a a' q ξ z) ∧ (ContDiffAt ℝ 2 a z → ContDiffAt ℝ 2 a' z → ContDiffAt ℝ 2 q z → 0 < a z → 0 < a' z → ContDiffAt ℝ 1 (angleForm n a a' q ξ) z) ∧ ∀ φ : E → E, DifferentiableAt ℂ φ z → DifferentiableAt ℝ a (φ z) → DifferentiableAt ℝ a' (φ z) → DifferentiableAt ℝ q (φ z) → 0 < a (φ z) → 0 < a' (φ z) → angleForm n (fun x => a (φ x)) (fun x => a' (φ x)) (fun x => q (φ x)) ξ z = angleForm n a a' q (fderiv ℂ φ z ξ) (φ z) :=
  fun _ _ _ _ _ n a a' q ξ z => ⟨angleForm_smul n a a' q ξ z,
    fun ha ha' hq h0 h0' => contDiffAt_angleForm n ξ ha ha' hq h0 h0',
    fun φ hφ ha ha' hq h0 h0' => angleForm_comp_holo n a a' q ξ z φ hφ ha ha' hq h0 h0'⟩

end GlobalTheory.CurveDens
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder ComplexConjugate

noncomputable section
namespace GlobalTheory.CurveDens.FrameIndep

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem ofReal_norm_sq (w : ℂ) : ((‖w‖ : ℂ)) ^ 2 = w * conj w := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

theorem dR_conj {f : E → ℂ} {z : E} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun x => conj (f x)) z := by
  simpa using hf.star

theorem dR_ofReal {a : E → ℝ} {z : E} (ha : DifferentiableAt ℝ a z) :
    DifferentiableAt ℝ (fun x => (a x : ℂ)) z :=
  (Complex.ofRealCLM.differentiableAt.comp z ha : _)

theorem dR_normSq {f : E → ℂ} {z : E} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun x => ‖f x‖ ^ 2) z :=
  hf.norm_sq ℝ

theorem del_log {t : E → ℝ} {z : E} (ht : DifferentiableAt ℝ t z) (h0 : 0 < t z) (ξ : E) :
    del (fun x => (Real.log (t x) : ℂ)) z ξ = ((t z : ℂ))⁻¹ * del (fun x => (t x : ℂ)) z ξ := by
  rw [del_ofReal_comp (Real.hasDerivAt_log (ne_of_gt h0)) ht ξ]; push_cast; rfl

theorem dbar_log {t : E → ℝ} {z : E} (ht : DifferentiableAt ℝ t z) (h0 : 0 < t z) (ξ : E) :
    dbar (fun x => (Real.log (t x) : ℂ)) z ξ = ((t z : ℂ))⁻¹ * dbar (fun x => (t x : ℂ)) z ξ := by
  rw [dbar_ofReal_comp (Real.hasDerivAt_log (ne_of_gt h0)) ht ξ]; push_cast; rfl

theorem ofReal_congr {b c : E → ℝ} {g : E → ℂ} {z : E} (e : b =ᶠ[𝓝 z] fun x => ‖g x‖ ^ 2 * c x) :
    (fun x => (b x : ℂ)) =ᶠ[𝓝 z] fun x => g x * conj (g x) * (c x : ℂ) := by
  filter_upwards [e] with x hx
  rw [hx]; push_cast; rw [ofReal_norm_sq]

theorem del_scaled {b c : E → ℝ} {g : E → ℂ} {z : E} (hc : DifferentiableAt ℝ c z) (h0 : 0 < c z)
    (hg : DifferentiableAt ℂ g z) (hg0 : g z ≠ 0) (e : b =ᶠ[𝓝 z] fun x => ‖g x‖ ^ 2 * c x) (ξ : E) :
    del (fun x => (Real.log (b x) : ℂ)) z ξ =
      del (fun x => (Real.log (c x) : ℂ)) z ξ + del g z ξ / g z := by
  have hgR := hg.restrictScalars ℝ
  have hbD : DifferentiableAt ℝ b z := e.differentiableAt_iff.2 ((dR_normSq hgR).mul hc)
  have hz : dbar g z ξ = 0 := by rw [dbar_eq_zero hg]; rfl
  have hbz : b z = ‖g z‖ ^ 2 * c z := e.eq_of_nhds
  have hb0 : 0 < b z := by rw [hbz]; have := norm_pos_iff.2 hg0; positivity
  rw [del_log hbD hb0, del_log hc h0, del_congr (ofReal_congr e),
    del_mul (a := fun x => g x * conj (g x)) (hgR.fun_mul (dR_conj hgR)) (dR_ofReal hc), del_mul hgR (dR_conj hgR), del_conj,
    hz, hbz]
  push_cast
  rw [ofReal_norm_sq]
  have h1 : conj (g z) ≠ 0 := (map_ne_zero _).2 hg0
  have h2 : (c z : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  simp only [map_zero]
  field_simp
  ring

theorem dbar_scaled {b c : E → ℝ} {g : E → ℂ} {z : E} (hc : DifferentiableAt ℝ c z) (h0 : 0 < c z)
    (hg : DifferentiableAt ℂ g z) (hg0 : g z ≠ 0) (e : b =ᶠ[𝓝 z] fun x => ‖g x‖ ^ 2 * c x) (ξ : E) :
    dbar (fun x => (Real.log (b x) : ℂ)) z ξ =
      dbar (fun x => (Real.log (c x) : ℂ)) z ξ + conj (del g z ξ / g z) := by
  have hgR := hg.restrictScalars ℝ
  have hbD : DifferentiableAt ℝ b z := e.differentiableAt_iff.2 ((dR_normSq hgR).mul hc)
  have hz : dbar g z ξ = 0 := by rw [dbar_eq_zero hg]; rfl
  have hbz : b z = ‖g z‖ ^ 2 * c z := e.eq_of_nhds
  have hb0 : 0 < b z := by rw [hbz]; have := norm_pos_iff.2 hg0; positivity
  rw [dbar_log hbD hb0, dbar_log hc h0, dbar_congr (ofReal_congr e),
    dbar_mul (a := fun x => g x * conj (g x)) (hgR.fun_mul (dR_conj hgR)) (dR_ofReal hc), dbar_mul hgR (dR_conj hgR), dbar_conj,
    hz, hbz]
  push_cast
  rw [ofReal_norm_sq]
  have h1 : conj (g z) ≠ 0 := (map_ne_zero _).2 hg0
  have h2 : (c z : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  simp only [map_zero, map_div₀]
  field_simp
  ring

theorem del_prod {q f g : E → ℂ} {z : E} (hq : DifferentiableAt ℝ q z) (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) (ξ : E) :
    del (fun x => g x * conj (f x) * q x) z ξ =
      g z * conj (f z) * del q z ξ + del g z ξ * conj (f z) * q z := by
  have hfR := hf.restrictScalars ℝ
  have hgR := hg.restrictScalars ℝ
  have hz : dbar f z ξ = 0 := by rw [dbar_eq_zero hf]; rfl
  rw [del_mul (a := fun x => g x * conj (f x)) (hgR.fun_mul (dR_conj hfR)) hq,
    del_mul hgR (dR_conj hfR), del_conj, hz, map_zero]
  ring

theorem dbar_prod {q f g : E → ℂ} {z : E} (hq : DifferentiableAt ℝ q z) (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) (ξ : E) :
    dbar (fun x => g x * conj (f x) * q x) z ξ =
      g z * conj (f z) * dbar q z ξ + g z * conj (del f z ξ) * q z := by
  have hfR := hf.restrictScalars ℝ
  have hgR := hg.restrictScalars ℝ
  have hz : dbar g z ξ = 0 := by rw [dbar_eq_zero hg]; rfl
  rw [dbar_mul (a := fun x => g x * conj (f x)) (hgR.fun_mul (dR_conj hfR)) hq,
    dbar_mul hgR (dR_conj hfR), dbar_conj, hz]
  ring

end GlobalTheory.CurveDens.FrameIndep

open GlobalTheory.CurveDens.FrameIndep in

theorem GlobalTheory.CurveDens.angleForm_frame_indep (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (n : ℕ) (a a' a₂ a₂' : E → ℝ) (q q₂ f g : E → ℂ)
    (ξ z : E) (ha : DifferentiableAt ℝ a z) (ha' : DifferentiableAt ℝ a' z)
    (hq : DifferentiableAt ℝ q z) (ha0 : 0 < a z) (ha0' : 0 < a' z) (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) (hf0 : f z ≠ 0) (hg0 : g z ≠ 0)
    (e₂ : a₂ =ᶠ[𝓝 z] fun x => ‖f x‖ ^ 2 * a x) (e₂' : a₂' =ᶠ[𝓝 z] fun x => ‖g x‖ ^ 2 * a' x)
    (eq : q₂ =ᶠ[𝓝 z] fun x => g x * starRingEnd ℂ (f x) * q x) :
    angleForm n a₂ a₂' q₂ ξ z = angleForm n a a' q ξ z := by
  have hqz : q₂ z = g z * conj (f z) * q z := eq.eq_of_nhds
  have haz : a₂ z = ‖f z‖ ^ 2 * a z := e₂.eq_of_nhds
  have haz' : a₂' z = ‖g z‖ ^ 2 * a' z := e₂'.eq_of_nhds
  have hF : ‖f z‖ ≠ 0 := norm_ne_zero_iff.2 hf0
  have hG : ‖g z‖ ≠ 0 := norm_ne_zero_iff.2 hg0
  have hv : ‖q₂ z‖ ^ 2 / (a₂ z * a₂' z) = ‖q z‖ ^ 2 / (a z * a' z) := by
    rw [hqz, haz, haz', norm_mul, norm_mul, Complex.norm_conj]
    field_simp
  unfold angleForm
  rw [hv]
  generalize (((‖q z‖ ^ 2 / (a z * a' z)) ^ n : ℝ) : ℂ) = V
  rw [del_congr eq, dbar_congr eq, del_prod hq hf hg, dbar_prod hq hf hg,
    del_scaled ha' ha0' hg hg0 e₂', dbar_scaled ha ha0 hf hf0 e₂, hqz, haz, haz']
  push_cast
  rw [ofReal_norm_sq, ofReal_norm_sq]
  have h1 : conj (f z) ≠ 0 := (map_ne_zero _).2 hf0
  have h2 : conj (g z) ≠ 0 := (map_ne_zero _).2 hg0
  have h3 : (a z : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have h4 : (a' z : ℂ) ≠ 0 := by exact_mod_cast ha0'.ne'
  simp only [map_mul, map_sub, map_add, map_div₀, map_inv₀, Complex.conj_conj]
  generalize del (fun x => (Real.log (a' x) : ℂ)) z ξ = A
  generalize dbar (fun x => (Real.log (a x) : ℂ)) z ξ = B
  generalize del q z ξ = Q1
  generalize dbar q z ξ = Q2
  generalize del f z ξ = F1
  generalize del g z ξ = G1
  field_simp
  ring
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder ContDiff

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AngleGlue
open GlobalTheory.Twist (resM app_resM)
variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {E L L' : X.Modules} {r : ℕ} (h : Met p σ E r)

theorem contDiffAt_form (H : h.IsCInf) {U : X.Opens} (s₁ s₂ : Γ(E, U)) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ U) {D : ℕ} (c : AlgChart p σ D) (hc : y ∈ c.e.source) :
    ContDiffAt ℝ ∞ (fun v => h.form s₁ s₂ (c.e.symm v)) (c.e y) :=
  (H.gram ![s₁, s₂] hy 0 1).contDiffAt_chart c hc

theorem contDiffAt_re_form (H : h.IsCInf) {U : X.Opens} (s₁ s₂ : Γ(E, U)) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ U) {D : ℕ} (c : AlgChart p σ D) (hc : y ∈ c.e.source) :
    ContDiffAt ℝ ∞ (fun v => (h.form s₁ s₂ (c.e.symm v)).re) (c.e y) :=
  Complex.reCLM.contDiff.contDiffAt.comp _ (contDiffAt_form h H s₁ s₂ hy c hc)

theorem re_form_pos {l : L ⟶ E} (hl : IsSubbundle l) (hL : IsVB L 1) {U : X.Opens} (t : Γ(L, U))
    (ht : IsFrame (fun _ : Fin 1 => t)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    0 < (h.form (l.app U t) (l.app U t) y).re :=
  (Complex.pos_iff.1 (((h.restrict hl hL).posDef ⟨U, fun _ => t, ht⟩ y hy).diag_pos (i := 0))).1

theorem form_eq_of_resM {U U₂ W : X.Opens} (hW : W ≤ U) (hW₂ : W ≤ U₂) (x₁ x₂ : Γ(E, U))
    (y₁ y₂ : Γ(E, U₂)) (f₁ f₂ : Γ(X, W)) (e₁ : resM E hW₂ y₁ = f₁ • resM E hW x₁)
    (e₂ : resM E hW₂ y₂ = f₂ • resM E hW x₂) (z : CxPts p σ) (hz : z ∈ ptsIn p σ W) :
    h.form y₁ y₂ z = ev p σ W f₁ z * starRingEnd ℂ (ev p σ W f₂ z) * h.form x₁ x₂ z := by
  have key (s t : Γ(E, W)) (f : Γ(X, W)) :
      h.form s (f • t) z = starRingEnd ℂ (ev p σ W f z) * h.form s t z := by
    rw [← h.conj_form, h.form_smul_left, map_mul, h.conj_form]
  rw [← h.form_resM y₁ y₂ hW₂ hz, e₁, e₂, h.form_smul_left, key, h.form_resM _ _ hW hz]
  ring

theorem exists_eq_smul {U U₂ : X.Opens} (t : Γ(L, U)) (ht : IsFrame (fun _ : Fin 1 => t))
    (s : Γ(L, U₂)) : ∃ f : Γ(X, U ⊓ U₂),
      resM L (inf_le_right : U ⊓ U₂ ≤ U₂) s = f • resM L (inf_le_left : U ⊓ U₂ ≤ U) t := by
  refine ⟨(ht.basis (inf_le_left : U ⊓ U₂ ≤ U)).repr (resM L inf_le_right s) 0, ?_⟩
  have := (ht.basis (inf_le_left : U ⊓ U₂ ≤ U)).sum_repr (resM L inf_le_right s)
  rw [Fin.sum_univ_one, IsFrame.basis_apply] at this
  exact this.symm

theorem exists_app_eq_smul (l : L ⟶ E) {U U₂ : X.Opens} (t : Γ(L, U))
    (ht : IsFrame (fun _ : Fin 1 => t)) (s : Γ(L, U₂)) : ∃ f : Γ(X, U ⊓ U₂),
      resM E (inf_le_right : U ⊓ U₂ ≤ U₂) (l.app U₂ s) =
        f • resM E (inf_le_left : U ⊓ U₂ ≤ U) (l.app U t) := by
  obtain ⟨f, hf⟩ := exists_eq_smul t ht s
  exact ⟨f, by rw [← app_resM, hf, Scheme.Modules.Hom.app_smul, app_resM]⟩

variable {l : L ⟶ E} {l' : L' ⟶ E}

theorem angleForm_frames (H : h.IsCInf) (hl : IsSubbundle l) (hl' : IsSubbundle l')
    (hL : IsVB L 1) (hL' : IsVB L' 1) (n : ℕ) {U U₂ : X.Opens} (t : Γ(L, U)) (t' : Γ(L', U))
    (s : Γ(L, U₂)) (s' : Γ(L', U₂)) (ht : IsFrame (fun _ : Fin 1 => t))
    (ht' : IsFrame (fun _ : Fin 1 => t')) (hs : IsFrame (fun _ : Fin 1 => s))
    (hs' : IsFrame (fun _ : Fin 1 => s')) (c : AlgChart p σ 1) {y : CxPts p σ}
    (hc : y ∈ c.e.source) (hy : y ∈ ptsIn p σ U) (hy₂ : y ∈ ptsIn p σ U₂) (ξ : EuclideanSpace ℂ (Fin 1)) :
    angleForm n (fun v => (h.form (l.app U₂ s) (l.app U₂ s) (c.e.symm v)).re)
      (fun v => (h.form (l'.app U₂ s') (l'.app U₂ s') (c.e.symm v)).re)
      (fun v => h.form (l'.app U₂ s') (l.app U₂ s) (c.e.symm v)) ξ (c.e y) =
    angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
      (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
      (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) ξ (c.e y) := by
  obtain ⟨f, hf⟩ := exists_app_eq_smul l t ht s
  obtain ⟨g, hg⟩ := exists_app_eq_smul l' t' ht' s'
  have hW : y ∈ ptsIn p σ (U ⊓ U₂) := mem_ptsIn_inf.2 ⟨hy, hy₂⟩
  have hN : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn p σ (U ⊓ U₂) :=
    eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn (U ⊓ U₂))).mem_nhds
      (ChartGlue.mem_over c.e hc hW)) fun _ hv => hv.2
  have hre (a b : ℂ) : (a * starRingEnd ℂ a * b).re = ‖a‖ ^ 2 * b.re := by
    rw [Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
  have ef := form_eq_of_resM h inf_le_left inf_le_right _ _ _ _ f f hf hf
  have eg := form_eq_of_resM h inf_le_left inf_le_right _ _ _ _ g g hg hg
  have eq := form_eq_of_resM h inf_le_left inf_le_right _ _ _ _ g f hg hf
  have e0 := c.e.left_inv hc
  have hpos₂ := re_form_pos h hl hL s hs hy₂
  have hpos₂' := re_form_pos h hl' hL' s' hs' hy₂
  refine GlobalTheory.CurveDens.angleForm_frame_indep _ n _ _ _ _ _ _ (fun v => ev p σ (U ⊓ U₂) f (c.e.symm v))
    (fun v => ev p σ (U ⊓ U₂) g (c.e.symm v)) ξ (c.e y)
    ((contDiffAt_re_form h H _ _ hy c hc).differentiableAt (by simp))
    ((contDiffAt_re_form h H _ _ hy c hc).differentiableAt (by simp))
    ((contDiffAt_form h H _ _ hy c hc).differentiableAt (by simp))
    (by simp only [e0]; exact re_form_pos h hl hL t ht hy)
    (by simp only [e0]; exact re_form_pos h hl' hL' t' ht' hy)
    (c.differentiableAt_ev f hc hW) (c.differentiableAt_ev g hc hW) ?_ ?_ ?_ ?_ ?_
  · simp only [e0]
    intro h0
    rw [ef _ hW, h0] at hpos₂
    simp at hpos₂
  · simp only [e0]
    intro h0
    rw [eg _ hW, h0] at hpos₂'
    simp at hpos₂'
  · filter_upwards [hN] with v hv
    rw [ef _ hv, hre]
  · filter_upwards [hN] with v hv
    rw [eg _ hv, hre]
  · filter_upwards [hN] with v hv
    rw [eq _ hv]

theorem apply_single_eq_det_smul (A : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) :
    A (EuclideanSpace.single 0 1) = A.det • EuclideanSpace.single 0 1 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 1) ℂ).toBasis,
    Matrix.det_unique]
  ext i
  simp [LinearMap.toMatrix_apply, Subsingleton.elim i 0]

end GlobalTheory.AngleGlue

open GlobalTheory.Twist (resM)

theorem GlobalTheory.angleForm_global : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (V L L' : X.Modules) (r : ℕ) (h : Met p σ V r) (l : L ⟶ V) (l' : L' ⟶ V), h.IsCInf → IsSubbundle l → IsSubbundle l' → IsVB L 1 → IsVB L' 1 → ∀ n : ℕ, ∃ m : AlgChart p σ 1 → CxPts p σ → ℂ, (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) ∧ (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) ∧ ∀ (U : X.Opens) (t : Γ(L, U)) (t' : Γ(L', U)), IsFrame (fun _ : Fin 1 => t) → IsFrame (fun _ : Fin 1 => t') → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∈ ptsIn p σ U → m c y = angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re) (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re) (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1) (c.e y) := by
  intro k _ X p σ V L L' r h l l' H hl hl' hL hL' n
  let W : CxPts p σ → X.Opens := fun y => (hL.pick y).U ⊓ (hL'.pick y).U
  let T : ∀ y, Γ(L, W y) := fun y => resM L inf_le_left ((hL.pick y).e 0)
  let T' : ∀ y, Γ(L', W y) := fun y => resM L' inf_le_right ((hL'.pick y).e 0)
  have hT : ∀ y, IsFrame (fun _ : Fin 1 => T y) := fun y => by
    have := (hL.pick y).isFrame.res (inf_le_left : W y ≤ _)
    convert this using 2 with i
    rw [Subsingleton.elim i 0]
  have hT' : ∀ y, IsFrame (fun _ : Fin 1 => T' y) := fun y => by
    have := (hL'.pick y).isFrame.res (inf_le_right : W y ≤ _)
    convert this using 2 with i
    rw [Subsingleton.elim i 0]
  have hW : ∀ y, y ∈ ptsIn p σ (W y) := fun y => mem_ptsIn_inf.2 ⟨hL.mem_pick y, hL'.mem_pick y⟩
  refine ⟨fun c y => angleForm n
    (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c.e.symm v)).re)
    (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c.e.symm v)).re)
    (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c.e.symm v))
    (EuclideanSpace.single 0 1) (c.e y), ?_, ?_, ?_⟩
  · intro c y hc
    have e0 := c.e.left_inv hc
    have hG := (GlobalTheory.CurveDens.angleForm_props _ n
      (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c.e.symm v)).re)
      (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c.e.symm v)).re)
      (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c.e.symm v))
      (EuclideanSpace.single 0 1) (c.e y)).2.1
      ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c hc).of_le (by norm_cast))
      ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c hc).of_le (by norm_cast))
      ((GlobalTheory.AngleGlue.contDiffAt_form h H _ _ (hW y) c hc).of_le (by norm_cast))
      (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl hL _ (hT y) (hW y))
      (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl' hL' _ (hT' y) (hW y))
    refine hG.congr_of_eventuallyEq ?_
    filter_upwards [(ChartGlue.isOpen_over c.e (isOpen_ptsIn (W y))).mem_nhds
      (ChartGlue.mem_over c.e hc (hW y))] with v hv
    have := GlobalTheory.AngleGlue.angleForm_frames h H hl hl' hL hL' n (T y) (T' y) (T (c.e.symm v))
      (T' (c.e.symm v)) (hT y) (hT' y) (hT _) (hT' _) c (c.e.map_target hv.1) hv.2 (hW _)
      (EuclideanSpace.single 0 1)
    exact this.trans (by rw [c.e.right_inv hv.1])
  · intro c c' y hc hc'
    have e0 := c.e.left_inv hc
    have e0' := c'.e.left_inv hc'
    have hN := (ChartGlue.isOpen_over c.e c'.e.open_source).mem_nhds (ChartGlue.mem_over c.e hc hc')
    have hφz : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e e0
    have hφ : DifferentiableAt ℂ (c'.e ∘ c.e.symm) (c.e y) := (c.holo_trans c').differentiableAt hN
    have step1 := GlobalTheory.CurveDens.angleForm_frame_indep _ n
      (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c.e.symm v)).re)
      (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c.e.symm v)).re)
      (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c'.e.symm ((c'.e ∘ c.e.symm) v))).re)
      (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y))
        (c'.e.symm ((c'.e ∘ c.e.symm) v))).re)
      (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c.e.symm v))
      (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c'.e.symm ((c'.e ∘ c.e.symm) v)))
      (fun _ => 1) (fun _ => 1) (EuclideanSpace.single 0 1) (c.e y)
      ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c hc).differentiableAt (by simp))
      ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c hc).differentiableAt (by simp))
      ((GlobalTheory.AngleGlue.contDiffAt_form h H _ _ (hW y) c hc).differentiableAt (by simp))
      (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl hL _ (hT y) (hW y))
      (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl' hL' _ (hT' y) (hW y))
      (differentiableAt_const _) (differentiableAt_const _) one_ne_zero one_ne_zero
      (by filter_upwards [hN] with v hv; simp [c'.e.left_inv hv.2])
      (by filter_upwards [hN] with v hv; simp [c'.e.left_inv hv.2])
      (by filter_upwards [hN] with v hv; simp [c'.e.left_inv hv.2])
    have step2 := (GlobalTheory.CurveDens.angleForm_props _ n
      (fun w => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c'.e.symm w)).re)
      (fun w => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c'.e.symm w)).re)
      (fun w => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c'.e.symm w))
      (EuclideanSpace.single 0 1) (c.e y)).2.2 (c'.e ∘ c.e.symm) hφ
      (by rw [hφz]; exact (GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c' hc').differentiableAt (by simp))
      (by rw [hφz]; exact (GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c' hc').differentiableAt (by simp))
      (by rw [hφz]; exact (GlobalTheory.AngleGlue.contDiffAt_form h H _ _ (hW y) c' hc').differentiableAt (by simp))
      (by rw [hφz]; simp only [e0']; exact GlobalTheory.AngleGlue.re_form_pos h hl hL _ (hT y) (hW y))
      (by rw [hφz]; simp only [e0']; exact GlobalTheory.AngleGlue.re_form_pos h hl' hL' _ (hT' y) (hW y))
    have step3 := (GlobalTheory.CurveDens.angleForm_props _ n
      (fun w => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c'.e.symm w)).re)
      (fun w => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c'.e.symm w)).re)
      (fun w => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c'.e.symm w))
      (EuclideanSpace.single 0 1) (c'.e y)).1 (ChartGlue.transDet c.e c'.e y)
    rw [hφz, GlobalTheory.AngleGlue.apply_single_eq_det_smul] at step2
    exact step1.symm.trans (step2.trans step3)
  · intro U t t' ht ht' c y hc hy
    exact GlobalTheory.AngleGlue.angleForm_frames h H hl hl' hL hL' n t t' (T y) (T' y) ht ht' (hT y)
      (hT' y) c hc hy (hW y) _
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_C1_density_for_line_pair : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (V L L' : X.Modules) (r : ℕ) (h : Met p σ V r) (l : L ⟶ V) (l' : L' ⟶ V), h.IsCInf → IsSubbundle l → IsSubbundle l' → IsVB L 1 → IsVB L' 1 → ∀ n : ℕ, ∃ m : AlgChart p σ 1 → CxPts p σ → ℂ, (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) ∧ (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) ∧ ∀ (U : X.Opens) (t : Γ(L, U)) (t' : Γ(L', U)), IsFrame (fun _ : Fin 1 => t) → IsFrame (fun _ : Fin 1 => t') → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∈ ptsIn p σ U → m c y = angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re) (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re) (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1) (c.e y) := by
  first | exact @GlobalTheory.angleForm_global | exact GlobalTheory.angleForm_global | (intros; apply GlobalTheory.angleForm_global <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.CurveDens

theorem part_compl_eq_zero {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {ρ : AlgChart p σ 1 → CxPts p σ → ℝ} {K : Set (CxPts p σ)} (hK : MeasurableSet K)
    (h : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∉ K → ρ c y ≤ 0) : part ρ Kᶜ = 0 := by
  have key : part ρ ≤ (part ρ).restrict K := iSup_le fun c => by
    have e : ChartGlue.chartMeas c.e (fun y => ENNReal.ofReal (ρ c y)) Kᶜ = 0 := by
      rw [ChartGlue.chartMeas_apply _ _ hK.compl]
      refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _
        (c.e.open_source.measurableSet.inter hK.compl) Set.inter_subset_left) ?_
      rintro _ ⟨y, hy, rfl⟩
      simp only [c.e.left_inv hy.1]
      exact ENNReal.ofReal_eq_zero.2 (h c y hy.1 hy.2)
    rw [← Measure.restrict_eq_self_of_ae_mem (s := K) (mem_ae_iff.2 e)]
    exact Measure.restrict_mono le_rfl (le_iSup (fun c : AlgChart p σ 1 =>
      ChartGlue.chartMeas c.e fun y => ENNReal.ofReal (ρ c y)) c)
  refine le_antisymm ((key Kᶜ).trans_eq ?_) bot_le
  rw [Measure.restrict_apply hK.compl, Set.compl_inter_self, measure_empty]

theorem integral_re_dbar_eq_zero {n : ℕ} {F : ReciprocityTheory.L2DbarEstimates.V n → ℂ} (hF : ContDiff ℝ 1 F)
    (hc : HasCompactSupport F) (u : ReciprocityTheory.L2DbarEstimates.V n) :
    Integrable (fun v => (dbar F v u).re) ∧ ∫ v, (dbar F v u).re = 0 := by
  have hint : ∀ w : ReciprocityTheory.L2DbarEstimates.V n, Integrable (fun y => fderiv ℝ F y w) := fun w =>
    ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  have hD : Integrable (fun v => dbar F v u) := by
    simp only [dbar_apply, smul_eq_mul]
    exact ((hint _).add ((hint _).const_mul _)).const_mul _
  refine ⟨Complex.reCLM.integrable_comp hD, ?_⟩
  have h0 : ∫ v, dbar F v u = 0 := by
    simp only [dbar_apply, smul_eq_mul]
    rw [integral_const_mul, integral_add (hint _) ((hint _).const_mul _), integral_const_mul,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n F hF hc,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n F hF hc]
    simp
  have := Complex.reCLM.integral_comp_comm hD
  simp only [Complex.reCLM_apply] at this
  rw [this, h0, Complex.zero_re]

theorem total_dbar_eq_zero_of_compact_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (m : AlgChart p σ 1 → CxPts p σ → ℂ), (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) → (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) → ∀ (c₀ : AlgChart p σ 1) (K : Set (CxPts p σ)), IsCompact K → K ⊆ c₀.e.source → (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∉ K → m c y = 0) → total (fun (c : AlgChart p σ 1) (y : CxPts p σ) => (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re) = 0 := by
  intro k _ X p σ _ _ m h1 h2 c₀ K hK hKs h3
  set ρ : AlgChart p σ 1 → CxPts p σ → ℝ := fun c y =>
    (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re with hρ
  have hD : IsDens ρ := GlobalTheory.T.dbar_density_of_transition k X p σ m h1 h2
  have hKm : MeasurableSet K := hK.isClosed.measurableSet

  have hz : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∉ K → ρ c y = 0 := fun c y hy hyK => by
    have hW := ChartGlue.isOpen_over c.e hK.isClosed.isOpen_compl
    have he : (fun v => m c (c.e.symm v)) =ᶠ[𝓝 (c.e y)] fun _ => 0 := by
      filter_upwards [hW.mem_nhds (ChartGlue.mem_over c.e hy hyK)] with v hv
      exact h3 c _ (c.e.map_target hv.1) hv.2
    simp only [hρ]
    rw [dbar_congr he, dbar_apply]
    simp

  set A : Set (ReciprocityTheory.L2DbarEstimates.V 1) := c₀.e '' K with hAdef
  have hA : IsCompact A := hK.image_of_continuousOn (c₀.e.continuousOn.mono hKs)
  have hAt : A ⊆ c₀.e.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact c₀.e.map_source (hKs hy)
  set F : ReciprocityTheory.L2DbarEstimates.V 1 → ℂ := c₀.e.target.indicator fun v => m c₀ (c₀.e.symm v) with hFdef
  have hF0 : ∀ v ∉ A, F v = 0 := fun v hv => by
    by_cases ht : v ∈ c₀.e.target
    · rw [hFdef, Set.indicator_of_mem ht]
      refine h3 c₀ _ (c₀.e.map_target ht) fun hk => hv ⟨_, hk, c₀.e.right_inv ht⟩
    · rw [hFdef, Set.indicator_of_notMem ht]
  have hFt : ∀ v ∈ c₀.e.target, F =ᶠ[𝓝 v] fun v => m c₀ (c₀.e.symm v) := fun v hv => by
    filter_upwards [c₀.e.open_target.mem_nhds hv] with w hw
    rw [hFdef, Set.indicator_of_mem hw]
  have hFA : ∀ v ∉ A, F =ᶠ[𝓝 v] fun _ => 0 := fun v hv => by
    filter_upwards [hA.isClosed.isOpen_compl.mem_nhds hv] with w hw
    exact hF0 w hw
  have hFC : ContDiff ℝ 1 F := contDiff_iff_contDiffAt.2 fun v => by
    by_cases ht : v ∈ c₀.e.target
    · have := h1 c₀ _ (c₀.e.map_target ht)
      rw [c₀.e.right_inv ht] at this
      exact this.congr_of_eventuallyEq (hFt v ht)
    · exact contDiffAt_const.congr_of_eventuallyEq (hFA v fun h => ht (hAt h))
  have hFs : HasCompactSupport F := HasCompactSupport.intro hA hF0
  obtain ⟨hHi, hH0⟩ := integral_re_dbar_eq_zero hFC hFs (EuclideanSpace.single 0 1)
  set H : ReciprocityTheory.L2DbarEstimates.V 1 → ℝ := fun v => (dbar F v (EuclideanSpace.single 0 1)).re with hHdef
  have hHA : ∀ v ∉ A, H v = 0 := fun v hv => by
    simp only [hHdef]
    rw [dbar_congr (hFA v hv), dbar_apply]
    simp
  have hHt : ∀ v ∈ A, H v = ρ c₀ (c₀.e.symm v) := fun v hv => by
    simp only [hHdef, hρ]
    rw [dbar_congr (hFt v (hAt hv)), c₀.e.right_inv (hAt hv)]

  have hl : ∀ τ : ℝ → ℝ, τ 0 = 0 → ∫⁻ v, ENNReal.ofReal (τ (H v)) =
      ∫⁻ v in A, ENNReal.ofReal (τ (ρ c₀ (c₀.e.symm v))) := fun τ h0 => by
    rw [← lintegral_indicator hA.measurableSet]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ A
    · rw [Set.indicator_of_mem hv, hHt v hv]
    · rw [Set.indicator_of_notMem hv, hHA v hv, h0, ENNReal.ofReal_zero]
  have hp : part ρ Set.univ = ∫⁻ v, ENNReal.ofReal (H v) := by
    rw [hl (fun t => t) rfl, ← measure_add_measure_compl hKm,
      part_compl_eq_zero hKm fun c y hy hyK => (hz c y hy hyK).le, add_zero,
      hD.part_apply c₀ hKm hKs]
  have hn : part (fun c y => -ρ c y) Set.univ = ∫⁻ v, ENNReal.ofReal (-H v) := by
    rw [hl (fun t => -t) neg_zero, ← measure_add_measure_compl hKm,
      part_compl_eq_zero hKm fun c y hy hyK => by rw [hz c y hy hyK, neg_zero], add_zero,
      hD.neg.part_apply c₀ hKm hKs]
  rw [total, hp, hn, ← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hHi]
  exact hH0

end GlobalTheory.CurveDens
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.total_re_dbar_eq_zero_of_compact_support_in_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (m : AlgChart p σ 1 → CxPts p σ → ℂ), (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) → (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) → ∀ (c₀ : AlgChart p σ 1) (K : Set (CxPts p σ)), IsCompact K → K ⊆ c₀.e.source → (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∉ K → m c y = 0) → total (fun (c : AlgChart p σ 1) (y : CxPts p σ) => (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re) = 0 := by
  first | exact @GlobalTheory.CurveDens.total_dbar_eq_zero_of_compact_chart | exact GlobalTheory.CurveDens.total_dbar_eq_zero_of_compact_chart | (intros; apply GlobalTheory.CurveDens.total_dbar_eq_zero_of_compact_chart <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveStokes

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem contDiffAt_chart_of_smooth {A : ReciprocityTheory.AnForm.M.FinHolAtlas 1 (CxPts p σ)} (hA : IsAlgAtlas A)
    {χ : CxPts p σ → ℝ} (hχ : A.Smooth χ) (c : AlgChart p σ 1) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    ContDiffAt ℝ 1 (fun v => χ (c.e.symm v)) (c.e y) := by
  have hC : ∀ x ∈ (Set.univ : Set (CxPts p σ)), CInfAt χ x := fun x _ => by
    obtain ⟨l, hl⟩ := A.cover x
    have h := hχ l
    rw [hA.chart_eq l] at h hl
    exact cInfAt_of_chart isOpen_univ _ ((AlgChart.contDiffOn_finChart_iff _ _ _ _).1 h) hl trivial
  have h := contDiffOn_chart hC c
  have hm : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' Set.univ := ⟨c.e.map_source hy, trivial⟩
  have hn : c.e.target ∩ c.e.symm ⁻¹' Set.univ ∈ 𝓝 (c.e y) := by
    rw [Set.preimage_univ, Set.inter_univ]; exact c.e.open_target.mem_nhds (c.e.map_source hy)
  exact ((h.contDiffAt hn).of_le (by norm_num))

end GlobalTheory.CurveStokes

namespace GlobalTheory

open GlobalTheory.CurveStokes in

theorem stokes_curve : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∀ (m : AlgChart p σ 1 → CxPts p σ → ℂ), (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) → (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) → total (fun (c : AlgChart p σ 1) (y : CxPts p σ) => (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re) = 0 := by
  intro k _ X p σ _ _ _ hR m hm hglue
  obtain ⟨R⟩ := hR
  set A := R.finAtlas
  have hA : IsAlgAtlas A := R.isAlgAtlas_finAtlas
  obtain ⟨P⟩ := ReciprocityTheory.AnForm.M.existsPartition A

  set mj : Fin A.n → AlgChart p σ 1 → CxPts p σ → ℂ := fun j c y => (P.χ j y : ℂ) * m c y with hmj
  have hχ : ∀ j (c : AlgChart p σ 1), ∀ y ∈ c.e.source,
      ContDiffAt ℝ 1 (fun v => ((P.χ j (c.e.symm v) : ℝ) : ℂ)) (c.e y) := fun j c y hy =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (contDiffAt_chart_of_smooth hA (P.smooth j) c hy)
  have hmj1 : ∀ j (c : AlgChart p σ 1), ∀ y ∈ c.e.source,
      ContDiffAt ℝ 1 (fun v => mj j c (c.e.symm v)) (c.e y) := fun j c y hy =>
    (hχ j c y hy).mul (hm c y hy)
  have hmj2 : ∀ j (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
      mj j c y = ChartGlue.transDet c.e c'.e y * mj j c' y := fun j c c' y hy hy' => by
    simp only [hmj, hglue c c' y hy hy']; ring
  set ρ : AlgChart p σ 1 → CxPts p σ → ℝ := fun c y =>
    (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re with hρ
  set ρj : Fin A.n → AlgChart p σ 1 → CxPts p σ → ℝ := fun j c y =>
    (dbar (fun v => mj j c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re with hρj

  have hzero : ∀ j, total (ρj j) = 0 := fun j => by
    obtain ⟨c₀, hc₀⟩ := hA j
    refine GlobalTheory.T.total_re_dbar_eq_zero_of_compact_support_in_chart k X p σ (mj j) (hmj1 j) (hmj2 j) c₀ (tsupport (P.χ j))
      (isClosed_tsupport _).isCompact ?_ ?_
    · have := P.tsupport_subset j
      rwa [hc₀, AlgChart.finChart_source] at this
    · intro c y _ hy
      simp [hmj, image_eq_zero_of_notMem_tsupport hy]

  have hsum : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = ∑ j, ρj j c y := fun c y hy => by
    have e : (fun v => m c (c.e.symm v)) = fun v => ∑ j, mj j c (c.e.symm v) := funext fun v => by
      simp only [hmj, ← Finset.sum_mul, ← Complex.ofReal_sum, P.sum_eq_one, Complex.ofReal_one, one_mul]
    simp only [hρ, hρj, e]
    rw [dbar_sum fun j _ => ((hmj1 j c y hy).differentiableAt one_ne_zero)]
    simp [Complex.re_sum]

  obtain ⟨ν, w, hfin, -, hdens, htot⟩ := GlobalTheory.T.finite_measure_density_exists k X p σ ⟨R⟩
  have hd : ∀ j, IsDens (ρj j) := fun j => GlobalTheory.T.dbar_density_of_transition k X p σ (mj j) (hmj1 j) (hmj2 j)
  choose g hgc hgw using fun j => hdens _ (hd j)
  have hint : ∀ j, Integrable (g j) ν := fun j =>
    (hgc j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h0 : ∀ j, ∫ y, g j y ∂ν = 0 := fun j => by
    rw [← (htot _ _ (hgc j) (hgw j)).2, hzero j]
  have hG : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = (∑ j, g j y) * w c y := fun c y hy => by
    rw [hsum c y hy, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => hgw j c y hy
  rw [(htot ρ _ (continuous_finsetSum _ fun j _ => hgc j) hG).2, integral_finsetSum _ fun j _ => hint j]
  simp [h0]

end GlobalTheory
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartwise_C1_density_of_compatible : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∀ (m : AlgChart p σ 1 → CxPts p σ → ℂ), (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) → (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) → total (fun (c : AlgChart p σ 1) (y : CxPts p σ) => (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re) = 0 := by
  atlas_forward_decl GlobalTheory.stokes_curve
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

open Matrix Complex ComplexConjugate

namespace GlobalTheory.CurveDens

theorem proj_rank_two_identity (A Dr : ℝ) (C x y da q : ℂ) (hA : 0 < A) (hQpos : 0 < Dr - normSq C / A) :
    ‖(x * da + y * (A*q + da*((A:ℂ)⁻¹*C))) - (x * A + y * C) * (((A⁻¹:ℝ):ℂ) * da)‖^2 =
    (A * (x * A * conj x + x * conj C * conj y + y * C * conj x + y * Dr * conj y).re - ‖x*A + y*C‖^2) *
      (Real.pi * (2 * (-I * (kappa * ((((Dr - normSq C / A : ℝ)) : ℂ)⁻¹ * conj (-q) * A * (-q)))).re)) := by
  have e : -Complex.I * kappa = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    rw [kappa, ← mul_div_assoc, neg_mul, Complex.I_mul_I]; simp
  have hX : (x * da + y * (A*q + da*((A:ℂ)⁻¹*C))) - (x * A + y * C) * (((A⁻¹:ℝ):ℂ) * da) = y * A * q := by
    have : (A:ℂ) ≠ 0 := by exact_mod_cast hA.ne'
    push_cast; field_simp; ring
  have hT : (((Dr - normSq C / A : ℝ)) : ℂ)⁻¹ * conj (-q) * A * (-q) = ((A * normSq q / (Dr - normSq C / A) : ℝ) : ℂ) := by
    have h0 : conj (-q) * (-q) = (normSq q : ℂ) := by rw [map_neg, neg_mul_neg, mul_comm, Complex.mul_conj]
    have hQ0 : (Dr - normSq C / A) ≠ 0 := hQpos.ne'
    calc _ = (((Dr - normSq C / A : ℝ)) : ℂ)⁻¹ * A * (conj (-q) * (-q)) := by ring
      _ = _ := by rw [h0]; push_cast; field_simp
  rw [hX, hT, ← mul_assoc (-I) kappa, e, ← ofReal_mul, ofReal_re, Complex.sq_norm, Complex.sq_norm]
  have hF : (x * A * conj x + x * conj C * conj y + y * C * conj x + y * Dr * conj y).re =
      A * normSq x + 2 * (x * conj C * conj y).re + Dr * normSq y := by
    simp [normSq_apply, mul_re, mul_im, conj_re, conj_im]; ring
  have hK : A * (x * A * conj x + x * conj C * conj y + y * C * conj x + y * Dr * conj y).re - normSq (x*A + y*C) =
      A * normSq y * (Dr - normSq C / A) := by
    rw [hF]
    simp only [normSq_apply, mul_re, mul_im, conj_re, conj_im, add_re, add_im, ofReal_re, ofReal_im]
    field_simp
    ring
  rw [hK, normSq_mul, normSq_mul, normSq_ofReal]
  have hpi : 0 < Real.pi := Real.pi_pos
  generalize Dr - normSq C / A = Qr at hQpos ⊢
  field_simp

theorem norm_sq_dbar_proj_rank_two (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (G : E → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (s : E → Fin 1 ⊕ Fin 1 → ℂ) (ξ z : E) (hG : MContDiffAt 1 G z) (hP : ∀ᶠ x in 𝓝 z, (G x).PosDef) (hs : ∀ i, DifferentiableAt ℂ (fun x => s x i) z) : ‖dbar (fun x => form (G x) (s x) (Pi.single (Sum.inl 0) 1)) z ξ - form (G z) (s z) (Pi.single (Sum.inl 0) 1) * dbar (fun x => (Real.log (G x (Sum.inl 0) (Sum.inl 0)).re : ℂ)) z ξ‖ ^ 2 = ((G z (Sum.inl 0) (Sum.inl 0)).re * (form (G z) (s z) (s z)).re - ‖form (G z) (s z) (Pi.single (Sum.inl 0) 1)‖ ^ 2) * (Real.pi * (2 * diagVal (extTrace G z) ξ)) := by
  set i₁ : Fin 1 ⊕ Fin 1 := Sum.inl 0 with hi₁
  set i₂ : Fin 1 ⊕ Fin 1 := Sum.inr 0 with hi₂
  have hz : (G z).PosDef := hP.self_of_nhds
  have hform1 : ∀ x, form (G x) (s x) (Pi.single i₁ 1) = s x i₁ * G x i₁ i₁ + s x i₂ * G x i₂ i₁ :=
    fun x => by simp [i₁, i₂, form_eq_sum, Fintype.sum_sum_type, Pi.single_apply]
  have hformss : form (G z) (s z) (s z) = s z i₁ * G z i₁ i₁ * conj (s z i₁) + s z i₁ * G z i₁ i₂ * conj (s z i₂)
     + s z i₂ * G z i₂ i₁ * conj (s z i₁) + s z i₂ * G z i₂ i₂ * conj (s z i₂) := by
    simp [i₁, i₂, form_eq_sum, Fintype.sum_sum_type]; ring
  have hda : DifferentiableAt ℝ (fun x => G x i₁ i₁) z := (hG i₁ i₁).differentiableAt one_ne_zero
  have hdc : DifferentiableAt ℝ (fun x => G x i₂ i₁) z := (hG i₂ i₁).differentiableAt one_ne_zero
  have hsR : ∀ i, DifferentiableAt ℝ (fun x => s x i) z := fun i => (hs i).restrictScalars ℝ

  have h1 : dbar (fun x => form (G x) (s x) (Pi.single i₁ 1)) z ξ =
      s z i₁ * dbar (fun x => G x i₁ i₁) z ξ + s z i₂ * dbar (fun x => G x i₂ i₁) z ξ := by
    simp only [hform1]
    rw [dbar_add ((hsR i₁).fun_mul hda) ((hsR i₂).fun_mul hdc), ContinuousLinearMap.add_apply,
      dbar_mul (hsR i₁) hda, dbar_mul (hsR i₂) hdc, dbar_eq_zero (hs i₁), dbar_eq_zero (hs i₂)]
    simp

  have hreal : ∀ᶠ x in 𝓝 z, G x i₁ i₁ = ((G x i₁ i₁).re : ℂ) := hP.mono fun x hx => by
    have := (Complex.lt_def.1 (hx.diag_pos (i := i₁))).2
    exact Complex.ext (by simp) (by simp [← this])
  have hApos : 0 < (G z i₁ i₁).re := (Complex.lt_def.1 (hz.diag_pos (i := i₁))).1

  have h2 : dbar (fun x => (Real.log (G x i₁ i₁).re : ℂ)) z ξ =
      (((G z i₁ i₁).re)⁻¹ : ℝ) * dbar (fun x => G x i₁ i₁) z ξ := by
    have hg : DifferentiableAt ℝ (fun x => (G x i₁ i₁).re) z := (Complex.reCLM.differentiableAt).comp z hda
    rw [dbar_ofReal_comp (t := fun x => (G x i₁ i₁).re) (Real.hasDerivAt_log hApos.ne') hg,
      dbar_congr (hreal.mono fun x hx => hx.symm)]

  have hoc : ∀ x, orthCoeff (G x) 0 0 = (G x i₁ i₁)⁻¹ * G x i₂ i₁ := fun x => by
    simp [orthCoeff, Matrix.mul_apply, Matrix.inv_def, Matrix.det_unique, i₁, i₂]
    rfl
  have hane : ∀ᶠ x in 𝓝 z, G x i₁ i₁ ≠ 0 := hP.mono fun x hx => (hx.diag_pos (i := i₁)).ne'
  have hdoc : DifferentiableAt ℝ (fun x => (G x i₁ i₁)⁻¹ * G x i₂ i₁) z :=
    (hda.inv hane.self_of_nhds).fun_mul hdc
  have h3 : G z i₁ i₁ * dbar (fun x => (G x i₁ i₁)⁻¹ * G x i₂ i₁) z ξ
      + dbar (fun x => G x i₁ i₁) z ξ * ((G z i₁ i₁)⁻¹ * G z i₂ i₁) = dbar (fun x => G x i₂ i₁) z ξ := by
    rw [← dbar_mul hda hdoc]
    congr 1
    exact dbar_congr (hane.mono fun x hx => by simp only; field_simp)
  have hb : extForm G z ξ 0 0 = -dbar (fun x => (G x i₁ i₁)⁻¹ * G x i₂ i₁) z ξ := by
    rw [extForm_eq_neg_mdbar]
    simp only [Matrix.neg_apply, mdbar_apply, hoc]

  have htr : extTrace G z ξ ξ = kappa * ((quotGram (G z) 0 0)⁻¹ * conj (extForm G z ξ 0 0) * G z i₁ i₁ * extForm G z ξ 0 0) := by
    simp [extTrace, extFormAdj, adj, Matrix.trace_fin_one, Matrix.mul_apply, Matrix.inv_def, Matrix.det_unique, subGram, Matrix.toBlocks₁₁, i₁]
  have hQ : quotGram (G z) 0 0 = G z i₂ i₂ - G z i₂ i₁ * (G z i₁ i₁)⁻¹ * G z i₁ i₂ := by
    simp [quotGram, Matrix.mul_apply, Matrix.inv_def, Matrix.det_unique, i₁, i₂]
    rfl
  have hQpos := (Complex.lt_def.1 ((posDef_quotGram hz).diag_pos (i := 0))).1
  have hGb : G z i₁ i₂ = conj (G z i₂ i₁) := (hz.isHermitian.apply i₁ i₂).symm
  have hGd : G z i₂ i₂ = ((G z i₂ i₂).re : ℂ) := by
    have := (Complex.lt_def.1 (hz.diag_pos (i := i₂))).2
    exact Complex.ext (by simp) (by simp [← this])
  rw [diagVal, htr, hQ, hb, h1, h2, hform1 z, hformss, ← h3, hGb, hGd]
  obtain ⟨A, hGa⟩ : ∃ A : ℝ, G z i₁ i₁ = A := ⟨_, hreal.self_of_nhds⟩
  rw [hQ, hGb, hGd] at hQpos
  rw [hGa] at hQpos ⊢
  simp only [ofReal_re] at hQpos ⊢
  have hQC : ((G z i₂ i₂).re : ℂ) - G z i₂ i₁ * (A : ℂ)⁻¹ * conj (G z i₂ i₁) =
      (((G z i₂ i₂).re - normSq (G z i₂ i₁) / A : ℝ) : ℂ) := by
    rw [mul_comm (G z i₂ i₁), mul_assoc, Complex.mul_conj]; push_cast; ring
  rw [hQC] at hQpos ⊢
  rw [Complex.zero_re, ofReal_re] at hQpos
  rw [hGa, ofReal_re] at hApos
  exact proj_rank_two_identity A _ _ _ _ _ _ hApos hQpos

end GlobalTheory.CurveDens
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_dbar_form_sub_log_metric_le : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (G : E → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (s : E → Fin 1 ⊕ Fin 1 → ℂ) (ξ z : E), MContDiffAt 1 G z → (∀ᶠ x in 𝓝 z, (G x).PosDef) → (∀ i, DifferentiableAt ℂ (fun x => s x i) z) → ‖dbar (fun x => form (G x) (s x) (Pi.single (Sum.inl 0) 1)) z ξ - form (G z) (s z) (Pi.single (Sum.inl 0) 1) * dbar (fun x => (Real.log (G x (Sum.inl 0) (Sum.inl 0)).re : ℂ)) z ξ‖ ^ 2 = ((G z (Sum.inl 0) (Sum.inl 0)).re * (form (G z) (s z) (s z)).re - ‖form (G z) (s z) (Pi.single (Sum.inl 0) 1)‖ ^ 2) * (Real.pi * (2 * diagVal (extTrace G z) ξ)) := by
  first | exact @GlobalTheory.CurveDens.norm_sq_dbar_proj_rank_two | exact GlobalTheory.CurveDens.norm_sq_dbar_proj_rank_two | (intros; apply GlobalTheory.CurveDens.norm_sq_dbar_proj_rank_two <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveDens

open GlobalTheory.VBExt (AdaptedChart)
open GlobalTheory.Twist (resM app_resM)

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {S : ShortComplex X.Modules}

theorem form_eq_gram_frame {r s : ℕ} (h : Met p σ S.X₂ (r + s)) (hS : S.ShortExact)
    (a : AdaptedChart S r s) {V : X.Opens} (u w : Γ(S.X₂, V)) {x : CxPts p σ}
    (hx : x ∈ ptsIn p σ a.U) (hV : x ∈ ptsIn p σ V) :
    h.form u w x = HermFrame.form (h.gram a.frame x)
      (fun i => (a.mid hS).crd p σ u x (finSumFinEquiv i))
      (fun i => (a.mid hS).crd p σ w x (finSumFinEquiv i)) := by
  rw [h.form_eq (a.mid hS) hx u w hV, Met.gram_frame h hS a hx, form_eq_sum, form_eq_sum,
    ← finSumFinEquiv.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← finSumFinEquiv.sum_comp]
  rfl

def adaptedOf (a : AdaptedChart S 1 1) {U : X.Opens} (t : Γ(S.X₁, U))
    (ht : IsFrame fun _ : Fin 1 => t) : AdaptedChart S 1 1 where
  U := U ⊓ a.U
  e := fun _ => resM S.X₁ inf_le_left t
  t := fun i => resM S.X₂ inf_le_right (a.t i)
  he := ht.res inf_le_left
  ht := by
    simp only [app_resM]
    exact a.ht.res inf_le_right

theorem crd_adaptedOf (hS : S.ShortExact) (a : AdaptedChart S 1 1) {U : X.Opens} (t : Γ(S.X₁, U))
    (ht : IsFrame fun _ : Fin 1 => t) {x : CxPts p σ} (hx : x ∈ ptsIn p σ (adaptedOf a t ht).U) :
    (fun i => ((adaptedOf a t ht).mid hS).crd p σ (S.f.app U t) x (finSumFinEquiv i)) =
      Pi.single (Sum.inl 0) 1 := by
  have e : (adaptedOf a t ht).frame (.inl 0) = resM S.X₂ inf_le_left (S.f.app U t) :=
    app_resM _ _ _
  funext i
  rw [← Chart.crd_resM _ (S.f.app U t) (inf_le_left : (adaptedOf a t ht).U ≤ U) hx, ← e]
  refine (AdaptedChart.crd_frame hS (adaptedOf a t ht) hx i (.inl 0)).trans ?_
  rw [Matrix.one_apply, Pi.single_apply]

theorem norm_dbar_projection_sq (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (S : ShortComplex X.Modules) (h : Met p σ S.X₂ (1 + 1)) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1)
    (h₃ : IsVB S.X₃ 1) (H : h.IsCInf) (U : X.Opens) (t : Γ(S.X₁, U)) (w : Γ(S.X₂, U))
    (ht : IsFrame (fun _ : Fin 1 => t)) (c : AlgChart p σ 1) (y : CxPts p σ) (hy : y ∈ c.e.source)
    (hU : y ∈ ptsIn p σ U) :
    ‖dbar (fun v => h.form w (S.f.app U t) (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1) -
        h.form w (S.f.app U t) y *
          dbar (fun v => (Real.log (h.form (S.f.app U t) (S.f.app U t) (c.e.symm v)).re : ℂ)) (c.e y)
            (EuclideanSpace.single 0 1)‖ ^ 2 =
      ((h.form (S.f.app U t) (S.f.app U t) y).re * (h.form w w y).re -
        ‖h.form w (S.f.app U t) y‖ ^ 2) * (Real.pi * h.bcDens hS h₁ h₃ c y) := by
  obtain ⟨a', ha'⟩ := Met.exists_adapted (p := p) (σ := σ) hS h₁ h₃ y
  set a := adaptedOf a' t ht with a_def
  have ha : y ∈ ptsIn p σ a.U := mem_ptsIn_inf.2 ⟨hU, ha'⟩
  set G : ReciprocityTheory.L2DbarEstimates.V 1 → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
    fun v => h.gram a.frame (c.e.symm v) with G_def
  set s : ReciprocityTheory.L2DbarEstimates.V 1 → Fin 1 ⊕ Fin 1 → ℂ :=
    fun v i => (a.mid hS).crd p σ w (c.e.symm v) (finSumFinEquiv i) with s_def
  have hs : ∀ i, DifferentiableAt ℂ (fun x => s x i) (c.e y) := fun i =>
    c.differentiableAt_ev _ hy (mem_ptsIn_inf.2 ⟨hU, ha⟩)
  have hG : MContDiffAt 1 G (c.e y) :=
    ((H.gram a.frame ha).mContDiffAt c hy).of_le (by norm_cast)
  have hp := h.eventually_posDef hS a c hy ha
  have hn : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn p σ (U ⊓ a'.U) :=
    eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn (U ⊓ a'.U))).mem_nhds
      (ChartGlue.mem_over c.e hy ha)) fun _ hv => hv.2
  have e₀ : c.e.symm (c.e y) = y := c.e.left_inv hy
  have key (v : ReciprocityTheory.L2DbarEstimates.V 1) (hv : c.e.symm v ∈ ptsIn p σ (U ⊓ a'.U)) :
      h.form w (S.f.app U t) (c.e.symm v) = form (G v) (s v) (Pi.single (Sum.inl 0) 1) ∧
      h.form (S.f.app U t) (S.f.app U t) (c.e.symm v) = G v (Sum.inl 0) (Sum.inl 0) ∧
      h.form w w (c.e.symm v) = form (G v) (s v) (s v) := by
    have hv' : c.e.symm v ∈ ptsIn p σ U := (mem_ptsIn_inf.1 hv).1
    have hc := crd_adaptedOf hS a' t ht hv
    refine ⟨?_, ?_, form_eq_gram_frame h hS a w w hv hv'⟩
    · rw [form_eq_gram_frame h hS a w _ hv hv', hc]
    · rw [form_eq_gram_frame h hS a _ _ hv hv', hc, form_single]
  have k₀ := key _ (e₀.symm ▸ ha)
  rw [e₀] at k₀
  have e₁ : dbar (fun v => h.form w (S.f.app U t) (c.e.symm v)) (c.e y) =
      dbar (fun v => form (G v) (s v) (Pi.single (Sum.inl 0) 1)) (c.e y) :=
    dbar_congr (hn.mono fun v hv => (key v hv).1)
  have e₂ : dbar (fun v => (Real.log (h.form (S.f.app U t) (S.f.app U t) (c.e.symm v)).re : ℂ))
        (c.e y) = dbar (fun v => (Real.log (G v (Sum.inl 0) (Sum.inl 0)).re : ℂ)) (c.e y) :=
    dbar_congr (hn.mono fun v hv => by simp only [(key v hv).2.1])
  have e₃ : G (c.e y) = h.gram a.frame y := by rw [G_def]; simp only [e₀]
  have main := GlobalTheory.T.norm_dbar_form_sub_log_metric_le _ G s (EuclideanSpace.single 0 1) (c.e y) hG hp hs
  rw [e₁, e₂, k₀.1, k₀.2.1, k₀.2.2, Met.bcDens_eq hS h₁ h₃ a c H hy ha]
  exact main

end GlobalTheory.CurveDens
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_dbar_quotient_form_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (S : ShortComplex X.Modules) (h : Met p σ S.X₂ (1 + 1)) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1) (h₃ : IsVB S.X₃ 1), h.IsCInf → ∀ (U : X.Opens) (t : Γ(S.X₁, U)) (w : Γ(S.X₂, U)), IsFrame (fun _ : Fin 1 => t) → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∈ ptsIn p σ U → ‖dbar (fun v => h.form w (S.f.app U t) (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1) - h.form w (S.f.app U t) y * dbar (fun v => (Real.log (h.form (S.f.app U t) (S.f.app U t) (c.e.symm v)).re : ℂ)) (c.e y) (EuclideanSpace.single 0 1)‖ ^ 2 = ((h.form (S.f.app U t) (S.f.app U t) y).re * (h.form w w y).re - ‖h.form w (S.f.app U t) y‖ ^ 2) * (Real.pi * h.bcDens hS h₁ h₃ c y) := by
  first | exact @GlobalTheory.CurveDens.norm_dbar_projection_sq | exact GlobalTheory.CurveDens.norm_dbar_projection_sq | (intros; apply GlobalTheory.CurveDens.norm_dbar_projection_sq <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CurveDens

open GlobalTheory.Twist (resM)

theorem leviForm_congr_germ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {u u' : E → ℝ} {z : E} (h : u =ᶠ[𝓝 z] u') :
    leviForm u z = leviForm u' z := by
  unfold leviForm ddbar
  refine del_congr ?_
  filter_upwards [h.eventuallyEq_nhds] with x hx
  exact dbar_congr (hx.mono fun w hw => by simp only [hw])

theorem green_algebra (π A B v bc bc' ch ch' lA lB x y N : ℝ) (n : ℕ) (hπ : π ≠ 0) (hA : 0 < A)
    (hB : 0 < B) (hN : N = v * A * B) (hx : x = (A * B - N) * (π * bc))
    (hy : y = (B * A - N) * (π * bc')) (hc : ch = -lA / π) (hc' : ch' = -lB / π) :
    v ^ (n + 1) * (ch - ch') + (n + 1) * v ^ n * (1 - v) * (bc - bc') =
      -(1 / π) * ((n + 1) * (N / (A * B)) ^ n * ((y - x) / (A * B)) +
        (N / (A * B)) ^ (n + 1) * (lA - lB)) := by
  have e : N / (A * B) = v := by rw [hN]; field_simp
  rw [e, hx, hy, hN, hc, hc']
  field_simp
  ring

theorem form_frame_re_pos {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {L : X.Modules} (g : Met p σ L 1) {U : X.Opens} {t : Γ(L, U)}
    (ht : IsFrame (fun _ : Fin 1 => t)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    0 < (g.form t t y).re := by
  let c₀ : VB.Chart L 1 := ⟨U, fun _ => t, ht⟩
  have h₀ := g.form_frame c₀ hy 0 0
  have h₁ := (g.posDef c₀ y hy).diag_pos (i := 0)
  have h₂ : g.form t t y = g.G c₀ y 0 0 := h₀
  rw [h₂]
  exact (Complex.pos_iff.1 h₁).1

theorem green_density {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {V L Q L' Q' : X.Modules} {l : L ⟶ V} {m : V ⟶ Q} {w : l ≫ m = 0} {l' : L' ⟶ V} {m' : V ⟶ Q'}
    {w' : l' ≫ m' = 0} (hS : (ShortComplex.mk l m w).ShortExact)
    (hS' : (ShortComplex.mk l' m' w').ShortExact) (hL : IsVB L 1) (hQ : IsVB Q 1)
    (hL' : IsVB L' 1) (hQ' : IsVB Q' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l')
    (h : Met p σ V (1 + 1)) (H : h.IsCInf) {v : CxPts p σ → ℝ} (hv : IsCosSq h l l' v) (n : ℕ)
    {m₀ : AlgChart p σ 1 → CxPts p σ → ℂ}
    (hm₁ : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source,
      ContDiffAt ℝ 1 (fun v => m₀ c (c.e.symm v)) (c.e y))
    (hm₃ : ∀ (U : X.Opens) (t : Γ(L, U)) (t' : Γ(L', U)), IsFrame (fun _ : Fin 1 => t) →
      IsFrame (fun _ : Fin 1 => t') → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∈ ptsIn p σ U →
      m₀ c y = angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
        (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
        (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1) (c.e y))
    (c : AlgChart p σ 1) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    v y ^ (n + 1) * (c.chernDens (h.restrict hl hL).detWeight y -
        c.chernDens (h.restrict hl' hL').detWeight y) +
      (n + 1) * v y ^ n * (1 - v y) * (Met.bcDens (S := ShortComplex.mk l m w) h hS hL hQ c y -
        Met.bcDens (S := ShortComplex.mk l' m' w') h hS' hL' hQ' c y) =
    (dbar (fun x => (((-(1 / Real.pi) : ℝ)) : ℂ) * m₀ c (c.e.symm x)) (c.e y)
      (EuclideanSpace.single 0 1)).re := by
  obtain ⟨U₁, e₁, hx₁, he₁⟩ := hL (y.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨U₂, e₂, hx₂, he₂⟩ := hL' (y.1 (IsLocalRing.closedPoint ℂ))
  have hU : y ∈ ptsIn p σ (U₁ ⊓ U₂) := mem_ptsIn_inf.2 ⟨mem_ptsIn.2 hx₁, mem_ptsIn.2 hx₂⟩
  obtain ⟨U, hUdef⟩ : ∃ U, U = U₁ ⊓ U₂ := ⟨_, rfl⟩
  rw [← hUdef] at hU
  obtain ⟨t, ht⟩ : ∃ t : Γ(L, U), IsFrame (fun _ : Fin 1 => t) := by
    subst hUdef
    refine ⟨resM L inf_le_left (e₁ 0), ?_⟩
    have e : (fun _ : Fin 1 => resM L (inf_le_left : U₁ ⊓ U₂ ≤ U₁) (e₁ 0)) =
        fun i => resM L inf_le_left (e₁ i) := by
      funext i; rw [Subsingleton.elim i 0]
    rw [e]
    exact he₁.res inf_le_left
  obtain ⟨t', ht'⟩ : ∃ t' : Γ(L', U), IsFrame (fun _ : Fin 1 => t') := by
    subst hUdef
    refine ⟨resM L' inf_le_right (e₂ 0), ?_⟩
    have e : (fun _ : Fin 1 => resM L' (inf_le_right : U₁ ⊓ U₂ ≤ U₂) (e₂ 0)) =
        fun i => resM L' inf_le_right (e₂ i) := by
      funext i; rw [Subsingleton.elim i 0]
    rw [e]
    exact he₂.res inf_le_right
  have e₀ : c.e.symm (c.e y) = y := c.e.left_inv hy
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) U)
  have hm := ChartGlue.mem_over c.e hy hU
  have hn := ho.mem_nhds hm

  have hG : MContDiffAt ∞ (fun x => h.gram ![l.app U t, l'.app U t'] (c.e.symm x)) (c.e y) :=
    (H.gram ![l.app U t, l'.app U t'] hU).mContDiffAt c hy
  have dq : ContDiffAt ℝ 2 (fun x => h.form (l'.app U t') (l.app U t) (c.e.symm x)) (c.e y) :=
    (hG 1 0).of_le (by norm_cast)
  have da₀ : ContDiffAt ℝ 2 (fun x => h.form (l.app U t) (l.app U t) (c.e.symm x)) (c.e y) :=
    (hG 0 0).of_le (by norm_cast)
  have da₁ : ContDiffAt ℝ 2 (fun x => h.form (l'.app U t') (l'.app U t') (c.e.symm x)) (c.e y) :=
    (hG 1 1).of_le (by norm_cast)
  have da : ContDiffAt ℝ 2 (fun x => (h.form (l.app U t) (l.app U t) (c.e.symm x)).re) (c.e y) :=
    Complex.reCLM.contDiff.contDiffAt.comp _ da₀
  have da' : ContDiffAt ℝ 2 (fun x => (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re) (c.e y) :=
    Complex.reCLM.contDiff.contDiffAt.comp _ da₁

  have pa : 0 < (h.form (l.app U t) (l.app U t) y).re := by
    have := form_frame_re_pos (h.restrict hl hL) ht hU
    rwa [h.form_restrict hl hL _ _ hU] at this
  have pa' : 0 < (h.form (l'.app U t') (l'.app U t') y).re := by
    have := form_frame_re_pos (h.restrict hl' hL') ht' hU
    rwa [h.form_restrict hl' hL' _ _ hU] at this

  have hdb : dbar (fun x => (((-(1 / Real.pi) : ℝ)) : ℂ) * m₀ c (c.e.symm x)) (c.e y)
      (EuclideanSpace.single 0 1) = (((-(1 / Real.pi) : ℝ)) : ℂ) *
        dbar (angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
          (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
          (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1))
          (c.e y) (EuclideanSpace.single 0 1) := by
    have e₁ := dbar_const_smul (((-(1 / Real.pi) : ℝ)) : ℂ)
      ((hm₁ c y hy).differentiableAt (by norm_num))
    have e₂ := dbar_congr (z := c.e y) (f := fun v => m₀ c (c.e.symm v))
      (g := angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
          (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
          (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1))
      (by
        filter_upwards [hn] with x hx
        have := hm₃ U t t' ht ht' c (c.e.symm x) (c.e.map_target hx.1) hx.2
        rwa [c.e.right_inv hx.1] at this)
    simp only [smul_eq_mul] at e₁
    rw [e₁, e₂]
    rfl
  have hcalc := GlobalTheory.T.dbar_angleForm_re_eq _ n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
    (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
    (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1) (c.e y)
    da da' dq (by simpa only [e₀] using pa) (by simpa only [e₀] using pa')

  have hX := GlobalTheory.T.norm_dbar_quotient_form_bound k X p σ (ShortComplex.mk l m w) h hS hL hQ H U t (l'.app U t') ht c y hy hU
  have hY := GlobalTheory.T.norm_dbar_quotient_form_bound k X p σ (ShortComplex.mk l' m' w') h hS' hL' hQ' H U t' (l.app U t) ht' c y hy hU
  have hY' : ‖del (fun x => h.form (l'.app U t') (l.app U t) (c.e.symm x)) (c.e y)
        (EuclideanSpace.single 0 1) - h.form (l'.app U t') (l.app U t) y *
        del (fun x => (Real.log (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re : ℂ)) (c.e y)
        (EuclideanSpace.single 0 1)‖ ^ 2 =
      ((h.form (l'.app U t') (l'.app U t') y).re * (h.form (l.app U t) (l.app U t) y).re -
        ‖h.form (l'.app U t') (l.app U t) y‖ ^ 2) * (Real.pi * h.bcDens hS' hL' hQ' c y) := by
    have e₁ : (fun x => h.form (l.app U t) (l'.app U t') (c.e.symm x)) =
        fun x => (starRingEnd ℂ) (h.form (l'.app U t') (l.app U t) (c.e.symm x)) := by
      funext x; rw [h.conj_form]
    have e₂ : h.form (l.app U t) (l'.app U t') y =
        (starRingEnd ℂ) (h.form (l'.app U t') (l.app U t) y) := by rw [h.conj_form]
    have hY2 : ‖dbar (fun x => h.form (l.app U t) (l'.app U t') (c.e.symm x)) (c.e y)
          (EuclideanSpace.single 0 1) - h.form (l.app U t) (l'.app U t') y *
          dbar (fun x => (Real.log (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re : ℂ)) (c.e y)
          (EuclideanSpace.single 0 1)‖ ^ 2 =
        ((h.form (l'.app U t') (l'.app U t') y).re * (h.form (l.app U t) (l.app U t) y).re -
          ‖h.form (l.app U t) (l'.app U t') y‖ ^ 2) * (Real.pi * h.bcDens hS' hL' hQ' c y) := hY
    rw [e₁, e₂, dbar_conj, dbar_ofReal, ← map_mul, ← map_sub, Complex.norm_conj,
      Complex.norm_conj] at hY2
    exact hY2
  have c₁ := (chernDens_curve k X p σ).2 L (h.restrict hl hL) (H.restrict hl hL) U t ht c y hy hU
  have c₂ := (chernDens_curve k X p σ).2 L' (h.restrict hl' hL') (H.restrict hl' hL') U t' ht' c y hy hU
  have l₁ : leviForm (fun x => Real.log ((h.restrict hl hL).form t t (c.e.symm x)).re) (c.e y) =
      leviForm (fun x => Real.log (h.form (l.app U t) (l.app U t) (c.e.symm x)).re) (c.e y) :=
    leviForm_congr_germ (by
      filter_upwards [hn] with x hx
      rw [h.form_restrict hl hL _ _ hx.2])
  have l₂ : leviForm (fun x => Real.log ((h.restrict hl' hL').form t' t' (c.e.symm x)).re) (c.e y) =
      leviForm (fun x => Real.log (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re) (c.e y) :=
    leviForm_congr_germ (by
      filter_upwards [hn] with x hx
      rw [h.form_restrict hl' hL' _ _ hx.2])
  rw [l₁] at c₁
  rw [l₂] at c₂
  simp only [e₀] at hcalc
  rw [hdb, Complex.re_ofReal_mul, hcalc]
  exact green_algebra Real.pi _ _ (v y) _ _ _ _ _ _ _ _ _ n Real.pi_ne_zero pa pa'
    (hv U t t' y hU) hX hY' c₁ c₂

theorem green_cosSq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∀ (V L Q L' Q' : X.Modules) (l : L ⟶ V) (m : V ⟶ Q) (w : l ≫ m = 0) (l' : L' ⟶ V) (m' : V ⟶ Q') (w' : l' ≫ m' = 0) (hS : (ShortComplex.mk l m w).ShortExact) (hS' : (ShortComplex.mk l' m' w').ShortExact) (hL : IsVB L 1) (hQ : IsVB Q 1) (hL' : IsVB L' 1) (hQ' : IsVB Q' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l') (h : Met p σ V (1 + 1)), h.IsCInf → ∀ v : CxPts p σ → ℝ, IsCosSq h l l' v → ∀ n : ℕ, total (fun (c : AlgChart p σ 1) y => v y ^ (n + 1) * (c.chernDens (h.restrict hl hL).detWeight y - c.chernDens (h.restrict hl' hL').detWeight y) + (n + 1) * v y ^ n * (1 - v y) * (Met.bcDens (S := ShortComplex.mk l m w) h hS hL hQ c y - Met.bcDens (S := ShortComplex.mk l' m' w') h hS' hL' hQ' c y)) = 0 := by
  intro k _ X p σ _ _ _ hAn V L Q L' Q' l m w l' m' w' hS hS' hL hQ hL' hQ' hl hl' h H v hv n
  obtain ⟨m₀, hm₁, hm₂, hm₃⟩ := GlobalTheory.T.exists_C1_density_for_line_pair k X p σ V L L' (1 + 1) h l l' H hl hl' hL hL' n
  have st := GlobalTheory.T.chartwise_C1_density_of_compatible k X p σ hAn (fun c y => (((-(1 / Real.pi) : ℝ)) : ℂ) * m₀ c y)
    (fun c y hy => contDiffAt_const.mul (hm₁ c y hy))
    (fun c c' y hy hy' => by rw [hm₂ c c' y hy hy']; ring)
  rw [← st]
  exact total_congr fun c y hy =>
    green_density hS hS' hL hQ hL' hQ' hl hl' h H hv n hm₁ hm₃ c hy

end GlobalTheory.CurveDens
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_pair_extension_cosSq_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∀ (V L Q L' Q' : X.Modules) (l : L ⟶ V) (m : V ⟶ Q) (w : l ≫ m = 0) (l' : L' ⟶ V) (m' : V ⟶ Q') (w' : l' ≫ m' = 0) (hS : (ShortComplex.mk l m w).ShortExact) (hS' : (ShortComplex.mk l' m' w').ShortExact) (hL : IsVB L 1) (hQ : IsVB Q 1) (hL' : IsVB L' 1) (hQ' : IsVB Q' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l') (h : Met p σ V (1 + 1)), h.IsCInf → ∀ v : CxPts p σ → ℝ, IsCosSq h l l' v → ∀ n : ℕ, total (fun (c : AlgChart p σ 1) y => v y ^ (n + 1) * (c.chernDens (h.restrict hl hL).detWeight y - c.chernDens (h.restrict hl' hL').detWeight y) + (n + 1) * v y ^ n * (1 - v y) * (Met.bcDens (S := ShortComplex.mk l m w) h hS hL hQ c y - Met.bcDens (S := ShortComplex.mk l' m' w') h hS' hL' hQ' c y)) = 0 := by
  first | exact @GlobalTheory.CurveDens.green_cosSq | exact GlobalTheory.CurveDens.green_cosSq | (intros; apply GlobalTheory.CurveDens.green_cosSq <;> assumption)
end
