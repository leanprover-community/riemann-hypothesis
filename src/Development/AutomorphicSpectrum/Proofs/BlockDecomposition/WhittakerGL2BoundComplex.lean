import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.UnipotentTateFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFourierBoundSeminorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeminormCompUnitaryLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormWhittakerGL2LeIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralDecayProductLeRatioPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Gl2ComplexIwasawaDecomposition
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AestronglyMeasurableWhittakerDiagUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff
import BuildAid.ForwardExisting

section
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fourier_bound_seminorm : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (f : SchwartzMap (Fin 2 → ℂ) ℂ) (x ξ : ℂ),
    ‖sF f x ξ‖ ≤ C * pS N f * (dd x * dd ξ) := by
  first | exact @GlobalTheory.CompanionTheory.GodementFE.Unif.sF_decay_unif | exact GlobalTheory.CompanionTheory.GodementFE.Unif.sF_decay_unif | (intros; apply GlobalTheory.CompanionTheory.GodementFE.Unif.sF_decay_unif <;> assumption)
end

section
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seminorm_comp_unitary_le : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ κ : Matrix (Fin 2) (Fin 2) ℂ, κ * κᴴ = 1 →
    ∀ f : SchwartzMap (Fin 2 → ℂ) ℂ, ∃ f' : SchwartzMap (Fin 2 → ℂ) ℂ,
      (∀ v, f' v = f (Matrix.vecMul v κ)) ∧ pS N f' ≤ C * pS N f := by
  first | exact @GlobalTheory.CompanionTheory.UnitaryCompSchwartz.comp_unitary_bounded | exact GlobalTheory.CompanionTheory.UnitaryCompSchwartz.comp_unitary_bounded | (intros; apply GlobalTheory.CompanionTheory.UnitaryCompSchwartz.comp_unitary_bounded <;> assumption)
end

section
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_whittakerGL2_le_integral : ∀ (k : ℕ) (f f' : SchwartzMap (Fin 2 → ℂ) ℂ) (κ : Matrix (Fin 2) (Fin 2) ℂ) (A B D : ℂ),
    A ≠ 0 → D ≠ 0 → ‖κ.det‖ = 1 → (∀ v, f' v = f (Matrix.vecMul v κ)) →
    ‖W2 k f (!![A, B; 0, D] * κ)‖ ≤
      ‖A‖ * ‖D‖⁻¹ * ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * ‖sF f' (t * A) (t * D)⁻¹‖ := by
  first | exact @GlobalTheory.CompanionTheory.GodementFE.norm_whittakerGL2_triangular_le | exact GlobalTheory.CompanionTheory.GodementFE.norm_whittakerGL2_triangular_le | (intros; apply GlobalTheory.CompanionTheory.GodementFE.norm_whittakerGL2_triangular_le <;> assumption)
end

section
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_decay_product_le_ratio_pow : ∀ e : ℝ, 0 < e → e < 2 → ∃ c : ℝ, 0 ≤ c ∧ ∀ A D : ℂ, A ≠ 0 → D ≠ 0 →
    Integrable (fun t : ℂ => (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹)) ∧
    ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹) ≤ c * (‖A‖ / ‖D‖) ^ (-e) := by
  first | exact @GlobalTheory.CompanionTheory.GodementFE.TInt.tint | exact GlobalTheory.CompanionTheory.GodementFE.TInt.tint | (intros; apply GlobalTheory.CompanionTheory.GodementFE.TInt.tint <;> assumption)
end

section
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gl2_complex_iwasawa_decomposition_upper_unitary : ∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.det ≠ 0 → ∃ (κ : Matrix (Fin 2) (Fin 2) ℂ) (b : ℂ) (R : ℝ),
    0 < R ∧ R ^ 2 = ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 ∧ κ * κᴴ = 1 ∧ ‖κ.det‖ = 1 ∧
      g = !![g.det / (R : ℂ), b; 0, (R : ℂ)] * κ := by
  first | exact @GlobalTheory.CompanionTheory.GodementFE.Iwasawa.gl2_complex_iwasawa | exact GlobalTheory.CompanionTheory.GodementFE.Iwasawa.gl2_complex_iwasawa | (intros; apply GlobalTheory.CompanionTheory.GodementFE.Iwasawa.gl2_complex_iwasawa <;> assumption)
end

section
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aestronglyMeasurable_whittaker_diag_units : ∀ (k : ℕ) (f : SchwartzMap (Fin 2 → ℂ) ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ),
    AEStronglyMeasurable (fun a : ℂˣ => W2 k f (d2 a * g)) mulC := by
  first | exact @GlobalTheory.CompanionTheory.GodementFE.aestronglyMeasurable_whittakerGL2_diag | exact GlobalTheory.CompanionTheory.GodementFE.aestronglyMeasurable_whittakerGL2_diag | (intros; apply GlobalTheory.CompanionTheory.GodementFE.aestronglyMeasurable_whittakerGL2_diag <;> assumption)
end

section
section
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE

namespace GlobalTheory.CompanionTheory.GodementFE.Radial

theorem weight_eq (σ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    ‖z‖ ^ (2 * (σ / 2) - 2) * dd z + ‖z‖ ^ (2 * ((σ + 1) / 2) - 2) * dd z =
      (‖z‖ ^ 2)⁻¹ * (‖z‖ ^ σ * dd z + ‖z‖ ^ (σ + 1) * dd z) := by
  have hp : 0 < ‖z‖ := norm_pos_iff.2 hz
  have e1 : (2 * (σ / 2) - 2) = σ - 2 := by ring
  have e2 : (2 * ((σ + 1) / 2) - 2) = (σ + 1) - 2 := by ring
  rw [e1, e2, Real.rpow_sub hp, Real.rpow_sub hp, Real.rpow_two]
  simp only [div_eq_mul_inv]
  ring

theorem integrable_weight : ∀ σ : ℝ, 0 < σ → σ < 1 →
    Integrable (fun a : ℂˣ => ‖(a : ℂ)‖ ^ σ * dd a + ‖(a : ℂ)‖ ^ (σ + 1) * dd a) mulC := by
  intro σ h0 h1
  have hA := (wt_vol (σ / 2) (by linarith) (by linarith)).add
    (wt_vol ((σ + 1) / 2) (by linarith) (by linarith))
  have hB : Integrable (fun z : ℂ => (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) *
      (((‖z‖ ^ σ * dd z + ‖z‖ ^ (σ + 1) * dd z : ℝ)) : ℂ)) := by
    refine (hA.ofReal (𝕜 := ℂ)).congr ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with z hz
    have hz0 : z ≠ 0 := hz
    have := weight_eq σ hz0
    simp only [Pi.add_apply]
    rw [this]
    push_cast
    rfl
  have hF := (integrable_mulC_iff
    (fun z : ℂ => (((‖z‖ ^ σ * dd z + ‖z‖ ^ (σ + 1) * dd z : ℝ)) : ℂ))).2 hB
  simpa using hF.re

end GlobalTheory.CompanionTheory.GodementFE.Radial
end

open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_unit_norm_pow_decay : ∀ σ : ℝ, 0 < σ → σ < 1 →
    Integrable (fun a : ℂˣ => ‖(a : ℂ)‖ ^ σ * dd a + ‖(a : ℂ)‖ ^ (σ + 1) * dd a) mulC := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GodementFE.Radial.integrable_weight
end

section
noncomputable section

open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE

namespace GlobalTheory.CompanionTheory.AbsoluteW2Bounds

theorem pS_nonneg {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : ℕ) (f : SchwartzMap E ℂ) :
    0 ≤ pS N f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _

theorem doubleOverlap_le_preimage_inter {C1 c e : ℝ} {N : ℕ} (hC1 : 0 ≤ C1) (hc : 0 ≤ c)
    (b1 : ∀ (f : SchwartzMap (Fin 2 → ℂ) ℂ) (x ξ : ℂ), ‖sF f x ξ‖ ≤ C1 * pS N f * (dd x * dd ξ))
    (b5 : ∀ A D : ℂ, A ≠ 0 → D ≠ 0 →
      Integrable (fun t : ℂ => (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹)) ∧
      ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹) ≤ c * (‖A‖ / ‖D‖) ^ (-e))
    (k : ℕ) (f f' : SchwartzMap (Fin 2 → ℂ) ℂ) (κ : Matrix (Fin 2) (Fin 2) ℂ) (A B D : ℂ)
    (hA : A ≠ 0) (hD : D ≠ 0) (hκ : ‖κ.det‖ = 1) (hf : ∀ v, f' v = f (Matrix.vecMul v κ)) :
    ‖W2 k f (!![A, B; 0, D] * κ)‖ ≤ C1 * pS N f' * c * (‖A‖ / ‖D‖) ^ (1 - e) := by
  have hP : 0 ≤ pS N f' := pS_nonneg N f'
  have hr : 0 < ‖A‖ / ‖D‖ := div_pos (norm_pos_iff.2 hA) (norm_pos_iff.2 hD)
  obtain ⟨i5, l5⟩ := b5 A D hA hD
  have h3 := GlobalTheory.T.norm_whittakerGL2_le_integral k f f' κ A B D hA hD hκ hf
  have hint : ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * ‖sF f' (t * A) (t * D)⁻¹‖ ≤
      C1 * pS N f' * ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹) := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => by positivity)
      (i5.const_mul _) (Filter.Eventually.of_forall fun t => ?_)
    have := b1 f' (t * A) (t * D)⁻¹
    have h0 : 0 ≤ (‖t‖ ^ 2)⁻¹ := by positivity
    calc (‖t‖ ^ 2)⁻¹ * ‖sF f' (t * A) (t * D)⁻¹‖
        ≤ (‖t‖ ^ 2)⁻¹ * (C1 * pS N f' * (dd (t * A) * dd (t * D)⁻¹)) :=
          mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  have hmul : 0 ≤ C1 * pS N f' := mul_nonneg hC1 hP
  calc ‖W2 k f (!![A, B; 0, D] * κ)‖
      ≤ ‖A‖ * ‖D‖⁻¹ * (C1 * pS N f' * (c * (‖A‖ / ‖D‖) ^ (-e))) := by
        refine h3.trans (mul_le_mul_of_nonneg_left (hint.trans ?_) (by positivity))
        exact mul_le_mul_of_nonneg_left l5 hmul
    _ = C1 * pS N f' * c * ((‖A‖ / ‖D‖) * (‖A‖ / ‖D‖) ^ (-e)) := by
        rw [div_eq_mul_inv ‖A‖ ‖D‖]; ring
    _ = _ := by
        rw [sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one]

theorem two_bounds {X K1 K2 s σ : ℝ} (hs : 0 < s) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (b1 : X ≤ K1 * s ^ σ) (b2 : X ≤ K2 * s ^ (σ - 1)) :
    X ≤ 2 * (K1 + K2) * (s ^ σ * (1 + s ^ 2)⁻¹ + s ^ (σ + 1) * (1 + s ^ 2)⁻¹) := by
  have hp : 0 < s ^ σ := Real.rpow_pos_of_pos hs _
  have hq : 0 < s ^ (σ + 1) := Real.rpow_pos_of_pos hs _
  have hi : 0 < (1 + s ^ 2)⁻¹ := by positivity
  rcases le_total s 1 with hs1 | hs1
  · have hd : (1 : ℝ) ≤ 2 * (1 + s ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      nlinarith
    have e1 : K1 * s ^ σ ≤ 2 * (K1 + K2) * (s ^ σ * (1 + s ^ 2)⁻¹) := by
      have : s ^ σ ≤ s ^ σ * (2 * (1 + s ^ 2)⁻¹) := le_mul_of_one_le_right hp.le hd
      calc K1 * s ^ σ ≤ K1 * (s ^ σ * (2 * (1 + s ^ 2)⁻¹)) := mul_le_mul_of_nonneg_left this h1
        _ = 2 * K1 * (s ^ σ * (1 + s ^ 2)⁻¹) := by ring
        _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e2 : 0 ≤ 2 * (K1 + K2) * (s ^ (σ + 1) * (1 + s ^ 2)⁻¹) := by positivity
    linarith
  · have e : s ^ (σ - 1) = s ^ (σ + 1) * (s ^ 2)⁻¹ := by
      rw [← Real.rpow_natCast s 2, ← Real.rpow_neg hs.le, ← Real.rpow_add hs]
      congr 1
      push_cast
      ring
    have hd2 : (s ^ 2)⁻¹ ≤ 2 * (1 + s ^ 2)⁻¹ := by
      rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have e2 : K2 * s ^ (σ - 1) ≤ 2 * (K1 + K2) * (s ^ (σ + 1) * (1 + s ^ 2)⁻¹) := by
      rw [e]
      calc K2 * (s ^ (σ + 1) * (s ^ 2)⁻¹)
          ≤ K2 * (s ^ (σ + 1) * (2 * (1 + s ^ 2)⁻¹)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd2 hq.le) h2
        _ = 2 * K2 * (s ^ (σ + 1) * (1 + s ^ 2)⁻¹) := by ring
        _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e3 : 0 ≤ 2 * (K1 + K2) * (s ^ σ * (1 + s ^ 2)⁻¹) := by positivity
    linarith

theorem main : Ad3.K.LC.C.AbsoluteZetaIntegralBound := by
  intro k hk σ h0 h1
  obtain ⟨C1, N, hC1, b1⟩ := GlobalTheory.T.partial_fourier_bound_seminorm
  obtain ⟨C2, hC2, b2⟩ := GlobalTheory.T.seminorm_comp_unitary_le N
  obtain ⟨c1, hc1, b5⟩ := GlobalTheory.T.integral_decay_product_le_ratio_pow σ h0 (by linarith)
  obtain ⟨c2, hc2, b6⟩ := GlobalTheory.T.integral_decay_product_le_ratio_pow (σ + 1) (by linarith) (by linarith)
  have hI := GlobalTheory.T.integrable_unit_norm_pow_decay σ h0 h1
  set M : ℂˣ → ℝ := fun a => ‖(a : ℂ)‖ ^ σ * dd a + ‖(a : ℂ)‖ ^ (σ + 1) * dd a with hM
  have hM0 : ∀ a, 0 ≤ M a := fun a => by
    have := dd_pos (a : ℂ)
    simp only [hM]
    positivity
  have hJ : 0 ≤ ∫ a, M a ∂mulC := integral_nonneg hM0
  refine ⟨2 * (C1 * C2 * c1 + C1 * C2 * c2) * ∫ a, M a ∂mulC, N, fun f g hg => ?_⟩
  obtain ⟨κ, b, R, hR, hR2, hκ, hκd, hgκ⟩ := GlobalTheory.T.gl2_complex_iwasawa_decomposition_upper_unitary g hg
  obtain ⟨f', hf', hP⟩ := b2 κ hκ f
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  set y : ℂ := g.det / (R : ℂ) ^ 2 with hy
  have hy0 : y ≠ 0 := div_ne_zero hg (pow_ne_zero _ hRc)
  set yu : ℂˣ := Units.mk0 y hy0 with hyu
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hf0 : 0 ≤ pS N f := pS_nonneg N f
  have hf1 : 0 ≤ pS N f' := pS_nonneg N f'
  set Q : ℝ := pS N f with hQ
  have hpt : ∀ a : ℂˣ, ‖W2 k f (d2 a * g)‖ * ‖(a : ℂ)‖ ^ (2 * σ - 1) ≤
      (2 * (C1 * C2 * c1 + C1 * C2 * c2) * Q * ‖y‖ ^ (1 - 2 * σ)) * M (yu * a) := by
    intro a
    have ha : (a : ℂ) ≠ 0 := a.ne_zero
    have han : 0 < ‖(a : ℂ)‖ := norm_pos_iff.2 ha
    set s : ℝ := ‖y * (a : ℂ)‖ with hs
    have hs0 : 0 < s := norm_pos_iff.2 (mul_ne_zero hy0 ha)
    have hmat : d2 a * g = !![(a : ℂ) * (g.det / (R : ℂ)), (a : ℂ) * b; 0, (R : ℂ)] * κ := by
      conv_lhs => rw [hgκ]
      rw [← Matrix.mul_assoc]
      congr 1
      simp [d2, Matrix.mul_fin_two]
    have hA : (a : ℂ) * (g.det / (R : ℂ)) ≠ 0 := mul_ne_zero ha (div_ne_zero hg hRc)
    have hr : ‖(a : ℂ) * (g.det / (R : ℂ))‖ / ‖(R : ℂ)‖ = s := by
      have e : y * (a : ℂ) = (a : ℂ) * (g.det / (R : ℂ)) / (R : ℂ) := by
        rw [hy]; field_simp
      rw [hs, e, norm_div]
    have w1 := doubleOverlap_le_preimage_inter hC1 hc1 b1 (b5) k f f' κ _ ((a : ℂ) * b) _ hA hRc hκd hf'
    have w2 := doubleOverlap_le_preimage_inter hC1 hc2 b1 (b6) k f f' κ _ ((a : ℂ) * b) _ hA hRc hκd hf'
    rw [← hmat, hr] at w1 w2
    have hpow : ‖(a : ℂ)‖ ^ (2 * σ - 1) = ‖y‖ ^ (1 - 2 * σ) * s ^ (2 * σ - 1) := by
      have : s = ‖y‖ * ‖(a : ℂ)‖ := by rw [hs, norm_mul]
      rw [this, Real.mul_rpow hyn.le han.le, ← mul_assoc, ← Real.rpow_add hyn]
      simp
    set Y : ℝ := ‖y‖ ^ (1 - 2 * σ) with hY
    have hY0 : 0 < Y := Real.rpow_pos_of_pos hyn _
    have hPQ : C1 * pS N f' ≤ C1 * (C2 * Q) := mul_le_mul_of_nonneg_left hP hC1
    have hp2 : 0 ≤ s ^ (2 * σ - 1) := (Real.rpow_pos_of_pos hs0 _).le
    have u1 : ‖W2 k f (d2 a * g)‖ * ‖(a : ℂ)‖ ^ (2 * σ - 1) ≤ (C1 * C2 * c1 * Q * Y) * s ^ σ := by
      rw [hpow]
      have e : s ^ σ = s ^ (1 - σ) * s ^ (2 * σ - 1) := by
        rw [← Real.rpow_add hs0]; congr 1; ring
      have w1' : ‖W2 k f (d2 a * g)‖ ≤ C1 * (C2 * Q) * c1 * s ^ (1 - σ) := by
        refine w1.trans ?_
        have : 0 ≤ s ^ (1 - σ) := (Real.rpow_pos_of_pos hs0 _).le
        gcongr
      calc ‖W2 k f (d2 a * g)‖ * (Y * s ^ (2 * σ - 1))
          ≤ (C1 * (C2 * Q) * c1 * s ^ (1 - σ)) * (Y * s ^ (2 * σ - 1)) :=
            mul_le_mul_of_nonneg_right w1' (by positivity)
        _ = _ := by rw [e]; ring
    have u2 : ‖W2 k f (d2 a * g)‖ * ‖(a : ℂ)‖ ^ (2 * σ - 1) ≤
        (C1 * C2 * c2 * Q * Y) * s ^ (σ - 1) := by
      rw [hpow]
      have e : s ^ (σ - 1) = s ^ (1 - (σ + 1)) * s ^ (2 * σ - 1) := by
        rw [← Real.rpow_add hs0]; congr 1; ring
      have w2' : ‖W2 k f (d2 a * g)‖ ≤ C1 * (C2 * Q) * c2 * s ^ (1 - (σ + 1)) := by
        refine w2.trans ?_
        have : 0 ≤ s ^ (1 - (σ + 1)) := (Real.rpow_pos_of_pos hs0 _).le
        gcongr
      calc ‖W2 k f (d2 a * g)‖ * (Y * s ^ (2 * σ - 1))
          ≤ (C1 * (C2 * Q) * c2 * s ^ (1 - (σ + 1))) * (Y * s ^ (2 * σ - 1)) :=
            mul_le_mul_of_nonneg_right w2' (by positivity)
        _ = _ := by rw [e]; ring
    have hfin := two_bounds hs0 (K1 := C1 * C2 * c1 * Q * Y) (K2 := C1 * C2 * c2 * Q * Y)
      (by positivity) (by positivity) u1 u2
    have hMe : M (yu * a) = s ^ σ * (1 + s ^ 2)⁻¹ + s ^ (σ + 1) * (1 + s ^ 2)⁻¹ := by
      simp [hM, hyu, dd, hs]
    rw [hMe]
    refine hfin.trans (le_of_eq ?_)
    ring
  have hIy : Integrable (fun a : ℂˣ => M (yu * a)) mulC := hI.comp_mul_left yu
  have hmeas : AEStronglyMeasurable
      (fun a : ℂˣ => ‖W2 k f (d2 a * g)‖ * ‖(a : ℂ)‖ ^ (2 * σ - 1)) mulC := by
    refine (GlobalTheory.T.aestronglyMeasurable_whittaker_diag_units k f g).norm.mul ?_
    have hv : Measurable (Units.val : ℂˣ → ℂ) := val_measEmb.measurable
    exact (hv.norm.pow_const _).aestronglyMeasurable
  have hnn : ∀ a : ℂˣ, 0 ≤ ‖W2 k f (d2 a * g)‖ * ‖(a : ℂ)‖ ^ (2 * σ - 1) := fun a => by positivity
  have hdom := hIy.const_mul (2 * (C1 * C2 * c1 + C1 * C2 * c2) * Q * ‖y‖ ^ (1 - 2 * σ))
  refine ⟨hdom.mono' hmeas (Filter.Eventually.of_forall fun a => ?_), ?_⟩
  · rw [Real.norm_of_nonneg (hnn a)]
    exact hpt a
  · have hY : Yb g ^ (1 / 2 - σ) = ‖y‖ ^ (1 - 2 * σ) := by
      have e : Yb g = ‖y‖ ^ 2 := by
        rw [Yb, ← hR2, hy, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le]
        field_simp
      rw [e, ← Real.rpow_natCast, ← Real.rpow_mul hyn.le]
      congr 1
      push_cast
      ring
    calc ∫ a : ℂˣ, ‖W2 k f (d2 a * g)‖ * ‖(a : ℂ)‖ ^ (2 * σ - 1) ∂mulC
        ≤ ∫ a : ℂˣ, (2 * (C1 * C2 * c1 + C1 * C2 * c2) * Q * ‖y‖ ^ (1 - 2 * σ)) * M (yu * a) ∂mulC :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hdom
            (Filter.Eventually.of_forall hpt)
      _ = (2 * (C1 * C2 * c1 + C1 * C2 * c2) * Q * ‖y‖ ^ (1 - 2 * σ)) * ∫ a, M a ∂mulC := by
          rw [integral_const_mul, integral_mul_left_eq_self M yu]
      _ = _ := by rw [hY]; ring

end GlobalTheory.CompanionTheory.AbsoluteW2Bounds
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE

namespace GlobalTheory.CompanionTheory.WhittakerGL2Bound

open GlobalTheory.CompanionTheory.GodementFE.Unif in

def Pn (N : ℕ) : Seminorm ℝ Sp :=
  (Finset.Iic ((N, N) : ℕ × ℕ)).sup (schwartzSeminormFamily ℝ (Fin 2 → ℂ) ℂ)

open GlobalTheory.CompanionTheory.GodementFE.Unif in
theorem pS_le_Pn (N : ℕ) (f : Sp) : pS N f ≤ ((N : ℝ) + 1) ^ 2 * Pn N f := by
  have h : ∀ i ∈ Finset.range (N + 1), ∀ j ∈ Finset.range (N + 1),
      SchwartzMap.seminorm ℝ i j f ≤ Pn N f := by
    intro i hi j hj
    have hm : ((i, j) : ℕ × ℕ) ∈ Finset.Iic ((N, N) : ℕ × ℕ) := by
      rw [Finset.mem_Iic]
      exact ⟨by simpa using Nat.lt_succ_iff.1 (Finset.mem_range.1 hi),
        by simpa using Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)⟩
    exact Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ (Fin 2 → ℂ) ℂ) hm
  unfold pS
  calc _ ≤ ∑ _i ∈ Finset.range (N + 1), ∑ _j ∈ Finset.range (N + 1), Pn N f :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => h i hi j hj
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

open GlobalTheory.CompanionTheory.GodementFE.Unif in

theorem pS_comp_bound (N : ℕ) (T : Sp →L[ℝ] Sp) :
    ∃ (N' : ℕ) (D : ℝ), 0 ≤ D ∧ ∀ f : Sp, pS N (T f) ≤ D * pS N' f := by
  have hc : Continuous (Pn N) := Seminorm.continuous_finsetSup fun i _ =>
    (schwartz_withSeminorms ℝ (Fin 2 → ℂ) ℂ).continuous_seminorm i
  let q : Seminorm ℝ Sp := (Pn N).comp T.toLinearMap
  have hq : Continuous q := hc.comp T.continuous
  obtain ⟨u, C, -, hle⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ (Fin 2 → ℂ) ℂ) q hq
  have hN : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := by positivity
  refine ⟨u.sup fun i => max i.1 i.2, ((N : ℝ) + 1) ^ 2 * C, mul_nonneg hN C.2, fun f => ?_⟩
  have h1 : q f ≤ (C : ℝ) * (u.sup (schwartzSeminormFamily ℝ (Fin 2 → ℂ) ℂ)) f := hle f
  have h2 : (u.sup (schwartzSeminormFamily ℝ (Fin 2 → ℂ) ℂ)) f ≤
      pS (u.sup fun i => max i.1 i.2) f := by
    refine sup_le_pS u (fun i hi => ?_) f
    have := Finset.le_sup (f := fun i : ℕ × ℕ => max i.1 i.2) hi
    exact ⟨(le_max_left _ _).trans this, (le_max_right _ _).trans this⟩
  calc pS N (T f) ≤ ((N : ℝ) + 1) ^ 2 * q f := pS_le_Pn N (T f)
    _ ≤ ((N : ℝ) + 1) ^ 2 * ((C : ℝ) * pS (u.sup fun i => max i.1 i.2) f) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 C.2)) hN
    _ = _ := by ring

open GlobalTheory.CompanionTheory.GodementFE.Unif in

theorem schw_pow (a : ℕ) (f : Sp) (x u : ℂ) :
    ‖f ![x, u]‖ ≤ 2 ^ (2 * a + 4) * pS (2 * a + 4) f * (dd x ^ a * dd u ^ 2) := by
  set m : ℕ := 2 * a + 4 with hm
  set K : ℝ := 2 ^ m * pS m f with hK
  set v : Fin 2 → ℂ := ![x, u] with hv
  have h : (1 + ‖v‖) ^ m * ‖f v‖ ≤ K := by
    have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (m, 0)) (k := m) (n := 0)
      le_rfl le_rfl f v
    rw [norm_iteratedFDeriv_zero] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine sup_le_pS _ (fun i hi => ?_) f
    have h2 := Finset.mem_Iic.1 hi
    have h3 : i.1 ≤ m := h2.1
    have h4 : i.2 ≤ 0 := h2.2
    exact ⟨h3, by omega⟩
  have hx : ‖x‖ ≤ ‖v‖ := by simpa [hv] using norm_le_pi_norm v 0
  have hu : ‖u‖ ≤ ‖v‖ := by simpa [hv] using norm_le_pi_norm v 1
  have hr : 0 ≤ ‖v‖ := norm_nonneg _
  have hA : 1 + ‖x‖ ^ 2 ≤ (1 + ‖v‖) ^ 2 := by nlinarith [norm_nonneg x]
  have hB : 1 + ‖u‖ ^ 2 ≤ (1 + ‖v‖) ^ 2 := by nlinarith [norm_nonneg u]
  have hAB : (1 + ‖x‖ ^ 2) ^ a * (1 + ‖u‖ ^ 2) ^ 2 ≤ (1 + ‖v‖) ^ m := by
    have h1 : (1 + ‖x‖ ^ 2) ^ a ≤ ((1 + ‖v‖) ^ 2) ^ a := pow_le_pow_left₀ (by positivity) hA a
    have h2 : (1 + ‖u‖ ^ 2) ^ 2 ≤ ((1 + ‖v‖) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hB 2
    calc (1 + ‖x‖ ^ 2) ^ a * (1 + ‖u‖ ^ 2) ^ 2 ≤ ((1 + ‖v‖) ^ 2) ^ a * ((1 + ‖v‖) ^ 2) ^ 2 :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (1 + ‖v‖) ^ m := by rw [hm, ← pow_mul, ← pow_mul, ← pow_add]
  have h3 : (1 + ‖x‖ ^ 2) ^ a * (1 + ‖u‖ ^ 2) ^ 2 * ‖f v‖ ≤ K :=
    le_trans (mul_le_mul_of_nonneg_right hAB (norm_nonneg _)) h
  have hpos : 0 < (1 + ‖x‖ ^ 2) ^ a * (1 + ‖u‖ ^ 2) ^ 2 := by positivity
  have e : K * (dd x ^ a * dd u ^ 2) = K / ((1 + ‖x‖ ^ 2) ^ a * (1 + ‖u‖ ^ 2) ^ 2) := by
    simp only [dd, inv_pow]
    field_simp
  rw [e, le_div_iff₀ hpos, mul_comm]
  exact h3

open GlobalTheory.CompanionTheory.GodementFE.Unif in
theorem sF_x_decay (a : ℕ) : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (f : Sp) (x ξ : ℂ),
    ‖sF f x ξ‖ ≤ C * pS N f * dd x ^ a := by
  have hJ : 0 ≤ ∫ u : ℂ, dd u ^ 2 := integral_nonneg fun u => by positivity
  refine ⟨2 ^ (2 * a + 4) * ∫ u : ℂ, dd u ^ 2, 2 * a + 4, by positivity, fun f x ξ => ?_⟩
  set K : ℝ := 2 ^ (2 * a + 4) * pS (2 * a + 4) f with hK
  have h1 : ‖sF f x ξ‖ ≤ ∫ u : ℂ, K * dd x ^ a * dd u ^ 2 := by
    refine norm_integral_le_of_norm_le (dd_sq_int.const_mul _)
      (Eventually.of_forall fun u => ?_)
    rw [norm_mul, norm_psiC, mul_one]
    calc ‖f ![x, u]‖ ≤ K * (dd x ^ a * dd u ^ 2) := schw_pow a f x u
      _ = _ := by ring
  rw [integral_const_mul] at h1
  calc _ ≤ _ := h1
    _ = _ := by rw [hK]; ring

open GlobalTheory.CompanionTheory.GodementFE.Unif in
theorem sF_decay_ab (a b : ℕ) : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (f : Sp) (x ξ : ℂ),
    ‖sF f x ξ‖ ≤ C * pS N f * (dd x ^ (a + 1) * dd ξ ^ b) := by
  induction b with
  | zero =>
    obtain ⟨C, N, hC, h⟩ := sF_x_decay (a + 1)
    exact ⟨C, N, hC, fun f x ξ => by simpa using h f x ξ⟩
  | succ b ih =>
    obtain ⟨C, N, hC, h⟩ := ih
    obtain ⟨N1, D1, hD1, t1⟩ := pS_comp_bound N (T2 1)
    obtain ⟨N2, D2, hD2, t2⟩ := pS_comp_bound N (T2 Complex.I)
    refine ⟨C * (1 + D1 + D2), max N (max N1 N2), by positivity, fun f x ξ => ?_⟩
    set A := pS (max N (max N1 N2)) f with hA
    have p0 : pS N f ≤ A := pS_mono (le_max_left _ _) f
    have p1 : pS N (T2 1 f) ≤ D1 * A :=
      (t1 f).trans (mul_le_mul_of_nonneg_left
        (pS_mono ((le_max_left _ _).trans (le_max_right _ _)) f) hD1)
    have p2 : pS N (T2 Complex.I f) ≤ D2 * A :=
      (t2 f).trans (mul_le_mul_of_nonneg_left
        (pS_mono ((le_max_right _ _).trans (le_max_right _ _)) f) hD2)
    have hdx := (dd_pos x).le
    have hdξ := (dd_pos ξ).le
    set Wt : ℝ := dd x ^ a * dd ξ ^ b with hWt
    have hW0 : 0 ≤ Wt := by positivity
    have key : ∀ (g : Sp) (B : ℝ), pS N g ≤ B → ‖sF g x ξ‖ ≤ C * B * Wt * dd x := fun g B hB => by
      refine (h g x ξ).trans ?_
      have e : dd x ^ (a + 1) * dd ξ ^ b = Wt * dd x := by rw [hWt, pow_succ]; ring
      rw [e]
      calc C * pS N g * (Wt * dd x) ≤ C * B * (Wt * dd x) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hC) (by positivity)
        _ = _ := by ring
    have := decay_of_bounds f (C * A * Wt) (C * (D1 * A) * Wt) (C * (D2 * A) * Wt) x ξ
      (key f A p0) (by rw [← secondLineDeriv_apply]; exact key _ _ p1) (by rw [← secondLineDeriv_apply]; exact key _ _ p2)
    calc _ ≤ _ := this
      _ = _ := by rw [hWt, pow_succ (dd x), pow_succ (dd ξ)]; ring

theorem sF_decay_pow (B : ℕ) : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
    ∀ (f : SchwartzMap (Fin 2 → ℂ) ℂ) (x ξ : ℂ),
      ‖sF f x ξ‖ ≤ C * pS N f * (dd x * dd ξ) ^ (B + 1) := by
  obtain ⟨C, N, hC, h⟩ := sF_decay_ab B (B + 1)
  exact ⟨C, N, hC, fun f x ξ => by rw [mul_pow]; exact h f x ξ⟩

theorem log_one_add_inv_le (Y : ℝ) (hY : 0 < Y) :
    Real.log (1 + Y⁻¹) ≤ Real.log 2 + |Real.log Y| := by
  have hYi : 0 < Y⁻¹ := inv_pos.2 hY
  rcases le_total 1 Y with h | h
  · have h2 : 1 + Y⁻¹ ≤ 2 := by
      have := inv_le_one_of_one_le₀ h
      linarith
    have h3 := Real.log_le_log (by positivity) h2
    linarith [abs_nonneg (Real.log Y)]
  · have h2 : 1 + Y⁻¹ ≤ 2 * Y⁻¹ := by
      have := (one_le_inv₀ hY).2 h
      linarith
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_mul (by norm_num) hYi.ne', Real.log_inv] at h3
    linarith [neg_le_abs (Real.log Y)]

def rad (s r : ℝ) : ℝ := r * ((1 + r ^ 2)⁻¹ * (1 + (r * s) ^ 2)⁻¹)

theorem continuous_rad (s : ℝ) : Continuous (rad s) := by
  unfold rad
  refine continuous_id.mul (Continuous.mul ?_ ?_)
  · exact Continuous.inv₀ (by fun_prop) fun r => by positivity
  · exact Continuous.inv₀ (by fun_prop) fun r => by positivity

theorem rad_le_left (s : ℝ) {r : ℝ} (hr : 0 < r) : rad s r ≤ r * (1 + r ^ 2)⁻¹ := by
  unfold rad
  refine mul_le_mul_of_nonneg_left ?_ hr.le
  have h : (1 + (r * s) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (r * s)])
  have h0 : 0 ≤ (1 + r ^ 2)⁻¹ := by positivity
  nlinarith

theorem rad_le_right {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    rad s r ≤ (s ^ 2)⁻¹ * r ^ (-3 : ℝ) := by
  have e : r ^ (-3 : ℝ) = (r ^ 3)⁻¹ := by
    rw [Real.rpow_neg hr.le]
    norm_cast
  rw [e]
  unfold rad
  have h1 : (1 + r ^ 2)⁻¹ ≤ (r ^ 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have h2 : (1 + (r * s) ^ 2)⁻¹ ≤ ((r * s) ^ 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  calc r * ((1 + r ^ 2)⁻¹ * (1 + (r * s) ^ 2)⁻¹)
      ≤ r * ((r ^ 2)⁻¹ * ((r * s) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (by positivity)) hr.le
    _ = _ := by field_simp

theorem integral_left (a : ℝ) (ha : 0 < a) :
    ∫ r in Set.Ioc 0 a, r * (1 + r ^ 2)⁻¹ = Real.log (1 + a ^ 2) / 2 := by
  rw [← intervalIntegral.integral_of_le ha.le]
  have hd : ∀ x ∈ Set.uIcc 0 a, HasDerivAt (fun r : ℝ => Real.log (1 + r ^ 2) / 2)
      (x * (1 + x ^ 2)⁻¹) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_id x).pow 2).const_add 1
    have h2 : HasDerivAt (fun r : ℝ => Real.log (1 + r ^ 2) / 2) (2 * x / (1 + x ^ 2) / 2) x :=
      (h1.log (by positivity)).div_const 2
    convert h2 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp
  · refine Continuous.intervalIntegrable ?_ _ _
    refine continuous_id.mul (Continuous.inv₀ (by fun_prop) fun r => by positivity)

theorem rad_integrableOn (s : ℝ) (hs : 0 < s) : IntegrableOn (rad s) (Set.Ioi 0) := by
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 s⁻¹ ∪ Set.Ioi s⁻¹ :=
    (Set.Ioc_union_Ioi_eq_Ioi (inv_pos.2 hs).le).symm
  rw [hsplit]
  refine IntegrableOn.union (continuous_rad s).integrableOn_Ioc ?_
  have hb : IntegrableOn (fun r : ℝ => (s ^ 2)⁻¹ * r ^ (-3 : ℝ)) (Set.Ioi s⁻¹) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (inv_pos.2 hs)).const_mul _
  refine Integrable.mono' hb (continuous_rad s).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
  have hr0 : 0 < r := (inv_pos.2 hs).trans hr
  rw [Real.norm_of_nonneg (by unfold rad; positivity)]
  exact rad_le_right hs hr0

theorem rad_integral_le (s : ℝ) (hs : 0 < s) :
    ∫ r in Set.Ioi (0 : ℝ), rad s r ≤ 1 + |Real.log (s ^ 2)| := by
  have ha : 0 < s⁻¹ := inv_pos.2 hs
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 s⁻¹ ∪ Set.Ioi s⁻¹ :=
    (Set.Ioc_union_Ioi_eq_Ioi ha.le).symm
  have hi := rad_integrableOn s hs
  have hi1 : IntegrableOn (rad s) (Set.Ioc 0 s⁻¹) := hi.mono_set (by
    intro r hr; exact hr.1)
  have hi2 : IntegrableOn (rad s) (Set.Ioi s⁻¹) := hi.mono_set (by
    intro r hr; exact ha.trans hr)
  have hu : ∫ r in Set.Ioi (0 : ℝ), rad s r =
      (∫ r in Set.Ioc 0 s⁻¹, rad s r) + ∫ r in Set.Ioi s⁻¹, rad s r := by
    rw [hsplit]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hi1 hi2
  have hl : IntegrableOn (fun r : ℝ => r * (1 + r ^ 2)⁻¹) (Set.Ioc 0 s⁻¹) :=
    (continuous_id.mul (Continuous.inv₀ (by fun_prop) fun r => by positivity)).integrableOn_Ioc
  have h1 : ∫ r in Set.Ioc 0 s⁻¹, rad s r ≤ Real.log (1 + (s⁻¹) ^ 2) / 2 := by
    rw [← integral_left _ ha]
    exact setIntegral_mono_on hi1 hl measurableSet_Ioc fun r hr => rad_le_left s hr.1
  have hb : IntegrableOn (fun r : ℝ => (s ^ 2)⁻¹ * r ^ (-3 : ℝ)) (Set.Ioi s⁻¹) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ha).const_mul _
  have h2 : ∫ r in Set.Ioi s⁻¹, rad s r ≤ 1 / 2 := by
    have e : ∫ r in Set.Ioi s⁻¹, (s ^ 2)⁻¹ * r ^ (-3 : ℝ) = 1 / 2 := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) ha]
      have e2 : (s⁻¹) ^ ((-3 : ℝ) + 1) = s ^ 2 := by
        rw [show ((-3 : ℝ) + 1) = -2 by norm_num, Real.rpow_neg ha.le, Real.inv_rpow hs.le,
          inv_inv]
        norm_cast
      rw [e2]
      field_simp
      norm_num
    rw [← e]
    exact setIntegral_mono_on hi2 hb measurableSet_Ioi fun r hr =>
      rad_le_right hs (ha.trans hr)
  have h3 := log_one_add_inv_le (s ^ 2) (by positivity)
  have h4 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have e3 : (s⁻¹) ^ 2 = (s ^ 2)⁻¹ := by rw [inv_pow]
  rw [hu]
  rw [e3] at h1
  linarith [abs_nonneg (Real.log (s ^ 2))]

theorem tint_log : ∃ c : ℝ, 0 ≤ c ∧ ∀ A D : ℂ, A ≠ 0 → D ≠ 0 →
    ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹) ≤
      c * (1 + |Real.log ((‖A‖ / ‖D‖) ^ 2)|) := by
  set V : ℝ := (Module.finrank ℝ ℂ : ℝ) * (volume : Measure ℂ).real (Metric.ball 0 1) with hV
  have hV0 : 0 ≤ V := by positivity
  refine ⟨V, hV0, fun A D hA hD => ?_⟩
  have hAp : 0 < ‖A‖ := norm_pos_iff.2 hA
  have hDp : 0 < ‖D‖ := norm_pos_iff.2 hD
  set s : ℝ := ‖A‖ / ‖D‖ with hs
  have hs0 : 0 < s := div_pos hAp hDp
  set G : ℝ → ℝ := fun r => (1 + r ^ 2)⁻¹ * (1 + (r * s) ^ 2)⁻¹ with hG
  have hpt : ∀ t : ℂ, t ≠ 0 → (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹) =
      ‖D‖ ^ 2 * G ‖t * D‖ := by
    intro t ht
    have htp : 0 < ‖t‖ := norm_pos_iff.2 ht
    rw [GlobalTheory.CompanionTheory.GodementFE.TInt.dd_inv _ (mul_ne_zero ht hD)]
    have e : ‖t * D‖ * s = ‖t * A‖ := by
      rw [norm_mul, norm_mul, hs]
      field_simp
    simp only [hG, e, dd]
    rw [norm_mul]
    field_simp
    rw [norm_mul]
    ring
  have h1 : ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹) =
      ∫ t : ℂ, ‖D‖ ^ 2 * G ‖t * D‖ := by
    refine integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with t ht
    exact hpt t ht
  have h2 : ∫ t : ℂ, G ‖t * D‖ = (‖D‖ ^ 2)⁻¹ * ∫ u : ℂ, G ‖u‖ :=
    GlobalTheory.CompanionTheory.GodementFE.TInt.integral_comp_mulRight (fun u => G ‖u‖) D hD
  have h3 : ∫ u : ℂ, G ‖u‖ = V * ∫ r in Set.Ioi (0 : ℝ), rad s r := by
    rw [integral_fun_norm_addHaar (volume : Measure ℂ) G]
    simp only [Complex.finrank_real_complex, smul_eq_mul, hV, hG, rad]
    norm_num
    ring
  rw [h1, integral_const_mul, h2, h3]
  have e : ‖D‖ ^ 2 * ((‖D‖ ^ 2)⁻¹ * (V * ∫ r in Set.Ioi (0 : ℝ), rad s r)) =
      V * ∫ r in Set.Ioi (0 : ℝ), rad s r := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left (rad_integral_le s hs0) hV0

theorem dd_mul_le (a b : ℂ) : dd a * dd b ≤ (1 + (‖a‖ * ‖b‖) ^ 2)⁻¹ := by
  unfold dd
  rw [← mul_inv]
  refine inv_anti₀ (by positivity) ?_
  have h1 := sq_nonneg ‖a‖
  have h2 := sq_nonneg ‖b‖
  nlinarith [mul_pow ‖a‖ ‖b‖ 2]

theorem main : Ad3.K.LC.C.WhittakerSchwartzBound := by
  intro k _ N
  obtain ⟨C1, N1, hC1, b1⟩ := sF_decay_pow N
  obtain ⟨C2, hC2, b2⟩ := GlobalTheory.CompanionTheory.UnitaryCompSchwartz.comp_unitary_bounded N1
  obtain ⟨c, hc, b3⟩ := tint_log
  obtain ⟨c', _, b5⟩ := GlobalTheory.CompanionTheory.GodementFE.TInt.tint 1 one_pos (by norm_num)
  refine ⟨C1 * C2 * c, N1, fun f M hM => ?_⟩
  obtain ⟨κ, b, R, hR, hR2, hκ, hκd, hMκ⟩ := GlobalTheory.CompanionTheory.GodementFE.Iwasawa.gl2_complex_iwasawa M hM
  obtain ⟨f', hf', hP⟩ := b2 κ hκ f
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have hDn : ‖(R : ℂ)‖ = R := by rw [Complex.norm_real, Real.norm_of_nonneg hR.le]
  set A : ℂ := M.det / (R : ℂ) with hA
  have hA0 : A ≠ 0 := div_ne_zero hM hRc
  have hAp : 0 < ‖A‖ := norm_pos_iff.2 hA0
  set s : ℝ := ‖A‖ / ‖(R : ℂ)‖ with hs
  have hs0 : 0 < s := div_pos hAp (norm_pos_iff.2 hRc)
  have hY : Yb M = s ^ 2 := by
    rw [Yb, ← hR2, hs, hA, norm_div, hDn]
    field_simp
  have hY12 : Yb M ^ ((1 : ℝ) / 2) = s := by
    rw [hY, ← Real.sqrt_eq_rpow, Real.sqrt_sq hs0.le]
  have hQ0 : 0 ≤ pS N1 f' := GlobalTheory.CompanionTheory.AbsoluteW2Bounds.pS_nonneg N1 f'
  have hQ1 : 0 ≤ pS N1 f := GlobalTheory.CompanionTheory.AbsoluteW2Bounds.pS_nonneg N1 f
  have h3 := norm_whittakerGL2_triangular_le k f f' κ A b (R : ℂ) hA0 hRc hκd hf'
  rw [← hMκ] at h3
  obtain ⟨i5, -⟩ := b5 A (R : ℂ) hA0 hRc
  set w : ℝ := ((1 + s ^ 2)⁻¹) ^ N with hw
  have hw0 : 0 ≤ w := by positivity
  set K : ℝ := C1 * pS N1 f' * w with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ t : ℂ, t ≠ 0 → (‖t‖ ^ 2)⁻¹ * ‖sF f' (t * A) (t * (R : ℂ))⁻¹‖ ≤
      K * ((‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * (R : ℂ))⁻¹)) := by
    intro t ht
    have htp : 0 < ‖t‖ := norm_pos_iff.2 ht
    set p : ℝ := dd (t * A) * dd (t * (R : ℂ))⁻¹ with hp
    have hp0 : 0 ≤ p := mul_nonneg (dd_pos _).le (dd_pos _).le
    have hps : p ≤ (1 + s ^ 2)⁻¹ := by
      have e : ‖t * A‖ * ‖(t * (R : ℂ))⁻¹‖ = s := by
        rw [norm_inv, norm_mul, norm_mul, hs]
        field_simp
      have := dd_mul_le (t * A) (t * (R : ℂ))⁻¹
      rwa [e] at this
    have hpow : p ^ (N + 1) ≤ w * p := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp0 hps N) hp0
    have h1 := b1 f' (t * A) (t * (R : ℂ))⁻¹
    have h2 : ‖sF f' (t * A) (t * (R : ℂ))⁻¹‖ ≤ K * p :=
      h1.trans (by
        calc C1 * pS N1 f' * p ^ (N + 1) ≤ C1 * pS N1 f' * (w * p) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = K * p := by rw [hK]; ring)
    calc (‖t‖ ^ 2)⁻¹ * ‖sF f' (t * A) (t * (R : ℂ))⁻¹‖ ≤ (‖t‖ ^ 2)⁻¹ * (K * p) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  have hint : ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * ‖sF f' (t * A) (t * (R : ℂ))⁻¹‖ ≤
      K * ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * (R : ℂ))⁻¹) := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun t => by positivity)
      (i5.const_mul _) ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with t ht
    exact hpt t ht
  have hJ := b3 A (R : ℂ) hA0 hRc
  rw [← hs] at hJ
  set L : ℝ := 1 + |Real.log (s ^ 2)| with hL
  have hL0 : 0 ≤ L := by positivity
  have hfin : ‖W2 k f M‖ ≤ s * (K * (c * L)) := by
    have e : ‖A‖ * ‖(R : ℂ)‖⁻¹ = s := by rw [hs, div_eq_mul_inv]
    rw [e] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left
      (hint.trans (mul_le_mul_of_nonneg_left hJ hK0)) hs0.le)
  rw [hY12, hY, ← hL]
  have hwe : w = 1 / (1 + s ^ 2) ^ N := by rw [hw, inv_pow, one_div]
  have hCQ : C1 * pS N1 f' ≤ C1 * (C2 * pS N1 f) := mul_le_mul_of_nonneg_left hP hC1
  calc ‖W2 k f M‖ ≤ s * (K * (c * L)) := hfin
    _ = (C1 * pS N1 f') * (s * w * c * L) := by rw [hK]; ring
    _ ≤ (C1 * (C2 * pS N1 f)) * (s * w * c * L) :=
        mul_le_mul_of_nonneg_right hCQ (by positivity)
    _ = _ := by rw [hwe]; ring

end GlobalTheory.CompanionTheory.WhittakerGL2Bound
end
end
