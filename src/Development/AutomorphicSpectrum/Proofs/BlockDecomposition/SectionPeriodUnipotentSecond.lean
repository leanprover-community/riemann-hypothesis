import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.UnipotentTateFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantScaled
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateLocalL1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AestronglyMeasurableWhittakerDiagUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Ga

section
section
open MeasureTheory Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.MajC.TInt

open Ad3.K Ad3.K.LC Ad3.K.LC.B GlobalTheory.CompanionTheory.TateC

theorem integrable_mulC_real (g : ℂ → ℝ) :
    Integrable (fun a : ℂˣ => g a) mulC ↔ Integrable (fun x : ℂ => (‖x‖ ^ 2)⁻¹ • g x) volume := by
  have hd : Measurable fun x : ℂ => ENNReal.ofReal (‖x‖ ^ 2)⁻¹ := by fun_prop
  have h2 : Integrable (fun a : ℂˣ => g a) mulC ↔
      Integrable g (Measure.map (Units.val : ℂˣ → ℂ) mulC) :=
    (val_measurableEmbedding.integrable_map_iff (g := g)).symm
  rw [h2, map_val_mulC, nuC,
    integrable_withDensity_iff_integrable_smul' hd (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine integrable_congr (ae_of_all _ fun x => ?_)
  have : 0 ≤ (‖x‖ ^ 2)⁻¹ := by positivity
  simp only [ENNReal.toReal_ofReal this]

theorem integral_mulC_real (g : ℂ → ℝ) :
    ∫ a : ℂˣ, g a ∂mulC = ∫ x : ℂ, (‖x‖ ^ 2)⁻¹ • g x := by
  have h1 : ∫ a : ℂˣ, g a ∂mulC = ∫ x, g x ∂nuC := by
    rw [← map_val_mulC, val_measurableEmbedding.integral_map]
  rw [h1, nuC, integral_withDensity_eq_integral_toReal_smul₀ (by fun_prop) (by simp)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have : 0 ≤ (‖x‖ ^ 2)⁻¹ := by positivity
  simp only [ENNReal.toReal_ofReal this]

theorem density_le (σ : ℝ) (hσ : σ < 1) (N : ℕ) (hN : 4 - 4 * σ ≤ N) (q : ℝ) (hq : 0 < q)
    (z : ℂ) (hz : z ≠ 0) :
    (‖z‖ ^ 2)⁻¹ * (‖z‖ ^ (2 * σ - 2) / (1 + ‖z⁻¹‖ * q) ^ N) ≤
      q ^ (2 * σ - 2) * kern (2 - 2 * σ) q z := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hb := radial_bound (2 - 2 * σ) q ‖z‖ N (by linarith) hq hr (by linarith)
  have e1 : ‖z‖ ^ (-(2 + (2 - 2 * σ))) = (‖z‖ ^ 2)⁻¹ * ‖z‖ ^ (2 * σ - 2) := by
    rw [show -(2 + (2 - 2 * σ)) = (-2 : ℝ) + (2 * σ - 2) by ring, Real.rpow_add hr,
      Real.rpow_neg hr.le, Real.rpow_two]
  have e2 : ‖z⁻¹‖ * q = q / ‖z‖ := by
    rw [norm_inv]
    field_simp
  have e3 : -(2 - 2 * σ) = 2 * σ - 2 := by ring
  have hk : kern (2 - 2 * σ) q z =
      (‖z‖ ^ 2)⁻¹ * min ((‖z‖ / q) ^ (2 - 2 * σ)) ((q / ‖z‖) ^ (2 - 2 * σ)) := rfl
  rw [e1, e3] at hb
  rw [e2, hk, div_eq_mul_inv, ← mul_assoc]
  exact hb

theorem measurable_kern (s T : ℝ) : Measurable (kern s T) := by
  unfold kern
  fun_prop

theorem tint : ∀ σ : ℝ, σ < 1 → ∀ N : ℕ, 4 - 4 * σ ≤ N → ∃ K : ℝ, ∀ q : ℝ, 0 < q →
    Integrable (fun t : ℂˣ => ‖(t : ℂ)‖ ^ (2 * σ - 2) / (1 + ‖(t : ℂ)⁻¹‖ * q) ^ N) Ad3.K.mulC ∧
    ∫ t : ℂˣ, ‖(t : ℂ)‖ ^ (2 * σ - 2) / (1 + ‖(t : ℂ)⁻¹‖ * q) ^ N ∂Ad3.K.mulC ≤
      K * q ^ (2 * σ - 2) := by
  intro σ hσ N hN
  obtain ⟨K, hK0, hK⟩ := KernInt.lintegral_kern_le (2 - 2 * σ) (by linarith)
  refine ⟨K, fun q hq => ?_⟩
  set g : ℂ → ℝ := fun z => ‖z‖ ^ (2 * σ - 2) / (1 + ‖z⁻¹‖ * q) ^ N with hg
  have hkm := measurable_kern (2 - 2 * σ) q
  have hk0 : ∀ z, 0 ≤ kern (2 - 2 * σ) q z := kern_nonneg' _ _ hq
  have hfin : ∫⁻ z : ℂ, ENNReal.ofReal (kern (2 - 2 * σ) q z) < ⊤ :=
    (hK q hq).trans_lt ENNReal.ofReal_lt_top
  have hkI : Integrable (kern (2 - 2 * σ) q) volume := by
    refine ⟨hkm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hk0)]
    exact hfin
  have hkint : ∫ z : ℂ, kern (2 - 2 * σ) q z ≤ K := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hk0) hkm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hK0 (hK q hq)
  have hqp : 0 ≤ q ^ (2 * σ - 2) := (Real.rpow_pos_of_pos hq _).le
  have hae : ∀ᵐ z : ℂ, z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))
  have hgm : Measurable fun z : ℂ => (‖z‖ ^ 2)⁻¹ • g z := by
    simp only [hg]
    fun_prop
  have hg0 : ∀ z : ℂ, 0 ≤ (‖z‖ ^ 2)⁻¹ • g z := by
    intro z
    have : 0 ≤ ‖z‖ ^ (2 * σ - 2) := Real.rpow_nonneg (norm_nonneg _) _
    simp only [hg, smul_eq_mul]
    positivity
  have hle : ∀ᵐ z : ℂ, (‖z‖ ^ 2)⁻¹ • g z ≤ q ^ (2 * σ - 2) * kern (2 - 2 * σ) q z := by
    filter_upwards [hae] with z hz
    exact density_le σ hσ N hN q hq z hz
  have hbI : Integrable (fun z : ℂ => q ^ (2 * σ - 2) * kern (2 - 2 * σ) q z) volume :=
    hkI.const_mul _
  have hI : Integrable (fun z : ℂ => (‖z‖ ^ 2)⁻¹ • g z) volume := by
    refine hbI.mono' hgm.aestronglyMeasurable ?_
    filter_upwards [hle] with z hz
    rw [Real.norm_of_nonneg (hg0 z)]
    exact hz
  refine ⟨(integrable_mulC_real g).2 hI, ?_⟩
  have e := integral_mulC_real g
  calc ∫ t : ℂˣ, ‖(t : ℂ)‖ ^ (2 * σ - 2) / (1 + ‖(t : ℂ)⁻¹‖ * q) ^ N ∂Ad3.K.mulC
      = ∫ z : ℂ, (‖z‖ ^ 2)⁻¹ • g z := e
    _ ≤ ∫ z : ℂ, q ^ (2 * σ - 2) * kern (2 - 2 * σ) q z := integral_mono_ae hI hbI hle
    _ = q ^ (2 * σ - 2) * ∫ z : ℂ, kern (2 - 2 * σ) q z := integral_const_mul _ _
    _ ≤ q ^ (2 * σ - 2) * K := mul_le_mul_of_nonneg_left hkint hqp
    _ = K * q ^ (2 * σ - 2) := mul_comm _ _

end GlobalTheory.CompanionTheory.MajC.TInt
end
end

open MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_unit_pow_decay_le : ∀ σ : ℝ, σ < 1 → ∀ N : ℕ, 4 - 4 * σ ≤ N → ∃ K : ℝ, ∀ q : ℝ, 0 < q →
    Integrable (fun t : ℂˣ => ‖(t : ℂ)‖ ^ (2 * σ - 2) / (1 + ‖(t : ℂ)⁻¹‖ * q) ^ N) Ad3.K.mulC ∧
    ∫ t : ℂˣ, ‖(t : ℂ)‖ ^ (2 * σ - 2) / (1 + ‖(t : ℂ)⁻¹‖ * q) ^ N ∂Ad3.K.mulC ≤ K * q ^ (2 * σ - 2) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.MajC.TInt.tint
end

section
section
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE

namespace GlobalTheory.CompanionTheory.PerUC.Meas

theorem measurable_det_of : Measurable fun h : M22 => (Matrix.of h).det := by
  have h : Continuous fun h : M22 => (Matrix.of h).det :=
    Continuous.matrix_det (continuous_id (X := M22))
  exact h.measurable

theorem measurable_inv_entry (i j : Fin 2) :
    Measurable fun h : M22 => (Matrix.of h)⁻¹ i j := by
  have e : (fun h : M22 => (Matrix.of h)⁻¹ i j) =
      fun h : M22 => (Matrix.of h).det⁻¹ * (Matrix.of h).adjugate i j := by
    funext h
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  have hadj : Continuous fun h : M22 => (Matrix.of h).adjugate i j :=
    (Continuous.matrix_adjugate (continuous_id (X := M22))).matrix_elem i j
  exact measurable_det_of.inv.mul hadj.measurable

theorem measurable_det_inv : Measurable fun h : M22 => ((Matrix.of h)⁻¹).det := by
  have e : (fun h : M22 => ((Matrix.of h)⁻¹).det) = fun h : M22 =>
      (Matrix.of h)⁻¹ 0 0 * (Matrix.of h)⁻¹ 1 1 - (Matrix.of h)⁻¹ 0 1 * (Matrix.of h)⁻¹ 1 0 := by
    funext h
    exact Matrix.det_fin_two _
  rw [e]
  exact ((measurable_inv_entry 0 0).mul (measurable_inv_entry 1 1)).sub
    ((measurable_inv_entry 0 1).mul (measurable_inv_entry 1 0))

theorem continuous_innQ_integrand (Ψ : Sw) :
    Continuous fun p : (M22 × ℂ × (Fin 2 → ℂ)) × (Fin 2 → ℂ) =>
      Ψ (Matrix.of.symm (Matrix.of p.1.1 * blk p.2 *
          ((1 : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)), p.1.2.2) *
        psiC (-(p.1.2.1 * p.2 1)) := by
  refine Continuous.mul (Ψ.continuous.comp (Continuous.prodMk ?_ (by fun_prop)))
    (continuous_psiC.comp (by fun_prop))
  have hb : Continuous fun x : Fin 2 → ℂ => blk x := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [blk] <;> fun_prop
  have hh : Continuous fun p : (M22 × ℂ × (Fin 2 → ℂ)) × (Fin 2 → ℂ) => Matrix.of p.1.1 :=
    continuous_fst.fst
  exact (hh.matrix_mul (hb.comp continuous_snd)).matrix_mul continuous_const

theorem stronglyMeasurable_innQ (Ψ : Sw) :
    StronglyMeasurable fun p : M22 × ℂ × (Fin 2 → ℂ) => innQ Ψ 1 p.1 p.2.1 p.2.2 :=
  (continuous_innQ_integrand Ψ).stronglyMeasurable.integral_prod_right'

theorem measurable_whittakerGL2_inner_quotient : ∀ (k : ℕ) (Ψ : Ad3.K.LC.Sw),
    Measurable (fun p : ℂˣ × Ad3.K.LC.M22 =>
      Ad3.K.LC.C.W2 k (Ad3.K.LC.C.innQ Ψ 1 p.2 (p.1 : ℂ)⁻¹) (Matrix.of p.2)⁻¹) := by
  intro k Ψ
  have hT : Measurable fun p : ℂˣ × M22 => ((p.1 : ℂ))⁻¹ :=
    (GlobalTheory.CompanionTheory.TateC.val_measurableEmbedding.measurable.comp measurable_fst).inv
  have hE : ∀ i j : Fin 2, Measurable fun r : ((ℂˣ × M22) × ℂ) × ℂ =>
      (Matrix.of r.1.1.2)⁻¹ i j := fun i j =>
    (measurable_inv_entry i j).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
  have hV : Measurable fun r : ((ℂˣ × M22) × ℂ) × ℂ =>
      Matrix.vecMul ![r.1.2, r.1.2 * r.2] (Matrix.of r.1.1.2)⁻¹ := by
    refine measurable_pi_iff.2 fun j => ?_
    have e : (fun r : ((ℂˣ × M22) × ℂ) × ℂ =>
        Matrix.vecMul ![r.1.2, r.1.2 * r.2] (Matrix.of r.1.1.2)⁻¹ j) =
        fun r => r.1.2 * (Matrix.of r.1.1.2)⁻¹ 0 j + r.1.2 * r.2 * (Matrix.of r.1.1.2)⁻¹ 1 j := by
      funext r
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [e]
    have h1 : Measurable fun r : ((ℂˣ × M22) × ℂ) × ℂ => r.1.2 := measurable_snd.comp measurable_fst
    have h2 : Measurable fun r : ((ℂˣ × M22) × ℂ) × ℂ => r.2 := measurable_snd
    exact (h1.mul (hE 0 j)).add ((h1.mul h2).mul (hE 1 j))
  have hA : Measurable fun r : ((ℂˣ × M22) × ℂ) × ℂ =>
      ((r.1.1.2, ((r.1.1.1 : ℂ))⁻¹, Matrix.vecMul ![r.1.2, r.1.2 * r.2] (Matrix.of r.1.1.2)⁻¹) :
        M22 × ℂ × (Fin 2 → ℂ)) :=
    (measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
      ((hT.comp (measurable_fst.comp measurable_fst)).prodMk hV)
  have hG : StronglyMeasurable fun r : ((ℂˣ × M22) × ℂ) × ℂ =>
      innQ Ψ 1 r.1.1.2 ((r.1.1.1 : ℂ))⁻¹
          (Matrix.vecMul ![r.1.2, r.1.2 * r.2] (Matrix.of r.1.1.2)⁻¹) * psiC (-r.2) :=
    ((stronglyMeasurable_innQ Ψ).comp_measurable hA).mul
      (continuous_psiC.comp (continuous_snd.neg)).stronglyMeasurable
  have hF : StronglyMeasurable fun q : (ℂˣ × M22) × ℂ =>
      ∫ y : ℂ, innQ Ψ 1 q.1.2 ((q.1.1 : ℂ))⁻¹
          (Matrix.vecMul ![q.2, q.2 * y] (Matrix.of q.1.2)⁻¹) * psiC (-y) :=
    hG.integral_prod_right'
  have hP4 : StronglyMeasurable fun q : (ℂˣ × M22) × ℂ => ph (4 * (k : ℤ) - 4) q.2 :=
    ((measurable_ph _).comp measurable_snd).stronglyMeasurable
  have hH : StronglyMeasurable fun p : ℂˣ × M22 => ∫ t : ℂ, ph (4 * (k : ℤ) - 4) t *
      ∫ y : ℂ, innQ Ψ 1 p.2 ((p.1 : ℂ))⁻¹
          (Matrix.vecMul ![t, t * y] (Matrix.of p.2)⁻¹) * psiC (-y) :=
    (hP4.mul hF).integral_prod_right'
  have hD : Measurable fun p : ℂˣ × M22 => ((Matrix.of p.2)⁻¹).det :=
    measurable_det_inv.comp measurable_snd
  have hP2 : Measurable fun p : ℂˣ × M22 => ph (2 * (k : ℤ) - 2) ((Matrix.of p.2)⁻¹).det :=
    (measurable_ph _).comp hD
  have hN : Measurable fun p : ℂˣ × M22 => (((‖((Matrix.of p.2)⁻¹).det‖ : ℝ)) : ℂ) :=
    Complex.measurable_ofReal.comp hD.norm
  exact (hP2.mul hN).mul hH.measurable

end GlobalTheory.CompanionTheory.PerUC.Meas
end

open MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_whittaker_inner_quotient_inv : ∀ (k : ℕ) (Ψ : Ad3.K.LC.Sw), Measurable (fun p : ℂˣ × Ad3.K.LC.M22 => Ad3.K.LC.C.W2 k (Ad3.K.LC.C.innQ Ψ 1 p.2 (p.1 : ℂ)⁻¹) (Matrix.of p.2)⁻¹) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerUC.Meas.measurable_whittakerGL2_inner_quotient
end

section
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC

noncomputable section

namespace GlobalTheory.CompanionTheory.PerUC.GaInt

theorem measurable_ga (σ : ℝ) (m : ℕ) : Measurable (GlobalTheory.CompanionTheory.PerUC.ga σ m) := by
  unfold GlobalTheory.CompanionTheory.PerUC.ga kern
  refine Measurable.ite ?_ ?_ (by fun_prop)
  · have h1 : MeasurableSet {h : M22 | ‖h 1 0‖ ≤ ‖h 0 0‖} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have h2 : MeasurableSet {h : M22 | h 0 0 ≠ 0} :=
      (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl
    exact h1.inter h2
  · refine Measurable.mul (by fun_prop) (Measurable.mul (by fun_prop)
      (Measurable.min (by fun_prop) (by fun_prop)))

theorem ga_nonneg (σ : ℝ) (m : ℕ) (h : M22) : 0 ≤ GlobalTheory.CompanionTheory.PerUC.ga σ m h := by
  unfold GlobalTheory.CompanionTheory.PerUC.ga
  split_ifs with hc
  · have hr : 0 < ‖h 0 0‖ := norm_pos_iff.mpr hc.2
    have := GlobalTheory.CompanionTheory.MajGm.kern_nonneg (1 - σ) ‖h 0 0‖ hr (h 1 1 - h 1 0 / h 0 0 * h 0 1)
    have h0 := Real.rpow_nonneg hr.le (-2 - 2 * σ)
    positivity
  · exact le_rfl

theorem inner_le (σ K : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hK : 0 ≤ K)
    (hker : ∀ T₀ : ℝ, 0 < T₀ → ∫⁻ z : ℂ, ENNReal.ofReal (kern (1 - σ) T₀ z) ≤ ENNReal.ofReal K)
    (u x : ℂ) :
    ∫⁻ v : ℂ, ∫⁻ y : ℂ, ENNReal.ofReal (GlobalTheory.CompanionTheory.PerUC.ga σ 4 ![![u, x], ![v, y]]) ≤
      ENNReal.ofReal (Real.pi * K) * ENNReal.ofReal (kern (2 - 2 * σ) 1 u) *
        ENNReal.ofReal (((1 + ‖x‖) ^ 4)⁻¹) := by
  by_cases hu : u = 0
  · subst hu
    simp [GlobalTheory.CompanionTheory.PerUC.ga]
  have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hP : 0 < ‖u‖ ^ (-2 - 2 * σ) := Real.rpow_pos_of_pos hr _
  set A : ℝ := ‖u‖ ^ (-2 - 2 * σ) * ((1 + ‖u‖) ^ 4)⁻¹ * ((1 + ‖x‖) ^ 4)⁻¹ with hAdef
  have hA : 0 ≤ A := by positivity
  have h1 : ∀ v : ℂ, ∫⁻ y : ℂ, ENNReal.ofReal (GlobalTheory.CompanionTheory.PerUC.ga σ 4 ![![u, x], ![v, y]]) ≤
      (Metric.closedBall (0 : ℂ) ‖u‖).indicator
        (fun _ => ENNReal.ofReal A * ENNReal.ofReal K) v := by
    intro v
    by_cases hv : ‖v‖ ≤ ‖u‖
    · rw [Set.indicator_of_mem (by simpa using hv)]
      have e : ∀ y : ℂ, GlobalTheory.CompanionTheory.PerUC.ga σ 4 ![![u, x], ![v, y]] =
          A * kern (1 - σ) ‖u‖ (y - v / u * x) := by
        intro y
        simp [GlobalTheory.CompanionTheory.PerUC.ga, hv, hu, hAdef]
      simp_rw [e, ENNReal.ofReal_mul hA]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      rw [lintegral_sub_right_eq_self (fun z => ENNReal.ofReal (kern (1 - σ) ‖u‖ z)) (v / u * x)]
      exact hker _ hr
    · have e : ∀ y : ℂ, GlobalTheory.CompanionTheory.PerUC.ga σ 4 ![![u, x], ![v, y]] = 0 := by
        intro y
        simp [GlobalTheory.CompanionTheory.PerUC.ga, hv]
      simp [e]
  have hvol : volume (Metric.closedBall (0 : ℂ) ‖u‖) = ENNReal.ofReal (‖u‖ ^ 2 * Real.pi) := by
    rw [Complex.volume_closedBall, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow hr.le]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal]
    simp
  have hreal := GlobalTheory.CompanionTheory.MajGm.real_bound (2 - 2 * σ) ‖u‖ 4 (by linarith)
    (by push_cast; linarith) hr
  rw [show (-4 + (2 - 2 * σ) : ℝ) = -2 - 2 * σ by ring] at hreal
  have hkn := GlobalTheory.CompanionTheory.MajGm.kern_nonneg (2 - 2 * σ) 1 one_pos u
  have hfin : A * K * (‖u‖ ^ 2 * Real.pi) ≤
      Real.pi * K * kern (2 - 2 * σ) 1 u * ((1 + ‖x‖) ^ 4)⁻¹ := by
    have hc : 0 ≤ Real.pi * K * ((1 + ‖x‖) ^ 4)⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_left hreal hc
    calc A * K * (‖u‖ ^ 2 * Real.pi)
        = Real.pi * K * ((1 + ‖x‖) ^ 4)⁻¹ *
            (‖u‖ ^ (-2 - 2 * σ) * ((1 + ‖u‖) ^ 4)⁻¹ * ‖u‖ ^ 2) := by rw [hAdef]; ring
      _ ≤ _ := this
      _ = _ := by unfold kern; ring
  calc ∫⁻ v : ℂ, ∫⁻ y : ℂ, ENNReal.ofReal (GlobalTheory.CompanionTheory.PerUC.ga σ 4 ![![u, x], ![v, y]])
      ≤ ∫⁻ v : ℂ, (Metric.closedBall (0 : ℂ) ‖u‖).indicator
        (fun _ => ENNReal.ofReal A * ENNReal.ofReal K) v := lintegral_mono h1
    _ = ENNReal.ofReal A * ENNReal.ofReal K * volume (Metric.closedBall (0 : ℂ) ‖u‖) :=
        lintegral_indicator_const Metric.isClosed_closedBall.measurableSet _
    _ = ENNReal.ofReal (A * K * (‖u‖ ^ 2 * Real.pi)) := by
        rw [hvol, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (mul_nonneg hA hK)]
    _ ≤ ENNReal.ofReal (Real.pi * K * kern (2 - 2 * σ) 1 u * ((1 + ‖x‖) ^ 4)⁻¹) :=
        ENNReal.ofReal_le_ofReal hfin
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]

theorem ga_integrable : ∀ σ : ℝ, 0 < σ → σ < 1 → Measurable (GlobalTheory.CompanionTheory.PerUC.ga σ 4) ∧
    (∀ h, 0 ≤ GlobalTheory.CompanionTheory.PerUC.ga σ 4 h) ∧
    ∫⁻ h : Ad3.K.LC.M22, ENNReal.ofReal (GlobalTheory.CompanionTheory.PerUC.ga σ 4 h) < ⊤ := by
  intro σ hσ0 hσ1
  refine ⟨measurable_ga σ 4, ga_nonneg σ 4, ?_⟩
  obtain ⟨K, hK, hker⟩ := KernInt.lintegral_kern_le (1 - σ) (by linarith)
  obtain ⟨K', hK', hker'⟩ := KernInt.lintegral_kern_le (2 - 2 * σ) (by linarith)
  have hQ := GlobalTheory.CompanionTheory.MajGm.finite_Q 4 (by norm_num)
  have hmeas : Measurable fun h : M22 => ENNReal.ofReal (GlobalTheory.CompanionTheory.PerUC.ga σ 4 h) :=
    (measurable_ga σ 4).ennreal_ofReal
  have hf : Measurable fun u : ℂ =>
      ENNReal.ofReal (Real.pi * K) * ENNReal.ofReal (kern (2 - 2 * σ) 1 u) :=
    ((GlobalTheory.CompanionTheory.MajGm.measurable_kern (2 - 2 * σ) 1).ennreal_ofReal).const_mul _
  have hg : Measurable fun x : ℂ => ENNReal.ofReal (((1 + ‖x‖) ^ 4)⁻¹) := by
    refine Measurable.ennreal_ofReal ?_
    fun_prop
  rw [GlobalTheory.CompanionTheory.MajGm.lint_rows _ hmeas]
  calc ∫⁻ a : ℂ × ℂ, ∫⁻ v : ℂ, ∫⁻ y : ℂ,
        ENNReal.ofReal (GlobalTheory.CompanionTheory.PerUC.ga σ 4 ![![a.1, a.2], ![v, y]])
      ≤ ∫⁻ a : ℂ × ℂ, (ENNReal.ofReal (Real.pi * K) * ENNReal.ofReal (kern (2 - 2 * σ) 1 a.1)) *
          ENNReal.ofReal (((1 + ‖a.2‖) ^ 4)⁻¹) :=
        lintegral_mono fun a => inner_le σ K hσ0 hσ1 hK hker a.1 a.2
    _ = (∫⁻ u : ℂ, ENNReal.ofReal (Real.pi * K) * ENNReal.ofReal (kern (2 - 2 * σ) 1 u)) *
          ∫⁻ x : ℂ, ENNReal.ofReal (((1 + ‖x‖) ^ 4)⁻¹) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_mul hf.aemeasurable hg.aemeasurable
    _ ≤ (ENNReal.ofReal (Real.pi * K) * ENNReal.ofReal K') *
          ∫⁻ x : ℂ, ENNReal.ofReal (((1 + ‖x‖) ^ 4)⁻¹) := by
        rw [lintegral_const_mul _ (GlobalTheory.CompanionTheory.MajGm.measurable_kern (2 - 2 * σ) 1).ennreal_ofReal]
        gcongr
        exact hker' 1 one_pos
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hQ

end GlobalTheory.CompanionTheory.PerUC.GaInt
end
end

open MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_majorant_torus_lt_top : ∀ σ : ℝ, 0 < σ → σ < 1 → Measurable (GlobalTheory.CompanionTheory.PerUC.ga σ 4) ∧ (∀ h, 0 ≤ GlobalTheory.CompanionTheory.PerUC.ga σ 4 h) ∧
    ∫⁻ h : Ad3.K.LC.M22, ENNReal.ofReal (GlobalTheory.CompanionTheory.PerUC.ga σ 4 h) < ⊤ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerUC.GaInt.ga_integrable
end

section
section
open MeasureTheory Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.PerUC.GxLe

theorem one_var_small (s : ℝ) (hs0 : 0 < s) (r Y : ℝ) (N : ℕ) (hr : 0 < r) (hr1 : r ≤ 1)
    (h1 : r ^ 2 / 4 ≤ Y) (h2 : Y ≤ r ^ 2) :
    r ^ (2 * s) * ((1 + |Real.log Y|) / (1 + Y) ^ N) ≤ (51 + 2 / s) * min (r ^ s) (r⁻¹ ^ s) := by
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) h1
  have hp : 0 < r ^ s := Real.rpow_pos_of_pos hr _
  have hp1 : r ^ s ≤ 1 := Real.rpow_le_one hr.le hr1 hs0.le
  have hq : r⁻¹ ^ s * r ^ s = 1 := by
    rw [← Real.mul_rpow (inv_nonneg.2 hr.le) hr.le, inv_mul_cancel₀ hr.ne', Real.one_rpow]
  have hq1 : 1 ≤ r⁻¹ ^ s := Real.one_le_rpow ((one_le_inv₀ hr).2 hr1) hs0.le
  have hmin : min (r ^ s) (r⁻¹ ^ s) = r ^ s := min_eq_left (hp1.trans hq1)
  have hlog4 : Real.log 4 ≤ 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]
    have := Real.log_two_lt_d9
    linarith
  have hlogY : Real.log Y ≤ 0 := Real.log_nonpos hY.le (h2.trans (by nlinarith))
  have hlogr : Real.log (r ^ 2 / 4) ≤ Real.log Y := Real.log_le_log (by positivity) h1
  have hexp : Real.log (r ^ 2 / 4) = 2 * Real.log r - Real.log 4 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]; norm_num
  have habs : |Real.log Y| ≤ Real.log 4 + 2 * Real.log r⁻¹ := by
    rw [abs_of_nonpos hlogY, Real.log_inv]; linarith
  have hl : Real.log r⁻¹ ≤ r⁻¹ ^ s / s := Real.log_le_rpow_div (inv_nonneg.2 hr.le) hs0
  have hW : 1 ≤ (1 + Y) ^ N := one_le_pow₀ (by linarith)
  have hL0 : 0 ≤ 1 + |Real.log Y| := by positivity
  have hfrac : (1 + |Real.log Y|) / (1 + Y) ^ N ≤ 1 + |Real.log Y| := div_le_self hL0 hW
  have hkey : r ^ s * (1 + |Real.log Y|) ≤ 51 + 2 / s := by
    have e1 : r ^ s * (1 + |Real.log Y|) ≤ r ^ s * (3 + 2 * (r⁻¹ ^ s / s)) := by
      apply mul_le_mul_of_nonneg_left _ hp.le
      linarith
    have e2 : r ^ s * (3 + 2 * (r⁻¹ ^ s / s)) = 3 * r ^ s + 2 / s := by
      have : r ^ s * (2 * (r⁻¹ ^ s / s)) = 2 / s * (r⁻¹ ^ s * r ^ s) := by ring
      rw [mul_add, this, hq]; ring
    linarith
  rw [hmin, show r ^ (2 * s) = r ^ s * r ^ s by rw [two_mul, Real.rpow_add hr]]
  calc r ^ s * r ^ s * ((1 + |Real.log Y|) / (1 + Y) ^ N)
      ≤ r ^ s * r ^ s * (1 + |Real.log Y|) :=
        mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = (r ^ s * (1 + |Real.log Y|)) * r ^ s := by ring
    _ ≤ (51 + 2 / s) * r ^ s := mul_le_mul_of_nonneg_right hkey hp.le

theorem one_var_large (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) (r Y : ℝ) (N : ℕ) (hN : 3 ≤ N)
    (hr1 : 1 ≤ r) (h1 : r ^ 2 / 4 ≤ Y) (h2 : Y ≤ r ^ 2) :
    r ^ (2 * s) * ((1 + |Real.log Y|) / (1 + Y) ^ N) ≤ (51 + 2 / s) * min (r ^ s) (r⁻¹ ^ s) := by
  have hr : 0 < r := by linarith
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) h1
  have hp : 0 < r ^ s := Real.rpow_pos_of_pos hr _
  have hq0 : 0 < r⁻¹ ^ s := Real.rpow_pos_of_pos (inv_pos.2 hr) _
  have hq : r⁻¹ ^ s * r ^ s = 1 := by
    rw [← Real.mul_rpow (inv_nonneg.2 hr.le) hr.le, inv_mul_cancel₀ hr.ne', Real.one_rpow]
  have hq1 : r⁻¹ ^ s ≤ 1 :=
    Real.rpow_le_one (inv_nonneg.2 hr.le) (inv_le_one_of_one_le₀ hr1) hs0.le
  have hp1 : 1 ≤ r ^ s := Real.one_le_rpow hr1 hs0.le
  have hmin : min (r ^ s) (r⁻¹ ^ s) = r⁻¹ ^ s := min_eq_right (hq1.trans hp1)
  have hlog4 : Real.log 4 ≤ 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]
    have := Real.log_two_lt_d9
    linarith
  have hW1 : 1 ≤ 1 + Y := by linarith
  have hW0 : 0 < 1 + Y := by linarith
  have hL : 1 + |Real.log Y| ≤ 3 * (1 + Y) := by
    by_cases hY1 : 1 ≤ Y
    · rw [abs_of_nonneg (Real.log_nonneg hY1)]
      have := Real.log_le_sub_one_of_pos hY
      linarith
    · have hY2 : Y ≤ 1 := (not_le.1 hY1).le
      rw [abs_of_nonpos (Real.log_nonpos hY.le hY2)]
      have hq4 : (4 : ℝ)⁻¹ ≤ Y := by nlinarith
      have := Real.log_le_log (by norm_num) hq4
      rw [Real.log_inv] at this
      linarith
  have hr3 : r ^ (3 * s) ≤ 16 * (1 + Y) ^ 2 := by
    have a1 : r ^ (3 * s) ≤ r ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
    have a2 : r ^ (3 : ℝ) = r ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have a3 : r ^ 2 ≤ 4 * (1 + Y) := by linarith
    have a4 : r ^ 3 ≤ r ^ 2 * r ^ 2 := by nlinarith [sq_nonneg r, mul_nonneg (sq_nonneg r) (sub_nonneg.2 hr1), mul_nonneg (mul_nonneg (sq_nonneg r) hr.le) (sub_nonneg.2 hr1)]
    have a5 : r ^ 2 * r ^ 2 ≤ (4 * (1 + Y)) * (4 * (1 + Y)) :=
      mul_le_mul a3 a3 (by positivity) (by positivity)
    rw [a2] at a1
    calc r ^ (3 * s) ≤ r ^ 3 := a1
      _ ≤ r ^ 2 * r ^ 2 := a4
      _ ≤ (4 * (1 + Y)) * (4 * (1 + Y)) := a5
      _ = 16 * (1 + Y) ^ 2 := by ring
  have hWN : (1 + Y) ^ 3 ≤ (1 + Y) ^ N := pow_le_pow_right₀ hW1 hN
  have hmain : r ^ (3 * s) * (1 + |Real.log Y|) ≤ 48 * (1 + Y) ^ N := by
    calc r ^ (3 * s) * (1 + |Real.log Y|) ≤ 16 * (1 + Y) ^ 2 * (3 * (1 + Y)) :=
          mul_le_mul hr3 hL (by positivity) (by positivity)
      _ = 48 * (1 + Y) ^ 3 := by ring
      _ ≤ 48 * (1 + Y) ^ N := by linarith
  have h3 : r ^ (3 * s) = r ^ (2 * s) * r ^ s := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have hWp : 0 < (1 + Y) ^ N := by positivity
  rw [hmin]
  have hs2 : 0 < 2 / s := by positivity
  calc r ^ (2 * s) * ((1 + |Real.log Y|) / (1 + Y) ^ N)
      = (r ^ (2 * s) * (r⁻¹ ^ s * r ^ s)) * ((1 + |Real.log Y|) / (1 + Y) ^ N) := by
        rw [hq, mul_one]
    _ = (r ^ (3 * s) * (1 + |Real.log Y|) / (1 + Y) ^ N) * r⁻¹ ^ s := by rw [h3]; ring
    _ ≤ 48 * r⁻¹ ^ s :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hWp).2 hmain) hq0.le
    _ ≤ (51 + 2 / s) * r⁻¹ ^ s := mul_le_mul_of_nonneg_right (by linarith) hq0.le

theorem one_var (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) (r Y : ℝ) (N : ℕ) (hN : 3 ≤ N)
    (hr : 0 < r) (h1 : r ^ 2 / 4 ≤ Y) (h2 : Y ≤ r ^ 2) :
    r ^ (2 * s) * ((1 + |Real.log Y|) / (1 + Y) ^ N) ≤ (51 + 2 / s) * min (r ^ s) (r⁻¹ ^ s) := by
  rcases le_total r 1 with hr1 | hr1
  · exact one_var_small s hs0 r Y N hr hr1 h1 h2
  · exact one_var_large s hs0 hs1 r Y N hN hr1 h1 h2

theorem alg_id (a Z P Q L IA IB : ℝ) (ha : a ≠ 0) (hZ : Z ≠ 0) (hP : P ≠ 0) :
    ((a * Z) ^ 3)⁻¹ * (Z / a) * L * Q * (IA * IB) =
      ((a ^ 4)⁻¹ * P) * IA * IB * (Z ^ 2)⁻¹ * (Q / P * L) := by
  field_simp

theorem real_step (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (a Z R A B H : ℝ) (N : ℕ) (hN : 3 ≤ N)
    (ha : 0 < a) (hZ : 0 < Z) (hR1 : a ^ 2 ≤ R) (hR2 : R ≤ 2 * a ^ 2)
    (hA : 0 < A) (hB : 0 < B) (hHnn : 0 ≤ H⁻¹) (hH : H⁻¹ ≤ A⁻¹ * B⁻¹) :
    ((a * Z) ^ 3)⁻¹ * (((a * Z) ^ 2 / R ^ 2) ^ ((1 : ℝ) / 2) *
        (1 + |Real.log ((a * Z) ^ 2 / R ^ 2)|) / (1 + (a * Z) ^ 2 / R ^ 2) ^ N) *
      (a / (a * Z)) ^ (2 * σ - 2) / H ≤
    (51 + 2 / (1 - σ)) * (a ^ (-2 - 2 * σ) * A⁻¹ * B⁻¹ *
      ((Z ^ 2)⁻¹ * min ((Z / a) ^ (1 - σ)) ((a / Z) ^ (1 - σ)))) := by
  have hs0 : 0 < 1 - σ := by linarith
  have hs1 : 1 - σ ≤ 1 := by linarith
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR1
  have hr : 0 < Z / a := div_pos hZ ha
  have hYsq : (a * Z) ^ 2 / R ^ 2 = (a * Z / R) ^ 2 := by rw [div_pow]
  have hT : ((a * Z) ^ 2 / R ^ 2) ^ ((1 : ℝ) / 2) = a * Z / R := by
    rw [hYsq, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  have hT2 : a * Z / R ≤ Z / a := by
    rw [div_le_div_iff₀ hR0 ha]
    nlinarith [mul_le_mul_of_nonneg_left hR1 hZ.le]
  have hT1 : Z / a / 2 ≤ a * Z / R := by
    rw [div_div, div_le_div_iff₀ (by positivity) hR0]
    nlinarith [mul_le_mul_of_nonneg_left hR2 hZ.le]
  have hY2 : (a * Z) ^ 2 / R ^ 2 ≤ (Z / a) ^ 2 := by
    rw [hYsq]
    exact pow_le_pow_left₀ (by positivity) hT2 2
  have hY1 : (Z / a) ^ 2 / 4 ≤ (a * Z) ^ 2 / R ^ 2 := by
    rw [hYsq]
    calc (Z / a) ^ 2 / 4 = (Z / a / 2) ^ 2 := by ring
      _ ≤ (a * Z / R) ^ 2 := pow_le_pow_left₀ (by positivity) hT1 2
  have hone := one_var (1 - σ) hs0 hs1 (Z / a) ((a * Z) ^ 2 / R ^ 2) N hN hr hY1 hY2
  rw [inv_div] at hone
  have hcol : (a / (a * Z)) ^ (2 * σ - 2) = Z ^ (2 * (1 - σ)) := by
    have : a / (a * Z) = Z⁻¹ := by field_simp
    rw [this, Real.inv_rpow hZ.le, ← Real.rpow_neg hZ.le]
    congr 1
    ring
  have hrp : (Z / a) ^ (2 * (1 - σ)) = Z ^ (2 * (1 - σ)) / a ^ (2 * (1 - σ)) :=
    Real.div_rpow hZ.le ha.le _
  have hap : a ^ (-2 - 2 * σ) = (a ^ 4)⁻¹ * a ^ (2 * (1 - σ)) := by
    have e : (-2 - 2 * σ : ℝ) = -((4 : ℕ) : ℝ) + 2 * (1 - σ) := by push_cast; ring
    rw [e, Real.rpow_add ha, Real.rpow_neg ha.le, Real.rpow_natCast]
  rw [hT, hcol, hap]
  rw [hrp] at hone
  have hP : 0 < a ^ (2 * (1 - σ)) := Real.rpow_pos_of_pos ha _
  have hQ : 0 < Z ^ (2 * (1 - σ)) := Real.rpow_pos_of_pos hZ _
  generalize a ^ (2 * (1 - σ)) = P at *
  generalize Z ^ (2 * (1 - σ)) = Q at *
  generalize hLdef : (1 + |Real.log ((a * Z) ^ 2 / R ^ 2)|) / (1 + (a * Z) ^ 2 / R ^ 2) ^ N = L at *
  have hL0 : 0 ≤ L := by
    rw [← hLdef]
    positivity
  have e1 : ((a * Z) ^ 3)⁻¹ * (a * Z / R * (1 + |Real.log ((a * Z) ^ 2 / R ^ 2)|) /
        (1 + (a * Z) ^ 2 / R ^ 2) ^ N) * Q / H = ((a * Z) ^ 3)⁻¹ * (a * Z / R) * L * Q * H⁻¹ := by
    rw [← hLdef]
    ring
  have hfac : 0 ≤ ((a ^ 4)⁻¹ * P) * A⁻¹ * B⁻¹ * (Z ^ 2)⁻¹ := by positivity
  rw [e1]
  calc ((a * Z) ^ 3)⁻¹ * (a * Z / R) * L * Q * H⁻¹
      ≤ ((a * Z) ^ 3)⁻¹ * (Z / a) * L * Q * (A⁻¹ * B⁻¹) := by
        have : ((a * Z) ^ 3)⁻¹ * (a * Z / R) * L * Q ≤ ((a * Z) ^ 3)⁻¹ * (Z / a) * L * Q := by
          gcongr
        exact mul_le_mul this hH (hHnn) (by positivity)
    _ = ((a ^ 4)⁻¹ * P) * A⁻¹ * B⁻¹ * (Z ^ 2)⁻¹ * (Q / P * L) :=
        alg_id a Z P Q L A⁻¹ B⁻¹ ha.ne' hZ.ne' hP.ne'
    _ ≤ ((a ^ 4)⁻¹ * P) * A⁻¹ * B⁻¹ * (Z ^ 2)⁻¹ *
          ((51 + 2 / (1 - σ)) * min ((Z / a) ^ (1 - σ)) ((a / Z) ^ (1 - σ))) :=
        mul_le_mul_of_nonneg_left hone hfac
    _ = _ := by ring

open GlobalTheory.CompanionTheory.MajC in

theorem gx_le_ga : ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ (C : ℝ) (N₀ : ℕ), ∀ N ≥ N₀, ∀ h : Ad3.K.LC.M22,
    ‖h 1 0‖ ≤ ‖h 0 0‖ → GlobalTheory.CompanionTheory.MajC.dt h ≠ 0 →
    GlobalTheory.CompanionTheory.PerUC.gx σ N h ≤ C * GlobalTheory.CompanionTheory.PerUC.ga σ 4 h := by
  intro σ hσ0 hσ1
  refine ⟨51 + 2 / (1 - σ), 8, fun N hN h hv hd => ?_⟩
  have hu : h 0 0 ≠ 0 := by
    intro hu
    have hv0 : h 1 0 = 0 := by
      rw [hu, norm_zero] at hv
      exact norm_le_zero_iff.1 hv
    apply hd
    rw [dt_eq, hu, hv0]
    simp
  have hga : GlobalTheory.CompanionTheory.PerUC.ga σ 4 h = ‖h 0 0‖ ^ (-2 - 2 * σ) * ((1 + ‖h 0 0‖) ^ 4)⁻¹ *
      ((1 + ‖h 0 1‖) ^ 4)⁻¹ * kern (1 - σ) ‖h 0 0‖ (h 1 1 - h 1 0 / h 0 0 * h 0 1) := by
    unfold GlobalTheory.CompanionTheory.PerUC.ga
    rw [if_pos ⟨hv, hu⟩]
  rw [hga]
  set z := h 1 1 - h 1 0 / h 0 0 * h 0 1 with hz
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = h 0 0 * z := by
    rw [hz]; field_simp
  have hU : 0 < ‖h 0 0‖ := norm_pos_iff.2 hu
  have hdt : dt h = ‖h 0 0‖ * ‖z‖ := by rw [dt_eq, hdet, norm_mul]
  have hZ : 0 < ‖z‖ := by
    have : 0 < dt h := lt_of_le_of_ne (by rw [dt_eq]; exact norm_nonneg _) (Ne.symm hd)
    rw [hdt] at this
    exact (pos_iff_pos_of_mul_pos this).1 hU
  have hcol : GlobalTheory.CompanionTheory.MajC.col h = ‖h 0 0‖ := max_eq_left hv
  have hk : kern (1 - σ) ‖h 0 0‖ z = (‖z‖ ^ 2)⁻¹ *
      min ((‖z‖ / ‖h 0 0‖) ^ (1 - σ)) ((‖h 0 0‖ / ‖z‖) ^ (1 - σ)) := rfl
  have hA : ((1 + ‖h‖) ^ N)⁻¹ ≤ ((1 + ‖h 0 0‖) ^ 4)⁻¹ * ((1 + ‖h 0 1‖) ^ 4)⁻¹ := by
    rw [← mul_inv]
    apply inv_anti₀ (by positivity)
    have h1 : 1 + ‖h 0 0‖ ≤ 1 + ‖h‖ := by linarith [entry_le h 0 0]
    have h2 : 1 + ‖h 0 1‖ ≤ 1 + ‖h‖ := by linarith [entry_le h 0 1]
    have h3 : (1 : ℝ) ≤ 1 + ‖h‖ := by linarith [norm_nonneg h]
    calc (1 + ‖h 0 0‖) ^ 4 * (1 + ‖h 0 1‖) ^ 4
        ≤ (1 + ‖h‖) ^ 4 * (1 + ‖h‖) ^ 4 := by gcongr
      _ = (1 + ‖h‖) ^ 8 := by ring
      _ ≤ (1 + ‖h‖) ^ N := pow_le_pow_right₀ h3 hN
  have hgx : GlobalTheory.CompanionTheory.PerUC.gx σ N h = (dt h ^ 3)⁻¹ *
      ((dt h ^ 2 / GlobalTheory.CompanionTheory.PerUC.rr h ^ 2) ^ ((1 : ℝ) / 2) *
        (1 + |Real.log (dt h ^ 2 / GlobalTheory.CompanionTheory.PerUC.rr h ^ 2)|) /
        (1 + dt h ^ 2 / GlobalTheory.CompanionTheory.PerUC.rr h ^ 2) ^ N) *
      (GlobalTheory.CompanionTheory.MajC.col h / dt h) ^ (2 * σ - 2) / (1 + ‖h‖) ^ N := rfl
  have hR1 : ‖h 0 0‖ ^ 2 ≤ GlobalTheory.CompanionTheory.PerUC.rr h := by
    unfold GlobalTheory.CompanionTheory.PerUC.rr
    nlinarith [sq_nonneg ‖h 1 0‖]
  have hR2 : GlobalTheory.CompanionTheory.PerUC.rr h ≤ 2 * ‖h 0 0‖ ^ 2 := by
    unfold GlobalTheory.CompanionTheory.PerUC.rr
    nlinarith [norm_nonneg (h 1 0)]
  rw [hgx, hk, hdt, hcol]
  exact real_step σ hσ0 hσ1 ‖h 0 0‖ ‖z‖ _ _ _ _ N (by omega) hU hZ hR1 hR2
    (by positivity) (by positivity) (by positivity) hA

end GlobalTheory.CompanionTheory.PerUC.GxLe
end
end

open MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorant_le_const_mul_torus : ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ (C : ℝ) (N₀ : ℕ), ∀ N ≥ N₀, ∀ h : Ad3.K.LC.M22, ‖h 1 0‖ ≤ ‖h 0 0‖ → GlobalTheory.CompanionTheory.MajC.dt h ≠ 0 →
    GlobalTheory.CompanionTheory.PerUC.gx σ N h ≤ C * GlobalTheory.CompanionTheory.PerUC.ga σ 4 h := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerUC.GxLe.gx_le_ga
end

section
noncomputable section
open MeasureTheory Matrix Filter Topology Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C
namespace GlobalTheory.CompanionTheory.PerUC

def rtEquiv (g : GL (Fin 3) ℂ) : M23 ≃L[ℝ] M23 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun X => Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℂ))
      invFun := fun X => Matrix.of.symm (Matrix.of X * ((g⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ))
      map_add' := fun X Y => by
        show Matrix.of.symm ((Matrix.of X + Matrix.of Y) * (g : Matrix (Fin 3) (Fin 3) ℂ)) = _
        rw [Matrix.add_mul]
        rfl
      map_smul' := fun c X => by
        show Matrix.of.symm ((c • Matrix.of X) * (g : Matrix (Fin 3) (Fin 3) ℂ)) = _
        rw [Matrix.smul_mul]
        rfl
      left_inv := fun X => by
        simp [Matrix.mul_assoc]
      right_inv := fun X => by
        simp [Matrix.mul_assoc] }

def rtS (g : GL (Fin 3) ℂ) (Ψ : Sw) : Sw :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((rtEquiv g).prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℂ))) Ψ

theorem rtS_apply (g : GL (Fin 3) ℂ) (Ψ : Sw) (X : M23) (q : Fin 2 → ℂ) :
    rtS g Ψ (X, q) = Ψ (Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℂ)), q) := by
  simp [rtS, rtEquiv]

theorem innQ_rt (Ψ : Sw) (g : GL (Fin 3) ℂ) (h : M22) (β : ℂ) :
    innQ Ψ g h β = innQ (rtS g Ψ) 1 h β := by
  funext q
  unfold innQ
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [rtS_apply]

theorem pS_nonneg {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : ℕ)
    (f : SchwartzMap E ℂ) : 0 ≤ pS N f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _

theorem pS_mono {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℕ} (hab : a ≤ b)
    (f : SchwartzMap E ℂ) : pS a f ≤ pS b f := by
  unfold pS
  have hs : Finset.range (a + 1) ⊆ Finset.range (b + 1) :=
    Finset.range_subset_range.2 (by omega)
  refine (Finset.sum_le_sum fun i _ => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hs fun i _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
  exact Finset.sum_le_sum_of_subset_of_nonneg hs fun _ _ _ => apply_nonneg _ _

theorem eta_entries (h : M22) : eta h 0 = (Matrix.of h).det⁻¹ * (-h 1 0) ∧
    eta h 1 = (Matrix.of h).det⁻¹ * h 0 0 := by
  constructor <;> simp [eta, Matrix.inv_def, Matrix.adjugate_fin_two]

theorem norm_eta (h : M22) (hd : (Matrix.of h).det ≠ 0) :
    ‖eta h‖ = GlobalTheory.CompanionTheory.MajC.col h / GlobalTheory.CompanionTheory.MajC.dt h := by
  have := (GlobalTheory.CompanionTheory.MajC.L_eta h hd).2
  rw [← this]
  rfl

theorem Yb_inv (h : M22) (hd : (Matrix.of h).det ≠ 0) : Yb (Matrix.of h)⁻¹ = yb h := by
  have hD : 0 < GlobalTheory.CompanionTheory.MajC.dt h := norm_pos_iff.2 hd
  obtain ⟨e0, e1⟩ := eta_entries h
  have a0 : ((Matrix.of h)⁻¹) 1 0 = (Matrix.of h).det⁻¹ * (-h 1 0) := e0
  have a1 : ((Matrix.of h)⁻¹) 1 1 = (Matrix.of h).det⁻¹ * h 0 0 := e1
  have hdet : ((Matrix.of h)⁻¹).det = (Matrix.of h).det⁻¹ := by
    rw [Matrix.det_nonsing_inv]
    simp
  unfold Yb yb rr
  rw [hdet, a0, a1]
  simp only [norm_mul, norm_inv, norm_neg]
  change (GlobalTheory.CompanionTheory.MajC.dt h)⁻¹ ^ 2 / (((GlobalTheory.CompanionTheory.MajC.dt h)⁻¹ * ‖h 1 0‖) ^ 2 + ((GlobalTheory.CompanionTheory.MajC.dt h)⁻¹ * ‖h 0 0‖) ^ 2) ^ 2 = _
  have hc := (GlobalTheory.CompanionTheory.MajC.L_eta h hd).1
  have hR : 0 < ‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2 := by
    rcases max_cases ‖h 0 0‖ ‖h 1 0‖ with ⟨e, -⟩ | ⟨e, -⟩ <;>
      · unfold GlobalTheory.CompanionTheory.MajC.col at hc
        rw [e] at hc
        positivity
  have e : ((GlobalTheory.CompanionTheory.MajC.dt h)⁻¹ * ‖h 1 0‖) ^ 2 + ((GlobalTheory.CompanionTheory.MajC.dt h)⁻¹ * ‖h 0 0‖) ^ 2 =
      ((GlobalTheory.CompanionTheory.MajC.dt h)⁻¹) ^ 2 * (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) := by ring
  rw [e]
  generalize ‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2 = R at hR
  field_simp

theorem norm_chC' (n : ℤ) (s : ℂ) (t : ℂˣ) : ‖chC n s t‖ = ‖(t : ℂ)‖ ^ (2 * s.re) := by
  have ht : 0 < ‖(t : ℂ)‖ := norm_pos_iff.2 t.ne_zero
  have h1 : ‖((t : ℂ) / ‖(t : ℂ)‖)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self ht.ne']
  unfold chC
  rw [norm_mul, norm_zpow, h1, _root_.one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  norm_num

theorem measurable_chC' (n : ℤ) (s : ℂ) : Measurable (chC n s) := by
  have hv : Measurable (Units.val : ℂˣ → ℂ) := GlobalTheory.CompanionTheory.TateC.val_measurableEmbedding.measurable
  have h1 : Measurable fun a : ℂˣ => ph n (a : ℂ) := (GlobalTheory.CompanionTheory.GodementFE.measurable_ph n).comp hv
  have h2 : Measurable fun a : ℂˣ => (((‖(a : ℂ)‖ ^ 2 : ℝ) : ℂ)) ^ s := by
    refine Measurable.pow_const ?_ s
    exact Complex.measurable_ofReal.comp ((hv.norm).pow_const 2)
  exact h1.mul h2

theorem gx_nonneg (σ : ℝ) (N : ℕ) (h : M22) : 0 ≤ gx σ N h := by
  have hD : 0 ≤ GlobalTheory.CompanionTheory.MajC.dt h := norm_nonneg _
  have hc : 0 ≤ GlobalTheory.CompanionTheory.MajC.col h := le_max_of_le_left (norm_nonneg _)
  have hy : 0 ≤ yb h := by unfold yb; positivity
  unfold gx
  positivity

theorem rr_swp (h : M22) : rr (GlobalTheory.CompanionTheory.MajC.swp h) = rr h := by
  simp [rr, GlobalTheory.CompanionTheory.MajC.swp, add_comm]

theorem gx_swp (σ : ℝ) (N : ℕ) (h : M22) : gx σ N (GlobalTheory.CompanionTheory.MajC.swp h) = gx σ N h := by
  unfold gx yb
  rw [GlobalTheory.CompanionTheory.MajC.dt_swp, GlobalTheory.CompanionTheory.MajC.col_swp, GlobalTheory.CompanionTheory.MajC.norm_swp, rr_swp]

theorem measurable_swp : Measurable GlobalTheory.CompanionTheory.MajC.swp := by
  unfold GlobalTheory.CompanionTheory.MajC.swp
  refine measurable_pi_lambda _ fun i => ?_
  fin_cases i
  · exact measurable_pi_apply 1
  · exact measurable_pi_apply 0

theorem measurable_gx (σ : ℝ) (N : ℕ) : Measurable (gx σ N) := by
  have hdt : Measurable GlobalTheory.CompanionTheory.MajC.dt := by
    unfold GlobalTheory.CompanionTheory.MajC.dt
    simp only [Matrix.det_fin_two, Matrix.of_apply]
    fun_prop
  have hcol : Measurable GlobalTheory.CompanionTheory.MajC.col := by
    unfold GlobalTheory.CompanionTheory.MajC.col
    fun_prop
  have hrr : Measurable rr := by
    unfold rr
    fun_prop
  have hyb : Measurable yb := by
    unfold yb
    fun_prop
  have hlog : Measurable fun h => Real.log (yb h) := Real.measurable_log.comp hyb
  unfold gx
  fun_prop

theorem hint : ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ N₀ : ℕ, ∀ N ≥ N₀, Integrable (gx σ N) := by
  intro σ h0 h1
  obtain ⟨hm, hn, hl⟩ := GlobalTheory.T.lintegral_majorant_torus_lt_top σ h0 h1
  obtain ⟨C, N₀, hC⟩ := GlobalTheory.T.majorant_le_const_mul_torus σ h0 h1
  refine ⟨N₀, fun N hN => ?_⟩
  have i1 : Integrable (ga σ 4) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hn)]
    exact hl
  have i2 : Integrable (fun h => ga σ 4 (GlobalTheory.CompanionTheory.MajC.swp h)) := by
    refine ⟨(hm.comp measurable_swp).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun h => hn _),
      GlobalTheory.CompanionTheory.MajC.L_swp (fun h => ENNReal.ofReal (ga σ 4 h))]
    exact hl
  refine Integrable.mono' ((i1.add i2).const_mul |C|) (measurable_gx σ N).aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => ?_)
  rw [Real.norm_of_nonneg (gx_nonneg σ N h)]
  have g1 := hn h
  have g2 := hn (GlobalTheory.CompanionTheory.MajC.swp h)
  have hCa := abs_nonneg C
  have key : ∀ h : M22, ‖h 1 0‖ ≤ ‖h 0 0‖ → GlobalTheory.CompanionTheory.MajC.dt h ≠ 0 → gx σ N h ≤ |C| * ga σ 4 h :=
    fun h a b => (hC N hN h a b).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (hn h))
  show gx σ N h ≤ |C| * (ga σ 4 h + ga σ 4 (GlobalTheory.CompanionTheory.MajC.swp h))
  by_cases hd : GlobalTheory.CompanionTheory.MajC.dt h = 0
  · have : gx σ N h = 0 := by
      simp [gx, hd]
    rw [this]
    positivity
  by_cases hv : ‖h 1 0‖ ≤ ‖h 0 0‖
  · have := key h hv hd
    nlinarith
  · have hv' : ‖(GlobalTheory.CompanionTheory.MajC.swp h) 1 0‖ ≤ ‖(GlobalTheory.CompanionTheory.MajC.swp h) 0 0‖ := by
      have : ‖h 0 0‖ ≤ ‖h 1 0‖ := (not_le.1 hv).le
      simpa [GlobalTheory.CompanionTheory.MajC.swp] using this
    have := key _ hv' (by rw [GlobalTheory.CompanionTheory.MajC.dt_swp]; exact hd)
    rw [gx_swp] at this
    nlinarith

theorem norm_integrand (k : ℕ) (Ψ : Sw) (n : ℤ) (s : ℂ) (t : ℂˣ) (h : M22) :
    ‖chC n s t * ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ *
      (((‖(Matrix.of h).det‖⁻¹ : ℝ) : ℂ) * W2 k (innQ Ψ 1 h (t : ℂ)⁻¹) (Matrix.of h)⁻¹)‖ =
      ‖(t : ℂ)‖ ^ (2 * s.re - 2) * ((GlobalTheory.CompanionTheory.MajC.dt h)⁻¹ * ‖W2 k (innQ Ψ 1 h (t : ℂ)⁻¹) (Matrix.of h)⁻¹‖) := by
  have ht : 0 < ‖(t : ℂ)‖ := norm_pos_iff.2 t.ne_zero
  have e : ‖(t : ℂ)‖ ^ (2 * s.re - 2) = ‖(t : ℂ)‖ ^ (2 * s.re) * (‖(t : ℂ)‖ ^ 2)⁻¹ := by
    rw [Real.rpow_sub ht, div_eq_mul_inv, Real.rpow_two]
  rw [norm_mul, norm_mul, norm_mul, norm_chC', norm_inv, Complex.norm_real, Complex.norm_real, e]
  simp [GlobalTheory.CompanionTheory.MajC.dt]

theorem main : IbpQ → WhittakerSchwartzBound → UnipotentJointIntegrability := by
  intro hIbp hW k hk Ψ n s hs0 hs1 u
  obtain ⟨N₀, hG⟩ := hint s.re hs0 hs1
  set N := max N₀ 4 with hN
  have hGN := hG N (le_max_left _ _)
  obtain ⟨C₂, N₂, hC₂⟩ := hW k hk N
  set Nb := max N N₂ with hNb
  obtain ⟨C₁, N₁, hC₁⟩ := hIbp Nb
  have hN4 : 4 ≤ Nb := (le_max_right _ _).trans (le_max_left _ _)
  have hNb4 : 4 - 4 * s.re ≤ (Nb : ℝ) := by
    have : (4 : ℝ) ≤ Nb := by exact_mod_cast hN4
    linarith
  obtain ⟨K, hK⟩ := GlobalTheory.T.integral_unit_pow_decay_le s.re hs1 Nb hNb4
  set Ψ' : Sw := rtS (cyc u) Ψ with hΨ'
  have hrw : ∀ (h : M22) (β : ℂ), innQ Ψ (cyc u) h β = innQ Ψ' 1 h β := fun h β => innQ_rt _ _ _ _
  simp only [hrw]
  set A : ℝ := |C₂| * |C₁ * pS N₁ Ψ'| with hA
  have hA0 : 0 ≤ A := by positivity
  set X : M22 → ℝ := fun h => yb h ^ ((1 : ℝ) / 2) * (1 + |Real.log (yb h)|) / (1 + yb h) ^ N with hX
  have hy0 : ∀ h, 0 ≤ yb h := fun h => by unfold yb; positivity
  have hX0 : ∀ h, 0 ≤ X h := fun h => by
    have := hy0 h
    simp only [hX]
    positivity
  have hWb : ∀ (h : M22) (t : ℂˣ), (Matrix.of h).det ≠ 0 →
      ‖W2 k (innQ Ψ' 1 h (t : ℂ)⁻¹) (Matrix.of h)⁻¹‖ ≤
        A * ((GlobalTheory.CompanionTheory.MajC.dt h ^ 2)⁻¹ / ((1 + ‖h‖) ^ Nb * (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb)) * X h := by
    intro h t hd
    obtain ⟨f, hf, hfb⟩ := hC₁ Ψ' h (t : ℂ)⁻¹ hd
    have hM : ((Matrix.of h)⁻¹).det ≠ 0 := by
      rw [Matrix.det_nonsing_inv]
      simpa using hd
    have b := hC₂ f _ hM
    rw [Yb_inv h hd] at b
    rw [← hf]
    have hQ : 0 ≤ (GlobalTheory.CompanionTheory.MajC.dt h ^ 2)⁻¹ / ((1 + ‖h‖) ^ Nb * (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb) := by
      have : 0 ≤ GlobalTheory.CompanionTheory.MajC.dt h := norm_nonneg _
      positivity
    have hp : pS N₂ f ≤ |C₁ * pS N₁ Ψ'| *
        ((GlobalTheory.CompanionTheory.MajC.dt h ^ 2)⁻¹ / ((1 + ‖h‖) ^ Nb * (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb)) := by
      refine (pS_mono (le_max_right _ _) f).trans (hfb.trans ?_)
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hQ
    calc _ ≤ C₂ * pS N₂ f * yb h ^ ((1 : ℝ) / 2) * (1 + |Real.log (yb h)|) / (1 + yb h) ^ N := b
      _ = (C₂ * pS N₂ f) * X h := by simp only [hX]; ring
      _ ≤ (|C₂| * pS N₂ f) * X h := by
          refine mul_le_mul_of_nonneg_right ?_ (hX0 h)
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (pS_nonneg _ _)
      _ ≤ (|C₂| * (|C₁ * pS N₁ Ψ'| *
            ((GlobalTheory.CompanionTheory.MajC.dt h ^ 2)⁻¹ / ((1 + ‖h‖) ^ Nb * (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb)))) * X h := by
          refine mul_le_mul_of_nonneg_right ?_ (hX0 h)
          exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ = _ := by rw [hA]; ring
  set E : M22 → ℝ := fun h => A * (((GlobalTheory.CompanionTheory.MajC.dt h ^ 3)⁻¹ * X h) / (1 + ‖h‖) ^ N) with hE
  have hE0 : ∀ h, 0 ≤ E h := fun h => by
    have := hX0 h
    have h2 : 0 ≤ GlobalTheory.CompanionTheory.MajC.dt h := norm_nonneg _
    simp only [hE]
    positivity
  have hpt : ∀ (h : M22) (t : ℂˣ), (Matrix.of h).det ≠ 0 →
      ‖(t : ℂ)‖ ^ (2 * s.re - 2) * ((GlobalTheory.CompanionTheory.MajC.dt h)⁻¹ * ‖W2 k (innQ Ψ' 1 h (t : ℂ)⁻¹) (Matrix.of h)⁻¹‖) ≤
        E h * (‖(t : ℂ)‖ ^ (2 * s.re - 2) / (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb) := by
    intro h t hd
    have hD : 0 < GlobalTheory.CompanionTheory.MajC.dt h := norm_pos_iff.2 hd
    have hT : 0 ≤ ‖(t : ℂ)‖ ^ (2 * s.re - 2) := Real.rpow_nonneg (norm_nonneg _) _
    have hq : 0 < (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb := by positivity
    have hP : (1 + ‖h‖) ^ N ≤ (1 + ‖h‖) ^ Nb :=
      pow_le_pow_right₀ (by linarith [norm_nonneg h]) (le_max_left _ _)
    have hP0 : 0 < (1 + ‖h‖) ^ N := by positivity
    have h1 := hWb h t hd
    have h2 : A * ((GlobalTheory.CompanionTheory.MajC.dt h ^ 2)⁻¹ / ((1 + ‖h‖) ^ Nb * (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb)) * X h ≤
        A * ((GlobalTheory.CompanionTheory.MajC.dt h ^ 2)⁻¹ / ((1 + ‖h‖) ^ N * (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb)) * X h := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hA0) (hX0 h)
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right hP hq.le)
    calc _ ≤ ‖(t : ℂ)‖ ^ (2 * s.re - 2) * ((GlobalTheory.CompanionTheory.MajC.dt h)⁻¹ *
          (A * ((GlobalTheory.CompanionTheory.MajC.dt h ^ 2)⁻¹ / ((1 + ‖h‖) ^ N * (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb)) * X h)) := by
          refine mul_le_mul_of_nonneg_left ?_ hT
          exact mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = _ := by
          simp only [hE]
          field_simp
  have hmeas : Measurable (fun p : ℂˣ × M22 => chC n s p.1 * ((‖(p.1 : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ *
      (((‖(Matrix.of p.2).det‖⁻¹ : ℝ) : ℂ) * W2 k (innQ Ψ' 1 p.2 (p.1 : ℂ)⁻¹) (Matrix.of p.2)⁻¹)) := by
    have hv : Measurable (fun p : ℂˣ × M22 => ((p.1 : ℂˣ) : ℂ)) :=
      GlobalTheory.CompanionTheory.TateC.val_measurableEmbedding.measurable.comp measurable_fst
    have hdet : Measurable (fun p : ℂˣ × M22 => (Matrix.of p.2).det) := by
      simp only [Matrix.det_fin_two, Matrix.of_apply]
      fun_prop
    refine (((measurable_chC' n s).comp measurable_fst).mul ?_).mul (Measurable.mul ?_ (GlobalTheory.T.measurable_whittaker_inner_quotient_inv k Ψ'))
    · exact (Complex.measurable_ofReal.comp (hv.norm.pow_const 2)).inv
    · exact Complex.measurable_ofReal.comp hdet.norm.inv
  have hnorm := fun (t : ℂˣ) (h : M22) => norm_integrand k Ψ' n s t h
  have hz : ∀ h : M22, (Matrix.of h).det = 0 → ∀ t : ℂˣ,
      chC n s t * ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ *
      (((‖(Matrix.of h).det‖⁻¹ : ℝ) : ℂ) * W2 k (innQ Ψ' 1 h (t : ℂ)⁻¹) (Matrix.of h)⁻¹) = 0 := by
    intro h hd t
    simp [hd]
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun h => ?_, ?_⟩
  · by_cases hd : (Matrix.of h).det = 0
    · simp only [hz h hd]
      exact integrable_zero _ _ _
    · have hq : 0 < ‖eta h‖ := by
        rw [norm_eta h hd]
        exact div_pos (GlobalTheory.CompanionTheory.MajC.L_eta h hd).1 (norm_pos_iff.2 hd)
      refine Integrable.mono' (((hK _ hq).1).const_mul (E h)) ?_ ?_
      · exact (hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun t => by
          have := hpt h t hd
          rw [← hnorm t h] at this
          exact this
  · refine Integrable.mono' (hGN.const_mul (A * |K|)) ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_left' (μ := mulC)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun h => ?_
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      by_cases hd : (Matrix.of h).det = 0
      · simp only [hz h hd, norm_zero, integral_zero]
        exact mul_nonneg (by positivity) (gx_nonneg _ _ _)
      · have hD : 0 < GlobalTheory.CompanionTheory.MajC.dt h := norm_pos_iff.2 hd
        have hq : 0 < ‖eta h‖ := by
          rw [norm_eta h hd]
          exact div_pos (GlobalTheory.CompanionTheory.MajC.L_eta h hd).1 hD
        obtain ⟨i1, i2⟩ := hK _ hq
        have hqp : 0 ≤ ‖eta h‖ ^ (2 * s.re - 2) := Real.rpow_nonneg hq.le _
        calc ∫ t : ℂˣ, ‖_‖ ∂mulC ≤ ∫ t : ℂˣ, E h *
              (‖(t : ℂ)‖ ^ (2 * s.re - 2) / (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb) ∂mulC := by
              refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
                (i1.const_mul _) (Filter.Eventually.of_forall fun t => ?_)
              have := hpt h t hd
              rw [← hnorm t h] at this
              exact this
          _ = E h * ∫ t : ℂˣ, ‖(t : ℂ)‖ ^ (2 * s.re - 2) / (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb ∂mulC :=
              integral_const_mul _ _
          _ ≤ E h * (K * ‖eta h‖ ^ (2 * s.re - 2)) := mul_le_mul_of_nonneg_left i2 (hE0 h)
          _ ≤ E h * (|K| * ‖eta h‖ ^ (2 * s.re - 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hqp) (hE0 h)
          _ = _ := by
              simp only [hE, hX, gx]
              rw [norm_eta h hd]
              ring

end GlobalTheory.CompanionTheory.PerUC
end
end
