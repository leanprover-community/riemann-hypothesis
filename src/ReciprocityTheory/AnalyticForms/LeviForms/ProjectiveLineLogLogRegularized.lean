import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax

section
namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

def fsGk (k : Fin 2) : ℝ → ℝ := if k = 0 then fubiniStudyProfile else fubiniStudyProfileInv

theorem finset_fin_two_eq_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp

@[simp] theorem fsGk_zero : fsGk 0 = fubiniStudyProfile := by
  simp [fsGk]
@[simp] theorem fsGk_one : fsGk 1 = fubiniStudyProfileInv := by
  simp [fsGk]

theorem fubiniStudy_first_term_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ fubiniStudyProfile q := by
  exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))

theorem fubiniStudy_second_term_nonneg {q : ℝ} (hq : 0 < q) : 0 ≤ fubiniStudyProfileInv q := by
  have h := inv_pos.mpr hq
  exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))

theorem fsGk_nonneg (k : Fin 2) {q : ℝ} (hq : 0 ≤ q) (hk : k = 1 → 0 < q) : 0 ≤ fsGk k q := by
  rcases finset_fin_two_eq_cases k with rfl | rfl
  · rw [fsGk_zero]
    exact fubiniStudy_first_term_nonneg hq
  · rw [fsGk_one]
    exact fubiniStudy_second_term_nonneg (hk rfl)

theorem fsGk_data (k : Fin 2) {q : ℝ} (hq : 0 ≤ q) (hk : k = 1 → 0 < q) :
    ∃ (G' : ℝ → ℝ) (G'' : ℝ), (∀ᶠ t in 𝓝 q, HasDerivAt (fsGk k) (G' t) t) ∧
      HasDerivAt G' G'' q ∧ q * G'' + G' q = 1 / (2 * (1 + q) ^ 2) := by
  rcases finset_fin_two_eq_cases k with rfl | rfl
  · rw [fsGk_zero]
    have h1 : (1 : ℝ) + q ≠ 0 := by linarith
    refine ⟨fun t => (1 / 2) * (1 + t)⁻¹, (1 / 2) * (-1 / (1 + q) ^ 2), ?_, ?_, ?_⟩
    · exact (eventually_gt_nhds (by linarith : (-1 : ℝ) < q)).mono fun t ht => hasDerivAt_fubiniStudyProfile ht
    · exact (((hasDerivAt_id' q).const_add 1).inv h1).const_mul (1 / 2)
    · field_simp
      ring
  · rw [fsGk_one]
    have hq1 := hk rfl
    have h1 : q * (q + 1) ≠ 0 := by positivity
    refine ⟨fun t => -(1 / 2) * (t * (t + 1))⁻¹,
      -(1 / 2) * (-(1 * (q + 1) + q * 1) / (q * (q + 1)) ^ 2), ?_, ?_, ?_⟩
    · exact (eventually_gt_nhds hq1).mono fun t ht => hasDerivAt_fubiniStudyProfileInv ht
    · exact (((hasDerivAt_id' q).mul ((hasDerivAt_id' q).add_const 1)).inv h1).const_mul (-(1 / 2))
    · have h2 : q + 1 ≠ 0 := by positivity
      have h3 : q ≠ 0 := hq1.ne'
      field_simp
      ring

theorem combo_alg {a q r κ Gk1 Gk2 Gj1 Gj2 : ℝ} (hr : 2 < r) (ha : 1 ≤ a) (hq : 0 ≤ q)
    (hκ : 0 ≤ κ) (hk : q * Gk2 + Gk1 = κ) (hj : q * Gj2 + Gj1 = κ) :
    0 ≤ (a * Gk2 - (2 * Gj2 * r - 2 * Gj1 * (2 * Gj1)) / r ^ 2) * q + (a * Gk1 - 2 * Gj1 / r) := by
  have hr0 : 0 < r := by linarith
  have hr0' : r ≠ 0 := hr0.ne'
  have e : (a * Gk2 - (2 * Gj2 * r - 2 * Gj1 * (2 * Gj1)) / r ^ 2) * q + (a * Gk1 - 2 * Gj1 / r)
      = a * (q * Gk2 + Gk1) - 2 / r * (q * Gj2 + Gj1) + 4 * q * Gj1 ^ 2 / r ^ 2 := by
    field_simp
    ring
  rw [e, hk, hj]
  have h1 : 2 / r ≤ 1 := by
    rw [div_le_one hr0]
    linarith
  have h2 : 0 ≤ 4 * q * Gj1 ^ 2 / r ^ 2 := by positivity
  have h3 : 2 / r * κ ≤ a * κ := mul_le_mul_of_nonneg_right (le_trans h1 ha) hκ
  linarith

theorem two_lt_exp_one : (2 : ℝ) < Real.exp 1 := by
  have h := Real.exp_one_gt_d9
  linarith

theorem levi_combo_nonneg {F : (Fin 1 → ℂ) → ℝ} {y : Fin 1 → ℂ} {a b : ℝ} (ha : 1 ≤ a)
    (k j : Fin 2) (hk : k = 1 → y 0 ≠ 0) (hj : j = 1 → y 0 ≠ 0)
    (hF : ∀ᶠ w in 𝓝 y, F w = a * fsGk k (fsQ w) + b - Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)))
    (v : Fin 1 → ℂ) : 0 ≤ levi F y v := by
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = ‖y 0‖ ^ 2 := ⟨_, rfl⟩
  have hq : 0 ≤ q := by
    rw [hq_def]
    positivity
  have hkq : k = 1 → 0 < q := fun h => by
    rw [hq_def]
    exact pow_pos (norm_pos_iff.mpr (hk h)) 2
  have hjq : j = 1 → 0 < q := fun h => by
    rw [hq_def]
    exact pow_pos (norm_pos_iff.mpr (hj h)) 2
  obtain ⟨Gk', Gk'', hkd, hkd2, hkid⟩ := fsGk_data k hq hkq
  obtain ⟨Gj', Gj'', hjd, hjd2, hjid⟩ := fsGk_data j hq hjq
  have hR : 2 < Real.exp 1 + 2 * fsGk j q := by
    have h1 := fsGk_nonneg j hq hjq
    have h2 := two_lt_exp_one
    linarith
  have hR0 : (0 : ℝ) < Real.exp 1 + 2 * fsGk j q := by linarith
  have hdj : HasDerivAt (fun t => Real.exp 1 + 2 * fsGk j t) (2 * Gj' q) q :=
    (hjd.self_of_nhds.const_mul 2).const_add _
  have hpos_ev : ∀ᶠ t in 𝓝 q, 0 < Real.exp 1 + 2 * fsGk j t :=
    hdj.continuousAt.eventually (lt_mem_nhds hR0)
  have hG : ∀ᶠ t in 𝓝 q,
      HasDerivAt (fun t => a * fsGk k t + b - Real.log (Real.exp 1 + 2 * fsGk j t))
        (a * Gk' t - 2 * Gj' t / (Real.exp 1 + 2 * fsGk j t)) t := by
    filter_upwards [hkd, hjd, hpos_ev] with t h1 h2 h3
    exact ((h1.const_mul a).add_const b).sub (((h2.const_mul 2).const_add _).log h3.ne')
  have hG2 : HasDerivAt (fun t => a * Gk' t - 2 * Gj' t / (Real.exp 1 + 2 * fsGk j t))
      (a * Gk'' - (2 * Gj'' * (Real.exp 1 + 2 * fsGk j q) - 2 * Gj' q * (2 * Gj' q)) /
        (Real.exp 1 + 2 * fsGk j q) ^ 2) q :=
    (hkd2.const_mul a).sub ((hjd2.const_mul 2).div hdj hR0.ne')
  have hκ : (0 : ℝ) ≤ 1 / (2 * (1 + q) ^ 2) := by positivity
  have hnn := combo_alg hR ha hq hκ hkid hjid
  subst hq_def
  exact projLine_leviForm_radial_nonneg (hF.mono fun w hw => by rw [hw]; rfl) hG hG2 hnn v

theorem levi_simple_nonneg {F : (Fin 1 → ℂ) → ℝ} {y : Fin 1 → ℂ} {a b : ℝ} (ha : 0 ≤ a)
    (k : Fin 2) (hk : k = 1 → y 0 ≠ 0) (hF : ∀ᶠ w in 𝓝 y, F w = a * fsGk k (fsQ w) + b)
    (v : Fin 1 → ℂ) : 0 ≤ levi F y v := by
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = ‖y 0‖ ^ 2 := ⟨_, rfl⟩
  have hq : 0 ≤ q := by
    rw [hq_def]
    positivity
  have hkq : k = 1 → 0 < q := fun h => by
    rw [hq_def]
    exact pow_pos (norm_pos_iff.mpr (hk h)) 2
  obtain ⟨Gk', Gk'', hkd, hkd2, hkid⟩ := fsGk_data k hq hkq
  have hG : ∀ᶠ t in 𝓝 q, HasDerivAt (fun t => a * fsGk k t + b) (a * Gk' t) t :=
    hkd.mono fun t h1 => (h1.const_mul a).add_const b
  have hG2 : HasDerivAt (fun t => a * Gk' t) (a * Gk'') q := hkd2.const_mul a
  have hnn : 0 ≤ a * Gk'' * q + a * Gk' q := by
    have e : a * Gk'' * q + a * Gk' q = a * (q * Gk'' + Gk' q) := by ring
    rw [e, hkid]
    exact mul_nonneg ha (by positivity)
  subst hq_def
  exact projLine_leviForm_radial_nonneg (hF.mono fun w hw => by rw [hw]; rfl) hG hG2 hnn v

theorem contDiffOn_fsGk (k : Fin 2) :
    ContDiffOn ℝ ∞ (fun w => fsGk k (fsQ w)) {w : Fin 1 → ℂ | k = 1 → w 0 ≠ 0} := by
  rcases finset_fin_two_eq_cases k with rfl | rfl
  · simp only [fsGk_zero]
    exact contDiff_fubiniStudyProfile_normSqFirst.contDiffOn
  · simp only [fsGk_one]
    exact contDiffOn_fubiniStudyProfileInv_normSqFirst.mono fun w hw => by simpa using hw

theorem isOpen_goodSet (k : Fin 2) : IsOpen {w : Fin 1 → ℂ | k = 1 → w 0 ≠ 0} := by
  rcases finset_fin_two_eq_cases k with rfl | rfl
  · have e : {w : Fin 1 → ℂ | (0 : Fin 2) = 1 → w 0 ≠ 0} = Set.univ := by
      ext w
      simp
    rw [e]
    exact isOpen_univ
  · have e : {w : Fin 1 → ℂ | (1 : Fin 2) = 1 → w 0 ≠ 0} = {w | w 0 ≠ 0} := by
      ext w
      simp
    rw [e]
    exact isOpen_ne_fun (continuous_apply 0) continuous_const

theorem fsGk_fsQ_nonneg (k : Fin 2) {w : Fin 1 → ℂ} (hw : k = 1 → w 0 ≠ 0) :
    0 ≤ fsGk k (fsQ w) := by
  exact fsGk_nonneg k (by unfold fsQ; positivity)
    (fun h => by unfold fsQ; exact pow_pos (norm_pos_iff.mpr (hw h)) 2)

theorem projectiveLine_section_self_infty : projectiveLinePairSection (OnePoint.infty : OnePoint ℂ) (OnePoint.infty : OnePoint ℂ) = 0 := by
  rw [projLineSection_infty, infiniteCoord_infty]

theorem projectiveLine_section_self_coe (z : ℂ) : projectiveLinePairSection (z : OnePoint ℂ) z = 1 := by
  rw [projLineSection_coe]

theorem mem_boundary_projectiveLine (y : OnePoint ℂ) : y ∈ bdry projectiveLinePairSection ↔ y = (OnePoint.infty : OnePoint ℂ) := by
  induction y using OnePoint.rec with
  | infty => simp [bdry, projectiveLine_section_self_infty]
  | coe z => simp [bdry, projectiveLine_section_self_coe]

theorem logNormSec_coe (z : ℂ) : logNormSec fsPot projectiveLinePairSection z = -fubiniStudyProfile (‖z‖ ^ 2) := by
  simp only [logNormSec, projectiveLine_section_self_coe, fsPot_φ_coe, finiteCoord_coe, norm_one, one_mul, Real.log_exp,
    fubiniStudyProfile]

theorem logNormSec_infty : logNormSec fsPot projectiveLinePairSection (OnePoint.infty : OnePoint ℂ) = 0 := by
  simp [logNormSec, projectiveLine_section_self_infty]

theorem rW_coe (z : ℂ) : rW fsPot projectiveLinePairSection z = Real.exp 1 + 2 * fubiniStudyProfile (‖z‖ ^ 2) := by
  simp only [rW, logNormSec_coe]
  ring

theorem rW_infty : rW fsPot projectiveLinePairSection (OnePoint.infty : OnePoint ℂ) = Real.exp 1 := by
  simp [rW, logNormSec_infty]

theorem projectiveLine_weight_ge_exp_one (y : OnePoint ℂ) : Real.exp 1 ≤ rW fsPot projectiveLinePairSection y := by
  induction y using OnePoint.rec with
  | infty => rw [rW_infty]
  | coe z =>
    rw [rW_coe]
    have h := fubiniStudy_first_term_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 2)
    linarith

theorem rW_pos (y : OnePoint ℂ) : 0 < rW fsPot projectiveLinePairSection y := by
  exact lt_of_lt_of_le (Real.exp_pos 1) (projectiveLine_weight_ge_exp_one y)

theorem logNormSec_nonpos (y : OnePoint ℂ) : logNormSec fsPot projectiveLinePairSection y ≤ 0 := by
  induction y using OnePoint.rec with
  | infty => rw [logNormSec_infty]
  | coe z =>
    rw [logNormSec_coe]
    have h := fubiniStudy_first_term_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 2)
    linarith

theorem one_le_log_rW (y : OnePoint ℂ) : 1 ≤ Real.log (rW fsPot projectiveLinePairSection y) := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (rW fsPot projectiveLinePairSection y) := Real.log_le_log (Real.exp_pos 1) (projectiveLine_weight_ge_exp_one y)

theorem ne_infty_iff_mem_range (x : OnePoint ℂ) :
    x ≠ (OnePoint.infty : OnePoint ℂ) ↔ x ∈ Set.range ((↑) : ℂ → OnePoint ℂ) := by
  rw [Set.mem_range]
  exact OnePoint.ne_infty_iff_exists

theorem chart_symm_ne_infty (j : Fin 2) (w : Fin 1 → ℂ) :
    (p1.chart j).symm w ≠ (OnePoint.infty : OnePoint ℂ) ↔ (j = 1 → w 0 ≠ 0) := by
  rcases finset_fin_two_eq_cases j with rfl | rfl
  · rw [projLineAtlas_chart0, projLineChart0_symm_apply]
    simp
  · rw [projLineAtlas_chart1, ne_infty_iff_mem_range, projLineChart1_symm_mem_range]
    simp

theorem projectiveLine_second_chart_symm_of_ne {w : Fin 1 → ℂ} (h : w 0 ≠ 0) :
    projectiveLineChartAtInfinity.symm w = (((w 0)⁻¹ : ℂ) : OnePoint ℂ) := by
  obtain ⟨z, hz⟩ := projLineChart1_symm_mem_range.mpr h
  have h1 := infiniteCoord_projLineChart1_symm w
  rw [← hz, infiniteCoord_coe] at h1
  rw [← hz, ← h1, inv_inv]

theorem projectiveLine_second_chart_symm_of_eq {w : Fin 1 → ℂ} (h : w 0 = 0) : projectiveLineChartAtInfinity.symm w = (OnePoint.infty : OnePoint ℂ) := by
  by_contra hne
  exact (projLineChart1_symm_mem_range.mp ((ne_infty_iff_mem_range _).mp hne)) h

def llw (y : OnePoint ℂ) : ℝ := -Real.log (rW fsPot projectiveLinePairSection y)

theorem projectiveLineLogLog_coe (z : ℂ) :
    llw z = -Real.log (Real.exp 1 + 2 * fubiniStudyProfile (‖z‖ ^ 2)) := by
  unfold llw
  rw [rW_coe]

theorem projectiveLineLogLog_chart (j : Fin 2) (w : Fin 1 → ℂ) (hw : j = 1 → w 0 ≠ 0) :
    llw ((p1.chart j).symm w) = -Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)) := by
  rcases finset_fin_two_eq_cases j with rfl | rfl
  · rw [projLineAtlas_chart0, projLineChart0_symm_apply, projectiveLineLogLog_coe, fsGk_zero]
    rfl
  · rw [projLineAtlas_chart1, projectiveLine_second_chart_symm_of_ne (hw rfl), projectiveLineLogLog_coe, fsGk_one]
    simp only [fubiniStudyProfile, fubiniStudyProfileInv, fsQ, norm_inv, inv_pow]

theorem projectiveLineLogLog_le_neg_one (y : OnePoint ℂ) : llw y ≤ -1 := by
  unfold llw
  have h := one_le_log_rW y
  linarith

theorem ell_ge {t B : ℝ} (ht : 0 < t) (htB : t ≤ Real.exp (-B)) : B ≤ Real.log (1 / t) := by
  rw [one_div, Real.log_inv]
  have h := Real.log_le_log ht htB
  rw [Real.log_exp] at h
  linarith

theorem one_le_exp_one : (1 : ℝ) ≤ Real.exp 1 := by
  have h := Real.add_one_le_exp 1
  linarith

theorem ell_big {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    Real.exp (Real.exp 1) ≤ Real.log (1 / t) := by
  exact ell_ge ht ht0

theorem ell_ge_e {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    Real.exp 1 ≤ Real.log (1 / t) := by
  exact le_trans (Real.exp_le_exp.mpr one_le_exp_one) (ell_big ht ht0)

theorem ell_pos {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    0 < Real.log (1 / t) := by
  exact lt_of_lt_of_le (Real.exp_pos 1) (ell_ge_e ht ht0)

theorem logell_big {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    Real.exp 1 ≤ Real.log (Real.log (1 / t)) := by
  calc Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := (Real.log_exp _).symm
    _ ≤ Real.log (Real.log (1 / t)) := Real.log_le_log (Real.exp_pos _) (ell_big ht ht0)

theorem logell_pos {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    0 < Real.log (Real.log (1 / t)) := by
  exact lt_of_lt_of_le (Real.exp_pos 1) (logell_big ht ht0)

theorem eps_pos {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    0 < epsT 1 t := by
  unfold epsT
  exact div_pos (mul_pos one_pos (logell_pos ht ht0)) (ell_pos ht ht0)

theorem eps_le_one {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    epsT 1 t ≤ 1 := by
  unfold epsT
  rw [div_le_one (ell_pos ht ht0), one_mul]
  have h := Real.log_le_sub_one_of_pos (ell_pos ht ht0)
  linarith

theorem epsT_two (t : ℝ) : epsT 2 t = 2 * epsT 1 t := by
  unfold epsT
  ring

theorem ell_anti {t t' : ℝ} (ht : 0 < t) (htt' : t ≤ t') : Real.log (1 / t') ≤ Real.log (1 / t) := by
  exact Real.log_le_log (one_div_pos.mpr (lt_of_lt_of_le ht htt')) (one_div_le_one_div_of_le ht htt')

theorem eps_mono {t t' : ℝ} (ht : 0 < t) (htt' : t ≤ t')
    (ht0 : t' ≤ Real.exp (-Real.exp (Real.exp 1))) : epsT 1 t ≤ epsT 1 t' := by
  have ht' : 0 < t' := lt_of_lt_of_le ht htt'
  have h1 : Real.exp 1 ≤ Real.log (1 / t') := ell_ge_e ht' ht0
  have h2 : Real.exp 1 ≤ Real.log (1 / t) := ell_ge_e ht (le_trans htt' ht0)
  have h3 : Real.log (1 / t') ≤ Real.log (1 / t) := ell_anti ht htt'
  unfold epsT
  simp only [one_mul]
  exact Real.log_div_self_antitoneOn h1 h2 h3

end

end ReciprocityTheory.AnForm.P
end

section
namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

def llT (t : ℝ) (y : OnePoint ℂ) : ℝ :=
  if projectiveLinePairSection y y = 0 then -Real.log (Real.log (1 / t)) else
    ReciprocityTheory.AnForm.A.regMax (epsT 1 t) ![llw y, -Real.log (Real.log (1 / t))]

abbrev T0 : ℝ := Real.exp (-Real.exp (Real.exp 1))

theorem two_le_inf : (2 : WithTop ℕ∞) ≤ ∞ := by norm_cast

section RM

open ReciprocityTheory.AnForm.A

theorem rm_ge_left (η a b : ℝ) : a ≤ regMax η ![a, b] :=
  le_trans (by simpa using le_tmax ![a, b] 0) (regMax_ge η _)

theorem rm_ge_right (η a b : ℝ) : b ≤ regMax η ![a, b] :=
  le_trans (by simpa using le_tmax ![a, b] 1) (regMax_ge η _)

theorem rm_le {η a b m : ℝ} (hη : 0 ≤ η) (ha : a ≤ m) (hb : b ≤ m) :
    regMax η ![a, b] ≤ m + η / 2 := by
  have : tmax ![a, b] ≤ m := tmax_le (fun i => by rcases finset_fin_two_eq_cases i with rfl | rfl <;> simpa)
  linarith [regMax_le hη ![a, b]]

theorem rm_eq_left {η a b : ℝ} (hη : 0 ≤ η) (h : b + η ≤ a) : regMax η ![a, b] = a := by
  have := regMax_eq_of_dom hη ![a, b] 0 (fun j hj => by
    rcases finset_fin_two_eq_cases j with rfl | rfl
    · exact absurd rfl hj
    · simpa using h)
  simpa using this

theorem rm_eq_right {η a b : ℝ} (hη : 0 ≤ η) (h : a + η ≤ b) : regMax η ![a, b] = b := by
  have := regMax_eq_of_dom hη ![a, b] 1 (fun j hj => by
    rcases finset_fin_two_eq_cases j with rfl | rfl
    · simpa using h
    · exact absurd rfl hj)
  simpa using this

end RM

theorem llT_infty (t : ℝ) : llT t OnePoint.infty = -Real.log (Real.log (1 / t)) := by
  simp [llT, projectiveLine_section_self_infty]

theorem llT_ne (t : ℝ) {y : OnePoint ℂ} (hy : y ≠ OnePoint.infty) :
    llT t y = ReciprocityTheory.AnForm.A.regMax (epsT 1 t) ![llw y, -Real.log (Real.log (1 / t))] := by
  rw [llT, if_neg (show ¬ (projectiveLinePairSection y y = 0) from fun h => hy ((mem_boundary_projectiveLine y).1 h))]

theorem projLine_chart_target (j : Fin 2) : (p1.chart j).target = Set.univ := by
  rcases finset_fin_two_eq_cases j with rfl | rfl
  · rw [projLineAtlas_chart0]; exact projLineChart0_target
  · rw [projLineAtlas_chart1]; exact projLineChart1_target

theorem fsPot_chart' (x : OnePoint ℂ) (j : Fin 2) : ∃ k : Fin 2,
    (∀ w, fsPot.φ x ((p1.chart j).symm w) = fsGk k (fsQ w)) ∧
    ∀ w ∈ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x, k = 1 → w 0 ≠ 0 := by
  rcases fsPot_chart x j with h | ⟨h, hs⟩
  · exact ⟨0, fun w => by rw [fsGk_zero]; exact congrFun h w, fun w _ h1 => absurd h1 (by decide)⟩
  · exact ⟨1, fun w => by rw [fsGk_one]; exact congrFun h w, fun w hw _ => hs w hw⟩

theorem chartV_iff (j : Fin 2) (w : Fin 1 → ℂ) :
    w ∈ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' (bdry projectiveLinePairSection)ᶜ ↔ (j = 1 → w 0 ≠ 0) := by
  rw [← chart_symm_ne_infty j w, projLine_chart_target j]
  simp [mem_boundary_projectiveLine]

theorem llT_chart_eq (t : ℝ) (j : Fin 2) (w : Fin 1 → ℂ) (hw : j = 1 → w 0 ≠ 0) :
    llT t ((p1.chart j).symm w) = ReciprocityTheory.AnForm.A.regMax (epsT 1 t)
      ![-Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)), -Real.log (Real.log (1 / t))] := by
  rw [llT_ne t ((chart_symm_ne_infty j w).2 hw), projectiveLineLogLog_chart j w hw]

theorem contDiffOn_llwChart (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun w => -Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)))
      {w : Fin 1 → ℂ | j = 1 → w 0 ≠ 0} :=
  ((contDiffOn_const.add (contDiffOn_const.mul (contDiffOn_fsGk j))).log (fun w hw =>
    ne_of_gt (by have := fsGk_fsQ_nonneg j hw; have := Real.exp_pos 1; linarith))).neg

theorem contDiffOn_llTChart (t : ℝ) (ht : 0 < t) (ht0 : t ≤ T0) (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun w => ReciprocityTheory.AnForm.A.regMax (epsT 1 t)
      ![-Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)), -Real.log (Real.log (1 / t))])
      {w : Fin 1 → ℂ | j = 1 → w 0 ≠ 0} := by
  refine (ReciprocityTheory.AnForm.A.regMax_contDiff (ι := Fin 2) (eps_pos ht ht0)).comp_contDiffOn ?_
  refine contDiffOn_pi.2 fun i => ?_
  rcases finset_fin_two_eq_cases i with rfl | rfl
  · exact (contDiffOn_llwChart j).congr (fun w _ => by simp)
  · exact (contDiffOn_const (c := -Real.log (Real.log (1 / t)))).congr (fun w _ => by simp)

theorem llT_near_pole (t : ℝ) (ht : 0 < t) (ht0 : t ≤ T0) : ∃ δ > 0, ∀ w : Fin 1 → ℂ,
    fsQ w < δ → llT t (projectiveLineChartAtInfinity.symm w) = -Real.log (Real.log (1 / t)) := by
  have hℓ := ell_pos ht ht0
  have hM : 0 < Real.log (1 / t) * Real.exp (epsT 1 t) := mul_pos hℓ (Real.exp_pos _)
  refine ⟨Real.exp (-(Real.log (1 / t) * Real.exp (epsT 1 t))), Real.exp_pos _, fun w hw => ?_⟩
  by_cases h0 : w 0 = 0
  · rw [projectiveLine_second_chart_symm_of_eq h0, llT_infty]
  · have e1 := llT_chart_eq t 1 w (fun _ => h0)
    rw [projLineAtlas_chart1] at e1
    rw [e1]
    apply rm_eq_right (eps_pos ht ht0).le
    have hq : 0 < fsQ w := by unfold fsQ; have := norm_pos_iff.2 h0; positivity
    have hinv : Real.exp (Real.log (1 / t) * Real.exp (epsT 1 t)) < (fsQ w)⁻¹ :=
      (lt_inv_comm₀ (Real.exp_pos _) hq).2 (by rwa [← Real.exp_neg])
    have h2 : 2 * fsGk 1 (fsQ w) = Real.log (1 + (fsQ w)⁻¹) := by rw [fsGk_one, fubiniStudyProfileInv]; ring
    have h3 : Real.log (1 / t) * Real.exp (epsT 1 t) < Real.log (1 + (fsQ w)⁻¹) := by
      have := Real.log_lt_log (Real.exp_pos _)
        (show Real.exp (Real.log (1 / t) * Real.exp (epsT 1 t)) < 1 + (fsQ w)⁻¹ by linarith)
      rwa [Real.log_exp] at this
    have h4 : Real.log (Real.log (1 / t) * Real.exp (epsT 1 t)) ≤
        Real.log (Real.exp 1 + 2 * fsGk 1 (fsQ w)) :=
      Real.log_le_log hM (by rw [h2]; linarith [Real.exp_pos 1])
    have h5 : Real.log (Real.log (1 / t) * Real.exp (epsT 1 t)) = Real.log (Real.log (1 / t)) + epsT 1 t := by
      rw [Real.log_mul hℓ.ne' (Real.exp_pos _).ne', Real.log_exp]
    linarith

theorem llT_smooth_chart (t : ℝ) (ht : 0 < t) (ht0 : t ≤ T0) (j : Fin 2) :
    ContDiffOn ℝ ∞ (llT t ∘ (p1.chart j).symm) ((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' Set.univ) := by
  obtain ⟨δ, hδ, hpole⟩ := llT_near_pole t ht ht0
  intro w _
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases hw : j = 1 → w 0 ≠ 0
  · have hmem : {w : Fin 1 → ℂ | j = 1 → w 0 ≠ 0} ∈ 𝓝 w := (isOpen_goodSet j).mem_nhds hw
    refine ((contDiffOn_llTChart t ht ht0 j).contDiffAt hmem).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with w' hw'
    exact llT_chart_eq t j w' hw'
  · push Not at hw
    obtain ⟨rfl, hw0⟩ := hw
    have hmem : {w : Fin 1 → ℂ | fsQ w < δ} ∈ 𝓝 w :=
      (isOpen_lt contDiff_fsQ.continuous continuous_const).mem_nhds (by simp [fsQ, hw0, hδ])
    refine (contDiffAt_const (c := -Real.log (Real.log (1 / t)))).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with w' hw'
    show llT t ((p1.chart (1 : Fin 2)).symm w') = _
    rw [projLineAtlas_chart1]
    exact hpole w' hw'

theorem llT_smooth (t : ℝ) (ht : 0 < t) (ht0 : t ≤ T0) : p1.Smooth (llT t) :=
  fun j => llT_smooth_chart t ht ht0 j

theorem llT_psh_chart (t : ℝ) (ht : 0 < t) (ht0 : t ≤ T0) (x : OnePoint ℂ) (j : Fin 2)
    (y : Fin 1 → ℂ) (hy : y ∈ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x)
    (v : Fin 1 → ℂ) :
    0 ≤ levi (fun w => fsPot.φ x ((p1.chart j).symm w) + llT t ((p1.chart j).symm w) +
      epsT 2 t * fsPot.φ x ((p1.chart j).symm w)) y v := by
  obtain ⟨k, hφw, hk⟩ := fsPot_chart' x j
  have hDo : IsOpen ((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x) :=
    (p1.chart j).isOpen_inter_preimage_symm (fsPot.isOpen_U x)
  have hη := eps_pos ht ht0
  have ha : 1 ≤ 1 + epsT 2 t := by rw [epsT_two]; linarith
  have hyk : k = 1 → y 0 ≠ 0 := hk y hy
  by_cases hyj : j = 1 → y 0 ≠ 0
  · have hNo : IsOpen (((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x) ∩
        {w : Fin 1 → ℂ | j = 1 → w 0 ≠ 0}) := hDo.inter (isOpen_goodSet j)
    have hyN : y ∈ ((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x) ∩
        {w : Fin 1 → ℂ | j = 1 → w 0 ≠ 0} := ⟨hy, hyj⟩
    have hEq : (fun w => fsPot.φ x ((p1.chart j).symm w) + llT t ((p1.chart j).symm w) +
        epsT 2 t * fsPot.φ x ((p1.chart j).symm w)) =ᶠ[𝓝 y]
        fun w => ReciprocityTheory.AnForm.A.regMax (epsT 1 t) (fun i =>
          ![-Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)), -Real.log (Real.log (1 / t))] i +
            (1 + epsT 2 t) * fsGk k (fsQ w)) := by
      filter_upwards [hNo.mem_nhds hyN] with w hw
      rw [hφw, llT_chart_eq t j w hw.2, ReciprocityTheory.AnForm.A.regMax_add_const]
      ring
    rw [levi_congr hEq]
    refine ReciprocityTheory.AnForm.A.regMaxLevi_thm 1 (Fin 2) (epsT 1 t) _
      (fun i w => ![-Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)), -Real.log (Real.log (1 / t))] i +
        (1 + epsT 2 t) * fsGk k (fsQ w)) hNo hη ?_ y hyN v 0 ?_
    · intro i
      have hG : ContDiffOn ℝ ∞ (fun w => fsGk k (fsQ w))
          (((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x) ∩
            {w : Fin 1 → ℂ | j = 1 → w 0 ≠ 0}) :=
        (contDiffOn_fsGk k).mono (fun w hw => hk w hw.1)
      rcases finset_fin_two_eq_cases i with rfl | rfl
      · exact ((((contDiffOn_llwChart j).mono (fun w hw => hw.2)).add
          ((contDiffOn_const (c := 1 + epsT 2 t)).mul hG)).of_le two_le_inf).congr (fun w _ => by simp)
      · exact (((contDiffOn_const (c := -Real.log (Real.log (1 / t)))).add
          ((contDiffOn_const (c := 1 + epsT 2 t)).mul hG)).of_le two_le_inf).congr (fun w _ => by simp)
    · intro i
      rcases finset_fin_two_eq_cases i with rfl | rfl
      · exact levi_combo_nonneg (a := 1 + epsT 2 t) (b := 0) ha k j hyk hyj
          (Eventually.of_forall fun w => by
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; ring) v
      · exact levi_simple_nonneg (a := 1 + epsT 2 t) (b := -Real.log (Real.log (1 / t)))
          (by linarith) k hyk (Eventually.of_forall fun w => by
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; ring) v
  · push Not at hyj
    obtain ⟨rfl, hy0⟩ := hyj
    obtain ⟨δ, hδ, hpole⟩ := llT_near_pole t ht ht0
    have hW : {w : Fin 1 → ℂ | fsQ w < δ} ∈ 𝓝 y :=
      (isOpen_lt contDiff_fsQ.continuous continuous_const).mem_nhds (by simp [fsQ, hy0, hδ])
    refine levi_simple_nonneg (a := 1 + epsT 2 t) (b := -Real.log (Real.log (1 / t)))
      (by linarith) k hyk ?_ v
    filter_upwards [hW] with w hw
    rw [hφw, projLineAtlas_chart1, hpole w hw]
    ring

theorem llT_psh (t : ℝ) (ht : 0 < t) (ht0 : t ≤ T0) :
    IsPsh p1 (fsPot + LocPot.ofFun (llT t) + fsPot.rsmul (epsT 2 t)) := by
  intro x j y hy v
  exact llT_psh_chart t ht ht0 x j y ⟨hy.1, hy.2.1.1⟩ v

theorem llw_psh_chart (x : OnePoint ℂ) (j : Fin 2) (y : Fin 1 → ℂ)
    (hy : y ∈ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x)
    (hyj : j = 1 → y 0 ≠ 0) (v : Fin 1 → ℂ) :
    0 ≤ levi (fun w => fsPot.φ x ((p1.chart j).symm w) + llw ((p1.chart j).symm w)) y v := by
  obtain ⟨k, hφw, hk⟩ := fsPot_chart' x j
  have hDo : IsOpen ((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x) :=
    (p1.chart j).isOpen_inter_preimage_symm (fsPot.isOpen_U x)
  have hNo := hDo.inter (isOpen_goodSet j)
  refine levi_combo_nonneg (a := 1) (b := 0) le_rfl k j (hk y hy) hyj ?_ v
  filter_upwards [hNo.mem_nhds ⟨hy, hyj⟩] with w hw
  rw [hφw, projectiveLineLogLog_chart j w hw.2]
  ring

theorem llw_smoothOn_chart (j : Fin 2) :
    ContDiffOn ℝ ∞ (llw ∘ (p1.chart j).symm)
      ((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' (bdry projectiveLinePairSection)ᶜ) := by
  have hs : (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' (bdry projectiveLinePairSection)ᶜ =
      {w | j = 1 → w 0 ≠ 0} := Set.ext fun w => chartV_iff j w
  rw [hs]
  exact (contDiffOn_llwChart j).congr (fun w hw => projectiveLineLogLog_chart j w hw)

theorem singWeight : IsSingWeight p1 fsPot projectiveLinePairSection fsPot llw 1 := by
  refine ⟨projLine_isSmoothPotential, fun j => llw_smoothOn_chart j, ?_, fun y _ => ⟨?_, ?_⟩⟩
  · intro x j y hy v
    exact llw_psh_chart x j y ⟨hy.1, hy.2.1.1⟩ ((chartV_iff j y).1 ⟨hy.1, hy.2.2⟩) v
  · rw [llw]; linarith
  · linarith [projectiveLineLogLog_le_neg_one y]

end

end ReciprocityTheory.AnForm.P
end

section
namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

def projectiveLineLogLog (y : OnePoint ℂ) : ℝ := -Real.log (rW fsPot projectiveLinePairSection y)

def projectiveLineLogLogRegularized (t : ℝ) (y : OnePoint ℂ) : ℝ :=
  if projectiveLinePairSection y y = 0 then -Real.log (Real.log (1 / t)) else
    ReciprocityTheory.AnForm.A.regMax (epsT 1 t) ![projectiveLineLogLog y, -Real.log (Real.log (1 / t))]

def ProjectiveLineLogLogInhabited : Prop :=
  (∀ y, logNormSec fsPot projectiveLinePairSection y ≤ 0) ∧ IsSingWeight p1 fsPot projectiveLinePairSection fsPot projectiveLineLogLog 1 ∧
    ∃ C t₀ : ℝ, IsRegFamily p1 fsPot fsPot projectiveLinePairSection fsPot projectiveLineLogLog projectiveLineLogLogRegularized C t₀ ∧
      IsRegFamilyC2 p1 projectiveLinePairSection projectiveLineLogLog projectiveLineLogLogRegularized

theorem projectiveLine_isRegFamily : IsRegFamily p1 fsPot fsPot projectiveLinePairSection fsPot llw llT 2 T0 := by
  refine ⟨Real.exp_pos _, (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (neg_lt_zero.2 (Real.exp_pos _))), fun t ht ht0 => ?_⟩
  have hη := eps_pos ht ht0
  have hL := logell_pos ht ht0
  have hℓ := ell_pos ht ht0
  have hr3 : 0 ≤ t ^ ((1 : ℝ) / 3) := Real.rpow_nonneg ht.le _
  refine ⟨llT_smooth t ht ht0, ?_, ?_, ?_, llT_psh t ht ht0, ?_, ?_, ?_⟩
  · intro y
    by_cases hy : y = OnePoint.infty
    · subst hy; rw [llT_infty]; linarith
    · rw [llT_ne t hy]
      have := rm_le (η := epsT 1 t) (a := llw y) (b := -Real.log (Real.log (1 / t))) (m := 0) hη.le
        (by linarith [projectiveLineLogLog_le_neg_one y]) (by linarith)
      linarith [eps_le_one ht ht0]
  · intro y hy
    rw [llT_ne t (fun h => hy ((mem_boundary_projectiveLine y).2 h))]
    exact rm_ge_left _ _ _
  · intro y
    by_cases hy : y = OnePoint.infty
    · subst hy; rw [llT_infty]; linarith
    · rw [llT_ne t hy]
      have := rm_ge_right (epsT 1 t) (llw y) (-Real.log (Real.log (1 / t)))
      linarith
  · intro y hy hr
    rw [llT_ne t (fun h => hy ((mem_boundary_projectiveLine y).2 h)), epsT_two]
    have hc : -Real.log (Real.log (1 / t)) ≤ llw y := by
      rw [llw]; exact neg_le_neg (Real.log_le_log (rW_pos y) hr)
    have := rm_le hη.le (le_refl (llw y)) hc
    linarith
  · intro y hy
    rw [llT_ne t (fun h => hy ((mem_boundary_projectiveLine y).2 h)), epsT_two]
    have hrp := rW_pos y
    have hre := projectiveLine_weight_ge_exp_one y
    have h1 : Real.log (rW fsPot projectiveLinePairSection y) - Real.log (Real.log (1 / t)) ≤
        rW fsPot projectiveLinePairSection y / Real.log (1 / t) := by
      rw [← Real.log_div hrp.ne' hℓ.ne']
      have := Real.log_le_sub_one_of_pos (div_pos hrp hℓ)
      linarith
    have h2 : rW fsPot projectiveLinePairSection y / Real.log (1 / t) ≤ epsT 1 t * rW fsPot projectiveLinePairSection y := by
      have e : epsT 1 t * rW fsPot projectiveLinePairSection y =
          Real.log (Real.log (1 / t)) * rW fsPot projectiveLinePairSection y / Real.log (1 / t) := by
        unfold epsT; ring
      rw [e]
      apply div_le_div_of_nonneg_right _ hℓ.le
      have := logell_big ht ht0
      nlinarith [one_le_exp_one]
    have hc : -Real.log (Real.log (1 / t)) ≤ llw y + epsT 1 t * rW fsPot projectiveLinePairSection y := by
      rw [llw]; linarith
    have hm : llw y ≤ llw y + epsT 1 t * rW fsPot projectiveLinePairSection y := by
      have := mul_nonneg hη.le hrp.le; linarith
    have := rm_le hη.le hm hc
    have h5 : epsT 1 t / 2 ≤ epsT 1 t * rW fsPot projectiveLinePairSection y := by nlinarith [one_le_exp_one]
    linarith
  · intro t' htt' ht0' y
    have ht' : 0 < t' := lt_of_lt_of_le ht htt'
    have hη' := eps_pos ht' ht0'
    have hmono := eps_mono ht htt' ht0'
    have hc : -Real.log (Real.log (1 / t)) ≤ -Real.log (Real.log (1 / t')) :=
      neg_le_neg (Real.log_le_log (ell_pos ht' ht0') (ell_anti ht htt'))
    rw [epsT_two]
    by_cases hy : y = OnePoint.infty
    · subst hy; rw [llT_infty, llT_infty]; linarith
    · rw [llT_ne t hy, llT_ne t' hy]
      have := rm_le (m := ReciprocityTheory.AnForm.A.regMax (epsT 1 t') ![llw y, -Real.log (Real.log (1 / t'))])
        hη.le (rm_ge_left _ _ _) (le_trans hc (rm_ge_right _ _ _))
      linarith

theorem tuo_of_eventually {α β : Type*} [UniformSpace β] {F : ℝ → α → β} {f : α → β}
    {p : Filter ℝ} {K : Set α} (h : ∀ᶠ t in p, ∀ y ∈ K, F t y = f y) :
    TendstoUniformlyOn F f p K := by
  intro u hu
  filter_upwards [h] with t ht y hy
  rw [ht y hy]
  exact refl_mem_uniformity hu

theorem regFamilyC2_of_chart (j : Fin 2) (K : Set (Fin 1 → ℂ))
    (hK : K ⊆ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' (bdry projectiveLinePairSection)ᶜ) (hKc : IsCompact K) :
    TendstoUniformlyOn (fun t => llT t ∘ (p1.chart j).symm) (llw ∘ (p1.chart j).symm)
        (nhdsWithin 0 (Set.Ioi 0)) K ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (llT t ∘ (p1.chart j).symm))
        (fderiv ℝ (llw ∘ (p1.chart j).symm)) (nhdsWithin 0 (Set.Ioi 0)) K ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (llT t ∘ (p1.chart j).symm)))
        (fderiv ℝ (fderiv ℝ (llw ∘ (p1.chart j).symm))) (nhdsWithin 0 (Set.Ioi 0)) K := by
  have hVeq : (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' (bdry projectiveLinePairSection)ᶜ =
      {w | j = 1 → w 0 ≠ 0} := Set.ext fun w => chartV_iff j w
  have hVo : IsOpen ((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' (bdry projectiveLinePairSection)ᶜ) := by
    rw [hVeq]; exact isOpen_goodSet j
  obtain ⟨δ, hδ, hδV⟩ := hKc.exists_cthickening_subset_open hVo hK
  have hC : IsCompact (Metric.cthickening δ K) := hKc.cthickening
  have hgc : ContinuousOn (fun w => -Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)))
      (Metric.cthickening δ K) :=
    (contDiffOn_llwChart j).continuousOn.mono (fun w hw => (chartV_iff j w).1 (hδV hw))
  obtain ⟨m, hm⟩ := hC.bddBelow_image hgc
  have hT : 0 < min T0 (Real.exp (-Real.exp (1 - m))) := lt_min (Real.exp_pos _) (Real.exp_pos _)
  have hev : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ w ∈ Metric.cthickening δ K,
      llT t ((p1.chart j).symm w) = llw ((p1.chart j).symm w) := by
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    intro w hw
    have ht0 : t ≤ T0 := le_trans ht.2.le (min_le_left _ _)
    have ht1 : t ≤ Real.exp (-Real.exp (1 - m)) := le_trans ht.2.le (min_le_right _ _)
    have hwj : j = 1 → w 0 ≠ 0 := (chartV_iff j w).1 (hδV hw)
    rw [llT_chart_eq t j w hwj, projectiveLineLogLog_chart j w hwj]
    apply rm_eq_left (eps_pos ht.1 ht0).le
    have h1 : Real.exp (1 - m) ≤ Real.log (1 / t) := ell_ge ht.1 ht1
    have h2 : 1 - m ≤ Real.log (Real.log (1 / t)) := by
      have := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at this
    have h3 := eps_le_one ht.1 ht0
    have h4 : m ≤ -Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)) := hm ⟨w, hw, rfl⟩
    linarith
  have hloc : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ y ∈ K,
      (llT t ∘ (p1.chart j).symm) =ᶠ[𝓝 y] (llw ∘ (p1.chart j).symm) := by
    filter_upwards [hev] with t ht y hy
    have hmem : Metric.thickening δ K ∈ 𝓝 y :=
      Metric.isOpen_thickening.mem_nhds (Metric.self_subset_thickening hδ K hy)
    filter_upwards [hmem] with w hw
    exact ht w (Metric.thickening_subset_cthickening δ K hw)
  refine ⟨tuo_of_eventually ?_, tuo_of_eventually ?_, tuo_of_eventually ?_⟩
  · filter_upwards [hloc] with t ht y hy
    exact (ht y hy).eq_of_nhds
  · filter_upwards [hloc] with t ht y hy
    exact (ht y hy).fderiv_eq (𝕜 := ℝ)
  · filter_upwards [hloc] with t ht y hy
    exact ((ht y hy).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)

theorem projectiveLine_isRegFamilyC2 : IsRegFamilyC2 p1 projectiveLinePairSection llw llT :=
  fun j K hK hKc => regFamilyC2_of_chart j K hK hKc

theorem isRegFamily_inhabited : IsRegFamilyInhabitStatement := by
  intro e X _ A Θ L s hΘ hpos hL
  have hT : (0 : ℝ) < Real.exp (-Real.exp 1) := Real.exp_pos _
  have hT1 : Real.exp (-Real.exp 1) < 1 := (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (neg_lt_zero.2 (Real.exp_pos _)))
  have hεnn : ∀ t, 0 < t → t ≤ Real.exp (-Real.exp 1) → 0 ≤ epsT 1 t := by
    intro t ht ht0
    have h1 : Real.exp 1 ≤ Real.log (1 / t) := ell_ge ht ht0
    have h2 : 0 ≤ Real.log (Real.log (1 / t)) :=
      Real.log_nonneg (by linarith [one_le_exp_one])
    unfold epsT
    rw [one_mul]
    exact div_nonneg h2 (by linarith [Real.exp_pos 1])
  have hlog : ∀ t, 0 < t → t ≤ Real.exp (-Real.exp 1) → 0 ≤ Real.log (Real.log (1 / t)) := by
    intro t ht ht0
    have h1 : Real.exp 1 ≤ Real.log (1 / t) := ell_ge ht ht0
    exact Real.log_nonneg (by linarith [one_le_exp_one])
  refine ⟨⟨hT, hT1, fun t ht ht0 => ?_⟩, fun j K _ _ => ⟨?_, ?_, ?_⟩⟩
  · have hε := hεnn t ht ht0
    have hr3 : 0 ≤ t ^ ((1 : ℝ) / 3) := Real.rpow_nonneg ht.le _
    refine ⟨fun j => contDiffOn_const, fun _ => zero_le_one, fun _ _ => le_refl _,
      fun _ => by linarith [hlog t ht ht0], ?_, fun _ _ _ => by linarith,
      fun y _ => ?_, fun t' htt' ht0' _ => ?_⟩
    · intro x j y hy w
      have hyD : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x := ⟨hy.1, hy.2.2⟩
      have hc : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y :=
        ((hΘ.1 x j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm
          (Θ.isOpen_U x)).mem_nhds hyD)).of_le two_le_inf
      have h0 : 0 ≤ levi (Θ.φ x ∘ (A.chart j).symm) y w := by
        by_cases hw : w = 0
        · rw [hw, levi_zero]
        · exact (hpos x j y hyD w hw).le
      show 0 ≤ levi (fun z => Θ.φ x ((A.chart j).symm z) + 0 +
        epsT 1 t * Θ.φ x ((A.chart j).symm z)) y w
      simp only [add_zero]
      rw [levi_add_smul (f := fun z => Θ.φ x ((A.chart j).symm z))
        (g := fun z => Θ.φ x ((A.chart j).symm z)) (epsT 1 t) hc hc w]
      have := mul_nonneg hε h0
      exact add_nonneg h0 this
    · have h1 : Real.exp 1 ≤ rW L s y := by
        have := hL y; unfold rW; linarith
      have := mul_nonneg hε (le_trans (Real.exp_pos 1).le h1)
      linarith
    · have := hεnn t' (lt_of_lt_of_le ht htt') ht0'
      linarith
  · exact tuo_of_eventually (Eventually.of_forall fun _ _ _ => rfl)
  · exact tuo_of_eventually (Eventually.of_forall fun _ _ _ => rfl)
  · exact tuo_of_eventually (Eventually.of_forall fun _ _ _ => rfl)


theorem isRegFamilyInhabit : IsRegFamilyInhabitStatement := isRegFamily_inhabited

end

end ReciprocityTheory.AnForm.P
end
