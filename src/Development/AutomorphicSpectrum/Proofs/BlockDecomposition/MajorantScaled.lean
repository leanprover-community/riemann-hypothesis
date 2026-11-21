import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Kern
import BuildAid.ForwardExisting

section
noncomputable section

open MeasureTheory Matrix Set GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B

namespace GlobalTheory.CompanionTheory.MajC.KernInt

lemma lintegral_lo {s T : ℝ} (hs : 0 < s) (hT : 0 < T) :
    ∫⁻ r in Ioc (0 : ℝ) T, ENNReal.ofReal (r ^ (s - 1) * T ^ (-s)) = ENNReal.ofReal (1 / s) := by
  have hint : IntervalIntegrable (fun r : ℝ => r ^ (s - 1)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hI : IntegrableOn (fun r : ℝ => r ^ (s - 1) * T ^ (-s)) (Ioc 0 T) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1 hint).mul_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hI ?_]
  · congr 1
    rw [integral_mul_const, ← intervalIntegral.integral_of_le hT.le,
      integral_rpow (Or.inl (by linarith))]
    have h1 : s - 1 + 1 = s := by ring
    have hp : T ^ s ≠ 0 := (Real.rpow_pos_of_pos hT s).ne'
    rw [h1, Real.zero_rpow hs.ne', sub_zero, Real.rpow_neg hT.le]
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact mul_nonneg (Real.rpow_nonneg hr.1.le _) (Real.rpow_nonneg hT.le _)

lemma lintegral_hi {s T : ℝ} (hs : 0 < s) (hT : 0 < T) :
    ∫⁻ r in Ioi T, ENNReal.ofReal (r ^ (-s - 1) * T ^ s) = ENNReal.ofReal (1 / s) := by
  have ha : -s - 1 < -1 := by linarith
  have hI : IntegrableOn (fun r : ℝ => r ^ (-s - 1) * T ^ s) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt ha hT).mul_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hI ?_]
  · congr 1
    rw [integral_mul_const, integral_Ioi_rpow_of_lt ha hT]
    have h1 : -s - 1 + 1 = -s := by ring
    have hp : T ^ s ≠ 0 := (Real.rpow_pos_of_pos hT s).ne'
    rw [h1, Real.rpow_neg hT.le]
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have : 0 < r := hT.trans hr
    exact mul_nonneg (Real.rpow_nonneg this.le _) (Real.rpow_nonneg hT.le _)

def prof (s T r : ℝ) : ℝ := r * ((r ^ 2)⁻¹ * min ((r / T) ^ s) ((T / r) ^ s))

lemma measurable_prof (s T : ℝ) : Measurable (prof s T) := by
  unfold prof
  fun_prop

lemma prof_le_lo {s T r : ℝ} (hT : 0 < T) (hr : 0 < r) :
    prof s T r ≤ r ^ (s - 1) * T ^ (-s) := by
  unfold prof
  have h1 : r * (r ^ 2)⁻¹ = r⁻¹ := by field_simp
  have h2 : r ^ (s - 1) * T ^ (-s) = r⁻¹ * (r / T) ^ s := by
    rw [Real.rpow_sub_one hr.ne', Real.div_rpow hr.le hT.le, Real.rpow_neg hT.le]
    field_simp
  rw [← mul_assoc, h1, h2]
  exact mul_le_mul_of_nonneg_left (min_le_left _ _) (inv_nonneg.2 hr.le)

lemma prof_le_hi {s T r : ℝ} (hT : 0 < T) (hr : 0 < r) :
    prof s T r ≤ r ^ (-s - 1) * T ^ s := by
  unfold prof
  have h1 : r * (r ^ 2)⁻¹ = r⁻¹ := by field_simp
  have h2 : r ^ (-s - 1) * T ^ s = r⁻¹ * (T / r) ^ s := by
    rw [Real.rpow_sub_one hr.ne', Real.div_rpow hT.le hr.le, Real.rpow_neg hr.le]
    field_simp
  rw [← mul_assoc, h1, h2]
  exact mul_le_mul_of_nonneg_left (min_le_right _ _) (inv_nonneg.2 hr.le)

lemma lintegral_prof_le {s T : ℝ} (hs : 0 < s) (hT : 0 < T) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (prof s T r) ≤ ENNReal.ofReal (2 / s) := by
  rw [← Ioc_union_Ioi_eq_Ioi hT.le, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  have hlo : ∫⁻ r in Ioc (0 : ℝ) T, ENNReal.ofReal (prof s T r) ≤ ENNReal.ofReal (1 / s) := by
    rw [← lintegral_lo hs hT]
    exact setLIntegral_mono' measurableSet_Ioc fun r hr =>
      ENNReal.ofReal_le_ofReal (prof_le_lo hT hr.1)
  have hhi : ∫⁻ r in Ioi T, ENNReal.ofReal (prof s T r) ≤ ENNReal.ofReal (1 / s) := by
    rw [← lintegral_hi hs hT]
    exact setLIntegral_mono' measurableSet_Ioi fun r hr =>
      ENNReal.ofReal_le_ofReal (prof_le_hi hT (hT.trans hr))
  have h2 : ENNReal.ofReal (2 / s) = ENNReal.ofReal (1 / s) + ENNReal.ofReal (1 / s) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [h2]
  exact add_le_add hlo hhi

theorem lintegral_kern_le : ∀ s : ℝ, 0 < s → ∃ K : ℝ, 0 ≤ K ∧ ∀ T₀ : ℝ, 0 < T₀ →
    ∫⁻ z : ℂ, ENNReal.ofReal (kern s T₀ z) ≤ ENNReal.ofReal K := by
  intro s hs
  refine ⟨2 / s * (2 * Real.pi), by positivity, fun T hT => ?_⟩
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have hcongr : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
        ENNReal.ofReal (kern s T (Complex.polarCoord.symm p)) =
      ∫⁻ p in polarCoord.target, ENNReal.ofReal (prof s T p.1) := by
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo |> fun h => by
      rw [polarCoord_target]; exact h) fun p hp => ?_
    rw [polarCoord_target] at hp
    have hp1 : 0 < p.1 := hp.1
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    simp only [smul_eq_mul, kern, hn, prof]
    rw [ENNReal.ofReal_mul hp1.le]
  rw [hcongr, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hprod := lintegral_prod_mul (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := volume.restrict (Ioo (-Real.pi) Real.pi))
    (f := fun r => ENNReal.ofReal (prof s T r)) (g := fun _ => (1 : ENNReal))
    (measurable_prof s T).ennreal_ofReal.aemeasurable aemeasurable_const
  simp only [mul_one] at hprod
  rw [hprod, lintegral_one, Measure.restrict_apply_univ, Real.volume_Ioo,
    ENNReal.ofReal_mul (by positivity)]
  have h2 : Real.pi - -Real.pi = 2 * Real.pi := by ring
  rw [h2]
  exact mul_le_mul_left (lintegral_prof_le hs hT) _

end GlobalTheory.CompanionTheory.MajC.KernInt
end
end

section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_kernel_uniform_bound : ∀ s : ℝ, 0 < s → ∃ K : ℝ, 0 ≤ K ∧ ∀ T₀ : ℝ, 0 < T₀ → ∫⁻ z : ℂ, ENNReal.ofReal (kern s T₀ z) ≤ ENNReal.ofReal K := by
  first | exact @GlobalTheory.CompanionTheory.MajC.KernInt.lintegral_kern_le | exact GlobalTheory.CompanionTheory.MajC.KernInt.lintegral_kern_le | (intros; apply GlobalTheory.CompanionTheory.MajC.KernInt.lintegral_kern_le <;> assumption)
end

section
section
noncomputable section

open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B

namespace GlobalTheory.CompanionTheory.MajC.TB

theorem gain_le {ε A D E T : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 2 * ε ≤ N) (hA : 0 < A) (hD : 0 < D)
    (hE : 0 < E) (hT : 0 < T) :
    (T * E / (A + T * E)) ^ N * ((1 + T / (D * E)) ^ N)⁻¹ ≤
      (D * E ^ 2 / A) ^ ε * min ((T / √(A * D)) ^ (2 * ε)) ((√(A * D) / T) ^ (2 * ε)) := by
  have hAD : 0 < A * D := mul_pos hA hD
  obtain ⟨T₀, hT₀⟩ : ∃ T₀, T₀ = √(A * D) := ⟨_, rfl⟩
  rw [← hT₀]
  have hT₀p : 0 < T₀ := hT₀ ▸ Real.sqrt_pos.mpr hAD
  have hsq : T₀ ^ 2 = A * D := by rw [hT₀]; exact Real.sq_sqrt hAD.le
  have hTE : 0 < T * E := mul_pos hT hE
  have hs : (0 : ℝ) ≤ 2 * ε := by positivity
  have hc : 0 < D * E ^ 2 / A := by positivity

  obtain ⟨x, hx⟩ : ∃ x, x = T * E / (A + T * E) := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one (by positivity)]; linarith
  have hxA : x ≤ T * E / A := by
    rw [hx]; exact div_le_div_of_nonneg_left hTE.le hA (by linarith)
  have e1 : (T * E / A) ^ (2 * ε) = (D * E ^ 2 / A) ^ ε * (T / T₀) ^ (2 * ε) := by
    rw [Real.rpow_mul (by positivity), Real.rpow_mul (by positivity), Real.rpow_two, Real.rpow_two,
      ← Real.mul_rpow hc.le (by positivity)]
    congr 1
    rw [div_pow, div_pow, hsq]
    field_simp
  have hxN : x ^ N ≤ (D * E ^ 2 / A) ^ ε * (T / T₀) ^ (2 * ε) := by
    rw [← e1, ← Real.rpow_natCast]
    exact (Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hN).trans
      (Real.rpow_le_rpow hx0.le hxA hs)
  have hxN1 : x ^ N ≤ 1 := pow_le_one₀ hx0.le hx1

  obtain ⟨w, hw⟩ : ∃ w, w = T / (D * E) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; positivity
  have e2 : (w⁻¹) ^ (2 * ε) = (D * E ^ 2 / A) ^ ε * (T₀ / T) ^ (2 * ε) := by
    rw [Real.rpow_mul (by positivity), Real.rpow_mul (by positivity), Real.rpow_two, Real.rpow_two,
      ← Real.mul_rpow hc.le (by positivity)]
    congr 1
    rw [hw, div_pow, hsq, inv_pow, div_pow, mul_pow]
    field_simp
  have hwN : ((1 + w) ^ N)⁻¹ ≤ (D * E ^ 2 / A) ^ ε * (T₀ / T) ^ (2 * ε) := by
    rw [← e2, Real.inv_rpow hw0.le]
    apply inv_anti₀ (Real.rpow_pos_of_pos hw0 _)
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow hw0.le (by linarith) hs).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith) hN)
  have hwN1 : ((1 + w) ^ N)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hwN0 : 0 ≤ ((1 + w) ^ N)⁻¹ := by positivity
  rw [← hx, ← hw, mul_min_of_nonneg _ _ (Real.rpow_nonneg hc.le _)]
  apply le_min
  · exact (mul_le_of_le_one_right (by positivity) hwN1).trans hxN
  · exact (mul_le_of_le_one_left hwN0 hxN1).trans hwN

theorem const_eq {ε A D E : ℝ} (hA : 0 < A) (hD : 0 < D) (hE : 0 < E) :
    (D ^ 2 * E ^ 2)⁻¹ * (D * E ^ 2 / A) ^ ε = A ^ (-ε) * D ^ (-2 + ε) * E ^ (-2 + 2 * ε) := by
  rw [Real.rpow_add hD, Real.rpow_add hE, Real.rpow_neg hA.le, Real.rpow_neg hD.le,
    Real.rpow_neg hE.le, Real.rpow_two, Real.rpow_two, Real.div_rpow (by positivity) hA.le,
    Real.mul_rpow hD.le (by positivity), Real.rpow_mul hE.le, Real.rpow_two]
  have := (Real.rpow_pos_of_pos hA ε).ne'
  field_simp

theorem jm_le_kern {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 2 * ε ≤ N) (h : M22) (a b t : ℂ) (ha : a ≠ 0)
    (hD : 0 < dt h) (hE : 0 < ‖eta h‖) :
    jm N h t a b ≤ (dt h ^ 2 * ‖eta h‖ ^ 2)⁻¹ * (dt h * ‖eta h‖ ^ 2 / ‖a‖) ^ ε *
        ((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹ * kern (2 * ε) (√(‖a‖ * dt h)) t := by
  have hA : 0 < ‖a‖ := norm_pos_iff.mpr ha
  by_cases ht : t = 0
  · subst ht
    simp [jm, kern]
  have hT : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have key := gain_le (T := ‖t‖) hε hN hA hD hE hT
  have hP : 0 ≤ ((1 + ‖h‖) ^ N)⁻¹ := by positivity
  have hQ : 0 ≤ ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹ := by positivity
  have hI : 0 ≤ (dt h ^ 2 * ‖eta h‖ ^ 2)⁻¹ * (‖t‖ ^ 2)⁻¹ * ((1 + ‖h‖) ^ N)⁻¹ *
      ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹ := by positivity
  have := mul_le_mul_of_nonneg_left key hI
  calc jm N h t a b = (dt h ^ 2 * ‖eta h‖ ^ 2)⁻¹ * (‖t‖ ^ 2)⁻¹ * ((1 + ‖h‖) ^ N)⁻¹ *
      ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹ * ((‖t‖ * ‖eta h‖ / (‖a‖ + ‖t‖ * ‖eta h‖)) ^ N *
        ((1 + ‖t‖ / (dt h * ‖eta h‖)) ^ N)⁻¹) := by
        simp only [jm, dt, mul_inv]; ring
    _ ≤ _ := this
    _ = _ := by simp only [kern]; ring

theorem lintegral_jm_le : ∀ (ε K : ℝ), 0 < ε → 0 ≤ K →
    (∀ T₀ : ℝ, 0 < T₀ → ∫⁻ z : ℂ, ENNReal.ofReal (kern (2 * ε) T₀ z) ≤ ENNReal.ofReal K) →
    ∀ N : ℕ, 2 * ε ≤ N → ∀ (h : M22) (a b : ℂ), a ≠ 0 → 0 < dt h → 0 < ‖eta h‖ →
    ∫⁻ t : ℂ, ENNReal.ofReal (jm N h t a b) ≤
      ENNReal.ofReal (K * ‖a‖ ^ (-ε) * dt h ^ (-2 + ε) * ‖eta h‖ ^ (-2 + 2 * ε) *
        ((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹) := by
  intro ε K hε hK hker N hN h a b ha hD hE
  have hA : 0 < ‖a‖ := norm_pos_iff.mpr ha
  obtain ⟨C, hC⟩ : ∃ C, C = (dt h ^ 2 * ‖eta h‖ ^ 2)⁻¹ * (dt h * ‖eta h‖ ^ 2 / ‖a‖) ^ ε *
      ((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹ := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]
    have : 0 ≤ (dt h * ‖eta h‖ ^ 2 / ‖a‖) ^ ε := Real.rpow_nonneg (by positivity) _
    positivity
  have hT₀ : 0 < √(‖a‖ * dt h) := Real.sqrt_pos.mpr (mul_pos hA hD)
  calc ∫⁻ t : ℂ, ENNReal.ofReal (jm N h t a b)
      ≤ ∫⁻ t : ℂ, ENNReal.ofReal C * ENNReal.ofReal (kern (2 * ε) (√(‖a‖ * dt h)) t) := by
        refine lintegral_mono fun t => ?_
        rw [← ENNReal.ofReal_mul hC0, hC]
        exact ENNReal.ofReal_le_ofReal (jm_le_kern hε hN h a b t ha hD hE)
    _ = ENNReal.ofReal C * ∫⁻ t : ℂ, ENNReal.ofReal (kern (2 * ε) (√(‖a‖ * dt h)) t) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal K := by gcongr; exact hker _ hT₀
    _ = ENNReal.ofReal (C * K) := (ENNReal.ofReal_mul hC0).symm
    _ = _ := by
        congr 1
        rw [hC, const_eq hA hD hE]
        ring

end GlobalTheory.CompanionTheory.MajC.TB
end
end

open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_majorant_fiber_bound : ∀ (ε K : ℝ), 0 < ε → 0 ≤ K → (∀ T₀ : ℝ, 0 < T₀ → ∫⁻ z : ℂ, ENNReal.ofReal (kern (2 * ε) T₀ z) ≤ ENNReal.ofReal K) → ∀ N : ℕ, 2 * ε ≤ N → ∀ (h : M22) (a b : ℂ), a ≠ 0 → 0 < dt h → 0 < ‖eta h‖ → ∫⁻ t : ℂ, ENNReal.ofReal (jm N h t a b) ≤ ENNReal.ofReal (K * ‖a‖ ^ (-ε) * dt h ^ (-2 + ε) * ‖eta h‖ ^ (-2 + 2 * ε) * ((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.MajC.TB.lintegral_jm_le
end

section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B

noncomputable section

namespace GlobalTheory.CompanionTheory.MajC

theorem kern_nonneg' (s T : ℝ) (hT : 0 < T) (z : ℂ) : 0 ≤ kern s T z := by
  unfold kern
  refine mul_nonneg (by positivity) (le_min ?_ ?_)
  · exact Real.rpow_nonneg (by positivity) _
  · exact Real.rpow_nonneg (by positivity) _

theorem gm_nonneg' (ε β : ℝ) (m : ℕ) (hβ : 0 < β) (h : M22) : 0 ≤ gm ε β m h := by
  unfold gm
  split_ifs with hc
  · have h1 : 0 ≤ β ^ (-ε) := Real.rpow_nonneg hβ.le _
    have h2 : 0 ≤ ‖h 0 0‖ ^ (-4 + ε) := Real.rpow_nonneg (norm_nonneg _) _
    have h3 := kern_nonneg' ε β hβ (h 1 1 - h 1 0 / h 0 0 * h 0 1)
    positivity
  · exact le_rfl

theorem radial_bound (ε β r : ℝ) (N : ℕ) (hε : 0 < ε) (hβ : 0 < β) (hr : 0 < r)
    (hN : 2 * ε ≤ N) :
    r ^ (-(2 + ε)) * ((1 + β / r) ^ N)⁻¹ ≤
      β ^ (-ε) * ((r ^ 2)⁻¹ * min ((r / β) ^ ε) ((β / r) ^ ε)) := by
  have hw : 0 < β / r := div_pos hβ hr
  set a := r ^ ε with ha
  set b := β ^ ε with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos hr _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hβ _
  set W := (1 + β / r) ^ N with hWdef
  have hW1 : 1 ≤ W := one_le_pow₀ (by linarith)
  have hW0 : 0 < W := by linarith
  have e1 : (β / r) ^ ε = b / a := Real.div_rpow hβ.le hr.le _
  have e2 : (r / β) ^ ε = a / b := Real.div_rpow hr.le hβ.le _
  have e3 : r ^ (-(2 + ε)) = (r ^ 2)⁻¹ * a⁻¹ := by
    rw [neg_add, Real.rpow_add hr, Real.rpow_neg hr.le, Real.rpow_neg hr.le, Real.rpow_two]
  have e4 : β ^ (-ε) = b⁻¹ := Real.rpow_neg hβ.le _
  have hW2 : (b / a) ^ 2 ≤ W := by
    have s1 : (b / a) ^ 2 = (β / r) ^ (2 * ε) := by
      rw [← e1, mul_comm, Real.rpow_mul hw.le, Real.rpow_two]
    have s2 : (β / r) ^ (2 * ε) ≤ (1 + β / r) ^ (2 * ε) :=
      Real.rpow_le_rpow hw.le (by linarith) (by positivity)
    have s3 : (1 + β / r) ^ (2 * ε) ≤ (1 + β / r) ^ (N : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hN
    rw [Real.rpow_natCast] at s3
    rw [s1]
    exact s2.trans s3
  rw [e1, e2, e3, e4]
  have hr2 : 0 < (r ^ 2)⁻¹ := by positivity
  have key : a⁻¹ * W⁻¹ ≤ b⁻¹ * min (a / b) (b / a) := by
    rw [mul_min_of_nonneg _ _ (by positivity)]
    refine le_min ?_ ?_
    · have : W⁻¹ ≤ ((b / a) ^ 2)⁻¹ := inv_anti₀ (by positivity) hW2
      calc a⁻¹ * W⁻¹ ≤ a⁻¹ * ((b / a) ^ 2)⁻¹ := by gcongr
        _ = b⁻¹ * (a / b) := by field_simp
    · have : W⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
      calc a⁻¹ * W⁻¹ ≤ a⁻¹ * 1 := by gcongr
        _ = b⁻¹ * (b / a) := by field_simp
  calc (r ^ 2)⁻¹ * a⁻¹ * W⁻¹ = (r ^ 2)⁻¹ * (a⁻¹ * W⁻¹) := by ring
    _ ≤ (r ^ 2)⁻¹ * (b⁻¹ * min (a / b) (b / a)) := by gcongr
    _ = b⁻¹ * ((r ^ 2)⁻¹ * min (a / b) (b / a)) := by ring

theorem dt_eq (h : M22) : dt h = ‖h 0 0 * h 1 1 - h 0 1 * h 1 0‖ := by
  unfold dt
  rw [Matrix.det_fin_two]
  simp [Matrix.of_apply]

theorem dt_swp (h : M22) : dt (swp h) = dt h := by
  rw [dt_eq, dt_eq]
  have : (swp h) 0 0 * (swp h) 1 1 - (swp h) 0 1 * (swp h) 1 0
      = -(h 0 0 * h 1 1 - h 0 1 * h 1 0) := by
    simp [swp]; ring
  rw [this, norm_neg]

theorem col_swp (h : M22) : col (swp h) = col h := by
  simp [col, swp, max_comm]

theorem norm_swp_le (h : M22) : ‖swp h‖ ≤ ‖h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  fin_cases i
  · simpa [swp] using norm_le_pi_norm h 1
  · simpa [swp] using norm_le_pi_norm h 0

theorem swp_swp (h : M22) : swp (swp h) = h := by
  funext i
  fin_cases i <;> simp [swp]

theorem norm_swp (h : M22) : ‖swp h‖ = ‖h‖ :=
  le_antisymm (norm_swp_le h) (by simpa [swp_swp] using norm_swp_le (swp h))

theorem hm_swp (ε β : ℝ) (N : ℕ) (h : M22) : hm ε N β (swp h) = hm ε N β h := by
  unfold hm
  rw [dt_swp, col_swp, norm_swp]

theorem entry_le (h : M22) (i j : Fin 2) : ‖h i j‖ ≤ ‖h‖ :=
  (norm_le_pi_norm (h i) j).trans (norm_le_pi_norm h i)

theorem one_region (ε β : ℝ) (m N : ℕ) (hε : 0 < ε) (hβ : 0 < β) (hm' : 2 * ε ≤ m)
    (hN : 2 * m ≤ N) (h : M22) (hv : ‖h 1 0‖ ≤ ‖h 0 0‖) (hd : dt h ≠ 0) :
    hm ε N β h ≤ gm ε β m h := by
  have hu : h 0 0 ≠ 0 := by
    intro hu
    have hv0 : h 1 0 = 0 := by
      rw [hu, norm_zero] at hv
      exact norm_le_zero_iff.1 hv
    apply hd
    rw [dt_eq, hu, hv0]
    simp
  set z := h 1 1 - h 1 0 / h 0 0 * h 0 1 with hz
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = h 0 0 * z := by
    rw [hz]; field_simp
  have hU : 0 < ‖h 0 0‖ := norm_pos_iff.2 hu
  have hdt : dt h = ‖h 0 0‖ * ‖z‖ := by rw [dt_eq, hdet, norm_mul]
  have hr : 0 < ‖z‖ := by
    have : 0 < dt h := lt_of_le_of_ne (by rw [dt_eq]; exact norm_nonneg _) (Ne.symm hd)
    rw [hdt] at this
    exact (pos_iff_pos_of_mul_pos this).1 hU
  have hcol : col h = ‖h 0 0‖ := max_eq_left hv
  have hgm : gm ε β m h = β ^ (-ε) * ‖h 0 0‖ ^ (-4 + ε) * ((1 + ‖h 0 0‖) ^ m)⁻¹ *
      ((1 + ‖h 0 1‖) ^ m)⁻¹ * kern ε β z := by
    unfold gm
    rw [if_pos ⟨hv, hu⟩]
  rw [hgm]
  have hfrac : β * (‖h 0 0‖ / (‖h 0 0‖ * ‖z‖)) = β / ‖z‖ := by field_simp
  have hpow : (‖h 0 0‖ * ‖z‖) ^ (-(2 + ε)) * ‖h 0 0‖ ^ (-2 + 2 * ε)
      = ‖h 0 0‖ ^ (-4 + ε) * ‖z‖ ^ (-(2 + ε)) := by
    rw [Real.mul_rpow hU.le hr.le, mul_right_comm, ← Real.rpow_add hU]
    congr 2
    ring
  have hA : ((1 + ‖h‖) ^ N)⁻¹ ≤ ((1 + ‖h 0 0‖) ^ m)⁻¹ * ((1 + ‖h 0 1‖) ^ m)⁻¹ := by
    rw [← mul_inv]
    apply inv_anti₀ (by positivity)
    have h1 : 1 + ‖h 0 0‖ ≤ 1 + ‖h‖ := by linarith [entry_le h 0 0]
    have h2 : 1 + ‖h 0 1‖ ≤ 1 + ‖h‖ := by linarith [entry_le h 0 1]
    have h3 : (1 : ℝ) ≤ 1 + ‖h‖ := by linarith [norm_nonneg h]
    calc (1 + ‖h 0 0‖) ^ m * (1 + ‖h 0 1‖) ^ m
        ≤ (1 + ‖h‖) ^ m * (1 + ‖h‖) ^ m := by gcongr
      _ = (1 + ‖h‖) ^ (2 * m) := by rw [two_mul, pow_add]
      _ ≤ (1 + ‖h‖) ^ N := pow_le_pow_right₀ h3 hN
  have hN' : 2 * ε ≤ (N : ℝ) := by
    have : (m : ℝ) ≤ N := by
      have : m ≤ N := by omega
      exact_mod_cast this
    linarith
  have hB := radial_bound ε β ‖z‖ N hε hβ hr hN'
  have hk : kern ε β z = (‖z‖ ^ 2)⁻¹ * min ((‖z‖ / β) ^ ε) ((β / ‖z‖) ^ ε) := rfl
  unfold hm
  rw [hdt, hcol, hfrac, hpow, hk]
  have hUp : 0 ≤ ‖h 0 0‖ ^ (-4 + ε) := Real.rpow_nonneg hU.le _
  have hzp : 0 ≤ ‖z‖ ^ (-(2 + ε)) * ((1 + β / ‖z‖) ^ N)⁻¹ := by
    have := Real.rpow_nonneg hr.le (-(2 + ε))
    positivity
  calc ‖h 0 0‖ ^ (-4 + ε) * ‖z‖ ^ (-(2 + ε)) * ((1 + ‖h‖) ^ N)⁻¹ * ((1 + β / ‖z‖) ^ N)⁻¹
      = ‖h 0 0‖ ^ (-4 + ε) * (((1 + ‖h‖) ^ N)⁻¹ *
          (‖z‖ ^ (-(2 + ε)) * ((1 + β / ‖z‖) ^ N)⁻¹)) := by ring
    _ ≤ ‖h 0 0‖ ^ (-4 + ε) * ((((1 + ‖h 0 0‖) ^ m)⁻¹ * ((1 + ‖h 0 1‖) ^ m)⁻¹) *
          (β ^ (-ε) * ((‖z‖ ^ 2)⁻¹ * min ((‖z‖ / β) ^ ε) ((β / ‖z‖) ^ ε)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hUp
        exact mul_le_mul hA hB hzp (by positivity)
    _ = _ := by ring

theorem hm_le_gm_add (ε β : ℝ) (m N : ℕ) (hε : 0 < ε) (hβ : 0 < β) (hm' : 2 * ε ≤ m)
    (hN : 2 * m ≤ N) (h : M22) : hm ε N β h ≤ gm ε β m h + gm ε β m (swp h) := by
  have g1 := gm_nonneg' ε β m hβ h
  have g2 := gm_nonneg' ε β m hβ (swp h)
  by_cases hd : dt h = 0
  · have : hm ε N β h = 0 := by
      unfold hm
      rw [hd, Real.zero_rpow (by linarith)]
      simp
    rw [this]
    exact add_nonneg g1 g2
  by_cases hv : ‖h 1 0‖ ≤ ‖h 0 0‖
  · have := one_region ε β m N hε hβ hm' hN h hv hd
    linarith
  · have hv' : ‖(swp h) 1 0‖ ≤ ‖(swp h) 0 0‖ := by
      have : ‖h 0 0‖ ≤ ‖h 1 0‖ := (not_le.1 hv).le
      simpa [swp] using this
    have := one_region ε β m N hε hβ hm' hN (swp h) hv' (by rw [dt_swp]; exact hd)
    rw [hm_swp] at this
    linarith

end GlobalTheory.CompanionTheory.MajC
end
end

section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorant_le_sum_swap : ∀ (ε β : ℝ) (m N : ℕ), 0 < ε → 0 < β → 2 * ε ≤ m → 2 * m ≤ N → ∀ h : M22, hm ε N β h ≤ gm ε β m h + gm ε β m (swp h) := by
  first | exact @GlobalTheory.CompanionTheory.MajC.hm_le_gm_add | exact GlobalTheory.CompanionTheory.MajC.hm_le_gm_add | (intros; apply GlobalTheory.CompanionTheory.MajC.hm_le_gm_add <;> assumption)
end

section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B

noncomputable section

namespace GlobalTheory.CompanionTheory.MajGm

theorem measurable_kern (s T : ℝ) : Measurable (kern s T) := by
  unfold kern
  refine Measurable.mul (by fun_prop) (Measurable.min (by fun_prop) (by fun_prop))

theorem measurable_gm (ε β : ℝ) (m : ℕ) : Measurable (gm ε β m) := by
  unfold gm
  have hk := measurable_kern ε β
  refine Measurable.ite ?_ ?_ (by fun_prop)
  · have h1 : MeasurableSet {h : M22 | ‖h 1 0‖ ≤ ‖h 0 0‖} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have h2 : MeasurableSet {h : M22 | h 0 0 ≠ 0} :=
      (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl
    exact h1.inter h2
  · refine Measurable.mul (by fun_prop) (hk.comp (by fun_prop))

theorem kern_nonneg (s T : ℝ) (hT : 0 < T) (z : ℂ) : 0 ≤ kern s T z := by
  unfold kern
  have h1 : 0 ≤ ‖z‖ / T := by positivity
  have h2 : 0 ≤ T / ‖z‖ := by positivity
  exact mul_nonneg (by positivity)
    (le_min (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _))

theorem real_bound (ε r : ℝ) (m : ℕ) (hε : 0 < ε) (hm : 2 * ε ≤ m) (hr : 0 < r) :
    r ^ (-4 + ε) * ((1 + r) ^ m)⁻¹ * r ^ 2 ≤ (r ^ 2)⁻¹ * min ((r / 1) ^ ε) ((1 / r) ^ ε) := by
  have e1 : r ^ (-4 + ε) * r ^ 2 = (r ^ 2)⁻¹ * r ^ ε := by
    rw [Real.rpow_add hr, show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hr.le,
      Real.rpow_natCast]
    field_simp
  have hw0 : 0 < ((1 + r) ^ m)⁻¹ := by positivity
  have hw1 : ((1 + r) ^ m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hrε : 0 < r ^ ε := Real.rpow_pos_of_pos hr _
  have key : r ^ ε * ((1 + r) ^ m)⁻¹ ≤ min ((r / 1) ^ ε) ((1 / r) ^ ε) := by
    refine le_min ?_ ?_
    · rw [div_one]
      exact mul_le_of_le_one_right hrε.le hw1
    · rcases le_total r 1 with h | h
      · have : r ≤ 1 / r := by
          rw [le_div_iff₀ hr]
          nlinarith
        calc r ^ ε * ((1 + r) ^ m)⁻¹ ≤ r ^ ε := mul_le_of_le_one_right hrε.le hw1
          _ ≤ (1 / r) ^ ε := Real.rpow_le_rpow hr.le this hε.le
      · have h2 : r ^ (2 * ε) ≤ (1 + r) ^ m := by
          calc r ^ (2 * ε) ≤ r ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le h hm
            _ = r ^ m := Real.rpow_natCast _ _
            _ ≤ (1 + r) ^ m := pow_le_pow_left₀ hr.le (by linarith) _
        have h3 : (1 / r) ^ ε = (r ^ ε)⁻¹ := by
          rw [one_div, Real.inv_rpow hr.le]
        have h4 : r ^ (2 * ε) = r ^ ε * r ^ ε := by
          rw [two_mul, Real.rpow_add hr]
        rw [h4] at h2
        rw [h3, ← div_eq_mul_inv, div_le_iff₀ (by positivity), inv_mul_eq_div,
          le_div_iff₀ hrε]
        exact h2
  calc r ^ (-4 + ε) * ((1 + r) ^ m)⁻¹ * r ^ 2
      = (r ^ (-4 + ε) * r ^ 2) * ((1 + r) ^ m)⁻¹ := by ring
    _ = (r ^ 2)⁻¹ * (r ^ ε * ((1 + r) ^ m)⁻¹) := by rw [e1]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key (by positivity)

theorem finite_Q (m : ℕ) (hm : 3 ≤ m) :
    ∫⁻ x : ℂ, ENNReal.ofReal (((1 + ‖x‖) ^ m)⁻¹) < ⊤ := by
  have h : Integrable (fun x : ℂ => (1 + ‖x‖) ^ (-(m : ℝ))) volume := by
    apply integrable_one_add_norm
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm
    simp only [Complex.finrank_real_complex]
    push_cast
    linarith
  have h2 := h.lintegral_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) h2
  refine lintegral_congr fun x => ?_
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

theorem lint_rows (F : M22 → ENNReal) (hF : Measurable F) :
    ∫⁻ h, F h = ∫⁻ a : ℂ × ℂ, ∫⁻ v : ℂ, ∫⁻ y : ℂ, F ![![a.1, a.2], ![v, y]] := by
  have e2 := volume_preserving_piFinTwo (fun _ : Fin 2 => ℂ)
  have e1 := volume_preserving_piFinTwo (fun _ : Fin 2 => Fin 2 → ℂ)
  have P := (e1.symm _).comp ((e2.symm _).prod (e2.symm _))
  have hΦ : (⇑(MeasurableEquiv.piFinTwo fun _ : Fin 2 => Fin 2 → ℂ).symm ∘
      Prod.map (MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℂ).symm
        (MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℂ).symm) =
      fun p : (ℂ × ℂ) × (ℂ × ℂ) => (![![p.1.1, p.1.2], ![p.2.1, p.2.2]] : M22) := by
    funext p
    funext i j
    fin_cases i <;> fin_cases j <;> simp [MeasurableEquiv.piFinTwo]
  rw [hΦ] at P
  have hG : Measurable fun p : (ℂ × ℂ) × (ℂ × ℂ) =>
      F (![![p.1.1, p.1.2], ![p.2.1, p.2.2]] : M22) := hF.comp P.measurable
  rw [← P.lintegral_comp hF, lintegral_prod _ hG.aemeasurable]
  refine lintegral_congr fun a => ?_
  have hG2 : Measurable fun b : ℂ × ℂ => F (![![a.1, a.2], ![b.1, b.2]] : M22) :=
    hG.comp (measurable_prodMk_left (x := a))
  rw [Measure.volume_eq_prod, lintegral_prod _ hG2.aemeasurable]

theorem inner_le (ε K β : ℝ) (m : ℕ) (hε : 0 < ε) (hK : 0 ≤ K) (hβ : 0 < β)
    (hker : ∫⁻ z : ℂ, ENNReal.ofReal (kern ε β z) ≤ ENNReal.ofReal K) (hm : 2 * ε ≤ m)
    (u x : ℂ) :
    ∫⁻ v : ℂ, ∫⁻ y : ℂ, ENNReal.ofReal (gm ε β m ![![u, x], ![v, y]]) ≤
      ENNReal.ofReal (β ^ (-ε) * Real.pi * K) * ENNReal.ofReal (kern ε 1 u) *
        ENNReal.ofReal (((1 + ‖x‖) ^ m)⁻¹) := by
  by_cases hu : u = 0
  · subst hu
    simp [gm]
  have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hβε : 0 < β ^ (-ε) := Real.rpow_pos_of_pos hβ _
  have hP : 0 < ‖u‖ ^ (-4 + ε) := Real.rpow_pos_of_pos hr _
  have hb : 0 < ((1 + ‖x‖) ^ m)⁻¹ := by positivity
  have hw : 0 < ((1 + ‖u‖) ^ m)⁻¹ := by positivity
  set A : ℝ := β ^ (-ε) * ‖u‖ ^ (-4 + ε) * ((1 + ‖u‖) ^ m)⁻¹ * ((1 + ‖x‖) ^ m)⁻¹ with hAdef
  have hA : 0 ≤ A := by positivity
  have h1 : ∀ v : ℂ, ∫⁻ y : ℂ, ENNReal.ofReal (gm ε β m ![![u, x], ![v, y]]) ≤
      (Metric.closedBall (0 : ℂ) ‖u‖).indicator
        (fun _ => ENNReal.ofReal A * ENNReal.ofReal K) v := by
    intro v
    by_cases hv : ‖v‖ ≤ ‖u‖
    · rw [Set.indicator_of_mem (by simpa using hv)]
      have e : ∀ y : ℂ, gm ε β m ![![u, x], ![v, y]] = A * kern ε β (y - v / u * x) := by
        intro y
        simp [gm, hv, hu, hAdef]
      simp_rw [e, ENNReal.ofReal_mul hA]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      rw [lintegral_sub_right_eq_self (fun z => ENNReal.ofReal (kern ε β z)) (v / u * x)]
      exact hker
    · have e : ∀ y : ℂ, gm ε β m ![![u, x], ![v, y]] = 0 := by
        intro y
        simp [gm, hv]
      simp [e]
  have hvol : volume (Metric.closedBall (0 : ℂ) ‖u‖) = ENNReal.ofReal (‖u‖ ^ 2 * Real.pi) := by
    rw [Complex.volume_closedBall, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow hr.le]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal]
    simp
  have hreal := real_bound ε ‖u‖ m hε hm hr
  have hkn := kern_nonneg ε 1 one_pos u
  have hfin : A * K * (‖u‖ ^ 2 * Real.pi) ≤
      β ^ (-ε) * Real.pi * K * kern ε 1 u * ((1 + ‖x‖) ^ m)⁻¹ := by
    have hc : 0 ≤ β ^ (-ε) * Real.pi * K * ((1 + ‖x‖) ^ m)⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_left hreal hc
    calc A * K * (‖u‖ ^ 2 * Real.pi)
        = β ^ (-ε) * Real.pi * K * ((1 + ‖x‖) ^ m)⁻¹ *
            (‖u‖ ^ (-4 + ε) * ((1 + ‖u‖) ^ m)⁻¹ * ‖u‖ ^ 2) := by rw [hAdef]; ring
      _ ≤ _ := this
      _ = _ := by unfold kern; ring
  calc ∫⁻ v : ℂ, ∫⁻ y : ℂ, ENNReal.ofReal (gm ε β m ![![u, x], ![v, y]])
      ≤ ∫⁻ v : ℂ, (Metric.closedBall (0 : ℂ) ‖u‖).indicator
        (fun _ => ENNReal.ofReal A * ENNReal.ofReal K) v := lintegral_mono h1
    _ = ENNReal.ofReal A * ENNReal.ofReal K * volume (Metric.closedBall (0 : ℂ) ‖u‖) :=
        lintegral_indicator_const Metric.isClosed_closedBall.measurableSet _
    _ = ENNReal.ofReal (A * K * (‖u‖ ^ 2 * Real.pi)) := by
        rw [hvol, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (mul_nonneg hA hK)]
    _ ≤ ENNReal.ofReal (β ^ (-ε) * Real.pi * K * kern ε 1 u * ((1 + ‖x‖) ^ m)⁻¹) :=
        ENNReal.ofReal_le_ofReal hfin
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]

theorem gm_integral_le : ∀ (ε K : ℝ) (m : ℕ), 0 < ε → 0 ≤ K →
    (∀ T₀ : ℝ, 0 < T₀ → ∫⁻ z : ℂ, ENNReal.ofReal (kern ε T₀ z) ≤ ENNReal.ofReal K) →
    3 ≤ m → 2 * ε ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 < β →
      ∫⁻ h : M22, ENNReal.ofReal (gm ε β m h) ≤ ENNReal.ofReal (C * β ^ (-ε)) := by
  intro ε K m hε hK hker hm3 hm
  have hQ := finite_Q m hm3
  set Q : ENNReal := ∫⁻ x : ℂ, ENNReal.ofReal (((1 + ‖x‖) ^ m)⁻¹) with hQdef
  refine ⟨Real.pi * K * K * Q.toReal, by positivity, fun β hβ => ?_⟩
  have hβε : 0 < β ^ (-ε) := Real.rpow_pos_of_pos hβ _
  have hmeas : Measurable fun h : M22 => ENNReal.ofReal (gm ε β m h) :=
    (measurable_gm ε β m).ennreal_ofReal
  have hf : Measurable fun u : ℂ =>
      ENNReal.ofReal (β ^ (-ε) * Real.pi * K) * ENNReal.ofReal (kern ε 1 u) :=
    ((measurable_kern ε 1).ennreal_ofReal).const_mul _
  have hg : Measurable fun x : ℂ => ENNReal.ofReal (((1 + ‖x‖) ^ m)⁻¹) := by
    refine Measurable.ennreal_ofReal ?_
    fun_prop
  rw [lint_rows _ hmeas]
  calc ∫⁻ a : ℂ × ℂ, ∫⁻ v : ℂ, ∫⁻ y : ℂ, ENNReal.ofReal (gm ε β m ![![a.1, a.2], ![v, y]])
      ≤ ∫⁻ a : ℂ × ℂ, (ENNReal.ofReal (β ^ (-ε) * Real.pi * K) * ENNReal.ofReal (kern ε 1 a.1)) *
          ENNReal.ofReal (((1 + ‖a.2‖) ^ m)⁻¹) :=
        lintegral_mono fun a => inner_le ε K β m hε hK hβ (hker β hβ) hm a.1 a.2
    _ = (∫⁻ u : ℂ, ENNReal.ofReal (β ^ (-ε) * Real.pi * K) * ENNReal.ofReal (kern ε 1 u)) * Q := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_mul hf.aemeasurable hg.aemeasurable
    _ ≤ (ENNReal.ofReal (β ^ (-ε) * Real.pi * K) * ENNReal.ofReal K) * Q := by
        rw [lintegral_const_mul _ (measurable_kern ε 1).ennreal_ofReal]
        gcongr
        exact hker 1 one_pos
    _ = ENNReal.ofReal (Real.pi * K * K * Q.toReal * β ^ (-ε)) := by
        have hQt : Q = ENNReal.ofReal Q.toReal := (ENNReal.ofReal_toReal hQ.ne).symm
        conv_lhs => rw [hQt]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end GlobalTheory.CompanionTheory.MajGm
end
end

section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_majorant_le_pow_neg : ∀ (ε K : ℝ) (m : ℕ), 0 < ε → 0 ≤ K → (∀ T₀ : ℝ, 0 < T₀ → ∫⁻ z : ℂ, ENNReal.ofReal (kern ε T₀ z) ≤ ENNReal.ofReal K) → 3 ≤ m → 2 * ε ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 < β → ∫⁻ h : M22, ENNReal.ofReal (gm ε β m h) ≤ ENNReal.ofReal (C * β ^ (-ε)) := by
  first | exact @GlobalTheory.CompanionTheory.MajGm.gm_integral_le | exact GlobalTheory.CompanionTheory.MajGm.gm_integral_le | (intros; apply GlobalTheory.CompanionTheory.MajGm.gm_integral_le <;> assumption)
end

section
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B

noncomputable section

namespace GlobalTheory.CompanionTheory.MajC

theorem measurable_M22_apply (i j : Fin 2) : Measurable (fun h : M22 => h i j) :=
  (measurable_pi_apply j).comp (measurable_pi_apply i)

theorem measurable_det_of_M22 : Measurable (fun h : M22 => (Matrix.of h).det) := by
  have h00 := measurable_M22_apply 0 0
  have h01 := measurable_M22_apply 0 1
  have h10 := measurable_M22_apply 1 0
  have h11 := measurable_M22_apply 1 1
  have : (fun h : M22 => (Matrix.of h).det) = fun h => h 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    funext h
    simp [Matrix.det_fin_two]
  rw [this]
  exact (h00.mul h11).sub (h01.mul h10)

theorem eta_eq_inv_det (h : M22) (j : Fin 2) :
    eta h j = ((Matrix.of h).det)⁻¹ * (![-h 1 0, h 0 0] j) := by
  unfold eta
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']
  fin_cases j <;> simp

theorem measurable_eta : Measurable eta := by
  refine measurable_pi_iff.2 fun j => ?_
  have : (fun h : M22 => eta h j) = fun h => ((Matrix.of h).det)⁻¹ * (![-h 1 0, h 0 0] j) := by
    funext h; exact eta_eq_inv_det h j
  rw [this]
  refine measurable_det_of_M22.inv.mul ?_
  fin_cases j
  · simpa using measurable_M22_apply 1 0
  · simpa using measurable_M22_apply 0 0

theorem measurable_jm_scaled (N : ℕ) (a b : ℂ) :
    Measurable (fun p : M22 × ℂ => (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ * jm N p.1 p.2 a b) := by
  have hd : Measurable (fun p : M22 × ℂ => ‖(Matrix.of p.1).det‖) :=
    (measurable_det_of_M22.comp measurable_fst).norm
  have he : Measurable (fun p : M22 × ℂ => ‖eta p.1‖) :=
    (measurable_eta.comp measurable_fst).norm
  have hh : Measurable (fun p : M22 × ℂ => ‖p.1‖) := measurable_fst.norm
  have ht : Measurable (fun p : M22 × ℂ => ‖p.2‖) := measurable_snd.norm
  unfold jm
  have c1 : Measurable (fun _ : M22 × ℂ => (1 : ℝ)) := measurable_const
  have ca : Measurable (fun _ : M22 × ℂ => ‖a‖) := measurable_const
  have cb : Measurable (fun _ : M22 × ℂ => ‖b‖) := measurable_const
  refine ((hd.pow_const 2).inv).mul ?_
  refine Measurable.mul (Measurable.mul (Measurable.mul (Measurable.mul ?_ ?_) ?_) ?_) ?_
  · exact (((hd.pow_const 2).mul (ht.pow_const 2)).mul (he.pow_const 2)).inv
  · exact ((c1.add hh).pow_const N).inv
  · exact ((c1.add (cb.mul he)).pow_const N).inv
  · exact ((ht.mul he).div (ca.add (ht.mul he))).pow_const N
  · exact ((c1.add (ht.div (hd.mul he))).pow_const N).inv

end GlobalTheory.CompanionTheory.MajC
end
end

open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_det_inv_mul_majorant : ∀ (N : ℕ) (a b : ℂ), Measurable (fun p : M22 × ℂ => (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ * jm N p.1 p.2 a b) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.MajC.measurable_jm_scaled
end

section
noncomputable section

open MeasureTheory Matrix Ad3.K.LC Ad3.K.LC.B

namespace GlobalTheory.CompanionTheory.MajC

theorem L_eta : ∀ h : M22, (Matrix.of h).det ≠ 0 → 0 < col h ∧ ‖eta h‖ = col h / dt h := by
  intro h hdet
  have hn : ∀ w : Fin 2 → ℂ, ‖w‖ = max ‖w 0‖ ‖w 1‖ := by
    intro w
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_)
      (max_le (norm_le_pi_norm w 0) (norm_le_pi_norm w 1))
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hD : 0 < dt h := norm_pos_iff.mpr hdet
  have he0 : eta h 0 = (Matrix.of h).det⁻¹ * (-h 1 0) := by
    simp [eta, Matrix.inv_def, Matrix.adjugate_fin_two]
  have he1 : eta h 1 = (Matrix.of h).det⁻¹ * h 0 0 := by
    simp [eta, Matrix.inv_def, Matrix.adjugate_fin_two]
  constructor
  · by_contra hc
    have hc0 : col h = 0 := le_antisymm (not_lt.mp hc) (le_max_of_le_left (norm_nonneg _))
    have h0 : h 0 0 = 0 := by
      have : ‖h 0 0‖ ≤ 0 := hc0 ▸ le_max_left _ _
      exact norm_le_zero_iff.mp this
    have h1 : h 1 0 = 0 := by
      have : ‖h 1 0‖ ≤ 0 := hc0 ▸ le_max_right _ _
      exact norm_le_zero_iff.mp this
    exact hdet (by simp [Matrix.det_fin_two, h0, h1])
  · rw [hn, he0, he1, norm_mul, norm_mul, norm_neg, norm_inv, ← mul_max_of_nonneg _ _ (by positivity), col, dt,
      max_comm]
    field_simp

theorem L_swp : ∀ f : M22 → ENNReal, ∫⁻ h : M22, f (swp h) = ∫⁻ h : M22, f h := by
  intro f
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Fin 2 → ℂ)
  have he : MeasurePreserving e volume volume := volume_preserving_piFinTwo _
  let s : M22 ≃ᵐ M22 := e.trans (MeasurableEquiv.prodComm.trans e.symm)
  have hs : MeasurePreserving s volume volume := by
    have hw : MeasurePreserving (Prod.swap : (Fin 2 → ℂ) × (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) volume volume :=
      Measure.measurePreserving_swap
    exact ((he.symm e).comp hw).comp he
  have hsw : ∀ h, s h = swp h := by
    intro h
    funext i
    fin_cases i <;> rfl
  have := hs.lintegral_comp_emb s.measurableEmbedding f
  simpa only [hsw] using this

theorem L_measgm : ∀ (ε β : ℝ) (m : ℕ), Measurable (gm ε β m) := by
  intro ε β m
  have h00 : Measurable fun h : M22 => h 0 0 := (measurable_pi_apply 0).comp (measurable_pi_apply 0)
  have h01 : Measurable fun h : M22 => h 0 1 := (measurable_pi_apply 1).comp (measurable_pi_apply 0)
  have h10 : Measurable fun h : M22 => h 1 0 := (measurable_pi_apply 0).comp (measurable_pi_apply 1)
  have h11 : Measurable fun h : M22 => h 1 1 := (measurable_pi_apply 1).comp (measurable_pi_apply 1)
  have hz : Measurable fun h : M22 => h 1 1 - h 1 0 / h 0 0 * h 0 1 :=
    h11.sub ((h10.div h00).mul h01)
  have hk : Measurable (kern ε β) := by
    unfold kern
    fun_prop
  have hset : MeasurableSet {h : M22 | ‖h 1 0‖ ≤ ‖h 0 0‖ ∧ h 0 0 ≠ 0} :=
    (measurableSet_le h10.norm h00.norm).inter (h00 (measurableSet_singleton 0).compl)
  unfold gm
  refine Measurable.ite hset ?_ measurable_const
  have := hk.comp hz
  simp only [Function.comp_def] at this
  exact ((((measurable_const.mul (h00.norm.pow_const _)).mul
    ((measurable_const.add h00.norm).pow_const m).inv).mul
    ((measurable_const.add h01.norm).pow_const m).inv).mul this)

theorem hm_int (ε : ℝ) (hε : 0 < ε) (m : ℕ) (h3 : 3 ≤ m) (hm2 : 2 * ε ≤ m) (K : ℝ) (hK : 0 ≤ K)
    (hk : ∀ T₀ : ℝ, 0 < T₀ → ∫⁻ z : ℂ, ENNReal.ofReal (kern ε T₀ z) ≤ ENNReal.ofReal K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 * m ≤ N → ∀ β : ℝ, 0 < β →
      ∫⁻ h : M22, ENNReal.ofReal (hm ε N β h) ≤ ENNReal.ofReal (C * β ^ (-ε)) := by
  obtain ⟨C, hC, hg⟩ := GlobalTheory.T.lintegral_majorant_le_pow_neg ε K m hε hK hk h3 hm2
  refine ⟨2 * C, by positivity, fun N hN β hβ => ?_⟩
  have hg0 : ∀ h, 0 ≤ gm ε β m h := by
    intro h
    unfold gm
    split_ifs
    · unfold kern
      positivity
    · exact le_rfl
  have hmeas : Measurable (gm ε β m) := L_measgm ε β m
  calc ∫⁻ h : M22, ENNReal.ofReal (hm ε N β h)
      ≤ ∫⁻ h : M22, (ENNReal.ofReal (gm ε β m h) + ENNReal.ofReal (gm ε β m (swp h))) := by
        refine lintegral_mono fun h => ?_
        rw [← ENNReal.ofReal_add (hg0 _) (hg0 _)]
        exact ENNReal.ofReal_le_ofReal (GlobalTheory.T.majorant_le_sum_swap ε β m N hε hβ hm2 hN h)
    _ = (∫⁻ h : M22, ENNReal.ofReal (gm ε β m h)) + ∫⁻ h : M22, ENNReal.ofReal (gm ε β m (swp h)) :=
        lintegral_add_left hmeas.ennreal_ofReal _
    _ = (∫⁻ h : M22, ENNReal.ofReal (gm ε β m h)) + ∫⁻ h : M22, ENNReal.ofReal (gm ε β m h) := by
        rw [L_swp (fun h => ENNReal.ofReal (gm ε β m h))]
    _ ≤ ENNReal.ofReal (C * β ^ (-ε)) + ENNReal.ofReal (C * β ^ (-ε)) := add_le_add (hg β hβ) (hg β hβ)
    _ = ENNReal.ofReal (2 * C * β ^ (-ε)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

theorem main : Ad3.K.LC.B.MajScaled := by
  intro ε hε
  obtain ⟨K1, hK1, hk1⟩ := GlobalTheory.T.lintegral_kernel_uniform_bound ε hε
  obtain ⟨K2, hK2, hk2⟩ := GlobalTheory.T.lintegral_kernel_uniform_bound (2 * ε) (by positivity)
  set m : ℕ := max 3 ⌈2 * ε⌉₊ with hmdef
  have h3 : 3 ≤ m := le_max_left _ _
  have hm2 : 2 * ε ≤ m := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  obtain ⟨C, hC, hH⟩ := hm_int ε hε m h3 hm2 K1 hK1 hk1
  refine ⟨2 * m, fun N hN => ⟨K2 * C, fun a b ha hb => ?_⟩⟩
  have hNε : 2 * ε ≤ N := by
    have : (2 * m : ℝ) ≤ N := by exact_mod_cast hN
    have h0 : (0 : ℝ) ≤ m := by positivity
    linarith
  have hA : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hB : 0 < ‖b‖ := norm_pos_iff.mpr hb
  set f : M22 × ℂ → ℝ := fun p => (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ * jm N p.1 p.2 a b with hf
  have hfm : Measurable f := GlobalTheory.T.measurable_det_inv_mul_majorant N a b
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    simp only [hf, jm]
    positivity
  have hper : ∀ h : M22, ∫⁻ t : ℂ, ENNReal.ofReal (f (h, t)) ≤
      ENNReal.ofReal (K2 * ‖a‖ ^ (-ε)) * ENNReal.ofReal (hm ε N ‖b‖ h) := by
    intro h
    by_cases hdet : (Matrix.of h).det = 0
    · simp [hf, hdet]
    have hD : 0 < dt h := norm_pos_iff.mpr hdet
    obtain ⟨hc, hE⟩ := L_eta h hdet
    have hE0 : 0 < ‖eta h‖ := by rw [hE]; positivity
    have hfe : ∀ t : ℂ, ENNReal.ofReal (f (h, t)) =
        ENNReal.ofReal ((dt h ^ 2)⁻¹) * ENNReal.ofReal (jm N h t a b) := by
      intro t
      rw [← ENNReal.ofReal_mul (by positivity)]
      rfl
    simp_rw [hfe]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_right (GlobalTheory.T.lintegral_majorant_fiber_bound ε K2 hε hK2 hk2 N hNε h a b ha hD hE0) _).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hpow : (dt h ^ 2)⁻¹ * dt h ^ (-2 + ε) * ‖eta h‖ ^ (-2 + 2 * ε) =
        dt h ^ (-(2 + ε)) * col h ^ (-2 + 2 * ε) := by
      rw [hE, Real.div_rpow hc.le hD.le, Real.rpow_add hD, Real.rpow_neg hD.le (2 + ε), Real.rpow_add hD,
        Real.rpow_add hD, two_mul ε, Real.rpow_add hD ε ε, Real.rpow_neg hD.le 2, Real.rpow_two]
      have hP := Real.rpow_pos_of_pos hD ε
      field_simp
    simp only [hm]
    rw [← hE]
    calc _ = K2 * ‖a‖ ^ (-ε) * ((dt h ^ 2)⁻¹ * dt h ^ (-2 + ε) * ‖eta h‖ ^ (-2 + 2 * ε)) * ((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹ := by ring
      _ = _ := by rw [hpow]; ring
  have hlin : ∫⁻ p, ENNReal.ofReal (f p) ≤ ENNReal.ofReal (K2 * C * (‖a‖ * ‖b‖) ^ (-ε)) := by
    rw [Measure.volume_eq_prod, lintegral_prod _ hfm.ennreal_ofReal.aemeasurable]
    calc ∫⁻ h : M22, ∫⁻ t : ℂ, ENNReal.ofReal (f (h, t))
        ≤ ∫⁻ h : M22, ENNReal.ofReal (K2 * ‖a‖ ^ (-ε)) * ENNReal.ofReal (hm ε N ‖b‖ h) :=
          lintegral_mono hper
      _ = ENNReal.ofReal (K2 * ‖a‖ ^ (-ε)) * ∫⁻ h : M22, ENNReal.ofReal (hm ε N ‖b‖ h) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (K2 * ‖a‖ ^ (-ε)) * ENNReal.ofReal (C * ‖b‖ ^ (-ε)) :=
          mul_le_mul_right (hH N hN ‖b‖ hB) _
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), Real.mul_rpow hA.le hB.le]
          congr 1
          ring
  have hint : Integrable f := by
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0)]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin

end GlobalTheory.CompanionTheory.MajC
end
end
