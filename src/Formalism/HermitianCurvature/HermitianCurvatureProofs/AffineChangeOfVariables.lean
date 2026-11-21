import Formalism.HermitianCurvature.StatementG

open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace Formalism.FourierDecayAlt.P.G3

theorem map_mul_vol (α : ℂ) (hα : α ≠ 0) :
    Measure.map (fun ρ : ℂ => α * ρ) (volume : Measure ℂ) = ENNReal.ofReal ((‖α‖ ^ 2)⁻¹) • volume := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ α) = ‖α‖ ^ 2 := by
    have h1 := Algebra.norm_complex_apply α
    rw [Algebra.norm_apply] at h1
    rw [← Complex.normSq_eq_norm_sq, ← h1]
    rfl
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := LinearMap.mulLeft ℝ α) (by rw [hdet]; positivity)
  rw [hdet, abs_of_nonneg (by positivity)] at h
  exact h

theorem integral_comp_mul (α : ℂ) (hα : α ≠ 0) (G : ℂ → ℂ) :
    ∫ ξ : ℂ, G (α * ξ) = ((‖α‖ ^ 2)⁻¹ : ℝ) • ∫ η : ℂ, G η := by
  have h := map_mul_vol α hα
  have he : MeasurableEmbedding (fun ρ : ℂ => α * ρ) :=
    (Homeomorph.mulLeft₀ α hα).measurableEmbedding
  rw [← he.integral_map, h, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]


noncomputable def al (β : ℂ) : ℂ := -((starRingEnd ℂ) β) * (((2 * Real.pi)⁻¹ : ℝ) : ℂ)

theorem norm_al (β : ℂ) : ‖al β‖ = ‖β‖ / (2 * Real.pi) := by
  unfold al
  rw [norm_mul, norm_neg, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rfl

theorem phase1 (β ξ v : ℂ) :
    -2 * Real.pi * ⟪v, al β * (starRingEnd ℂ) ξ⟫ = (β * (ξ * v)).re := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [Complex.inner]
  unfold al
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
  field_simp
  ring

theorem phase2 (β ξ w : ℂ) :
    2 * Real.pi * ⟪al β * (starRingEnd ℂ) ξ, -w⟫ = (β * (w * ξ)).re := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [Complex.inner]
  unfold al
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, map_mul, map_neg, Complex.conj_conj,
    Complex.conj_ofReal]
  field_simp
  ring

theorem inner_int (β ξ : ℂ) (f : ℂ → ℂ) :
    ∫ x : ℂ, f x * psi β (ξ * x) = 𝓕 f (al β * (starRingEnd ℂ) ξ) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [phase1, psi, smul_eq_mul]
  rw [mul_comm (f x), mul_comm Complex.I]



theorem exists_schwartz : ∃ f : SchwartzMap ℂ ℂ, f 0 = 1 := by
  let b : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x : ℂ => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℂ => ((b x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨h1.toSchwartzMap h2, ?_⟩
  have : b 0 = 1 := b.one_of_mem_closedBall (by simpa using b.rIn_pos.le)
  simp [this]

theorem wMat_mul_self (d : ℕ) : wMat d * wMat d = 1 := by
  ext i j
  have key : ∀ k : Fin d, (if k = i.rev then (1:ℂ) else 0) * (if j = k.rev then (1:ℂ) else 0) =
      if k = i.rev then (if i = j then 1 else 0) else 0 := by
    intro k
    by_cases hk : k = i.rev
    · simp [hk, eq_comm]
    · simp [hk]
  simp only [wMat, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply, key]
  simp

theorem wMat_det_ne (d : ℕ) : (wMat d).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (wMat_mul_self d)
  simp [Matrix.det_mul, h] at this

theorem cont_detM (s : ℕ) : Continuous (detM : Mat s → ℂ) := by
  unfold detM
  exact Continuous.matrix_det (A := fun Z : Mat s => Matrix.of Z) continuous_id

theorem aux (a R : ℝ) (ha : 0 ≤ a) (h : a ≤ R) : a ≤ max 1 R * min 1 a := by
  rcases le_total a 1 with h1 | h1
  · rw [min_eq_right h1]
    nlinarith [le_max_left 1 R]
  · rw [min_eq_left h1]
    simpa using h.trans (le_max_right 1 R)

instance (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance

end Formalism.FourierDecayAlt.P.G3

namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.G3



theorem affine_change_of_variables : Formalism.FourierDecayAlt.G.AffineChange := by
  intro β α γ hα
  have h1 : (fun ρ : ℂ => α * ρ + γ) = (fun x => x + γ) ∘ (fun ρ : ℂ => α * ρ) := rfl
  unfold mu
  rw [Measure.map_smul, h1, ← Measure.map_map (measurable_add_const γ) (measurable_const_mul α),
    map_mul_vol α hα, Measure.map_smul, map_add_right_eq_self]
  rw [smul_comm]
  congr 1

theorem scale_product_measure : Formalism.FourierDecayAlt.G.ScalePi := by
  intro β z ι _ hz
  unfold muPi
  have hA := affine_change_of_variables β z 0 hz
  simp only [add_zero] at hA
  have hfun : (fun v : ι → ℂ => z • v) = fun v i => z * v i := by
    ext v i; simp
  have hc : Real.toNNReal ((‖z‖ ^ (2 * Fintype.card ι))⁻¹) =
      (Real.toNNReal ((‖z‖ ^ 2)⁻¹)) ^ Fintype.card ι := by
    rw [← Real.toNNReal_pow (by positivity), inv_pow, pow_mul]
  have hsf : SigmaFinite (Measure.map (fun ρ : ℂ => z * ρ) (mu β)) := by
    rw [hA]; infer_instance
  rw [hfun, Measure.pi_map_pi (fun _ => (measurable_const_mul z).aemeasurable)]
  simp only [hA]
  refine Measure.pi_eq fun s hs => ?_
  rw [hc]
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

theorem germ_of_rate : Formalism.FourierDecayAlt.G.GermOfRate := by
  rintro ⟨C₁, C₂, h⟩
  refine ⟨max C₁ C₂, fun m β hβ => ⟨fun _ => 1, by simp, ?_⟩⟩
  intro A hA Kc hKc h0 K ε hε
  obtain ⟨Cst, hC⟩ := h m β hβ Kc hKc h0
  obtain ⟨d0, hd0, hd⟩ : ∃ d0 : ℝ, 0 < d0 ∧ ∀ D ∈ Kc, d0 ≤ ‖D‖ := by
    rcases Kc.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_pos, by simp⟩
    · obtain ⟨D0, hD0, hmin⟩ := hKc.exists_isMinOn hne continuous_norm.continuousOn
      exact ⟨‖D0‖, norm_pos_iff.mpr (fun h => h0 (h ▸ hD0)), fun D hD => hmin hD⟩
  have hw : 0 < ‖(wMat (m + 1)).det‖ := norm_pos_iff.mpr (wMat_det_ne _)
  obtain ⟨r0, hr0, hr⟩ : ∃ r0 : ℝ, 0 < r0 ∧ ∀ Z : Mat (m + 1 + 1), detM Z ∈ detSet (m + 1) Kc → r0 ≤ ‖Z‖ := by
    have hc := (cont_detM (m + 1 + 1)).continuousAt (x := 0)
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨r, hrpos, hr⟩ := hc (‖(wMat (m + 1)).det‖ * d0) (mul_pos hw hd0)
    refine ⟨r, hrpos, fun Z hZ => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have h1 := hr (x := Z) (by simpa [dist_eq_norm] using hlt)
    have h00 : detM (0 : Mat (m + 1 + 1)) = 0 := by
      unfold detM
      exact Matrix.det_zero
    rw [h00, dist_eq_norm, sub_zero] at h1
    obtain ⟨D, hD, hDe⟩ := hZ
    rw [← hDe, norm_mul] at h1
    have := hd D hD
    nlinarith
  have hs : (1 : ℝ) ≤ (m : ℝ) + 2 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hmax1 : (C₁ : ℝ) ≤ ((max C₁ C₂ : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
  have hC1nn : (0 : ℝ) ≤ (C₁ : ℝ) := Nat.cast_nonneg _
  have hA1 : (C₁ : ℝ) * ((m : ℝ) + 2) ^ 2 ≤ A := by
    refine le_trans ?_ hA
    have h2 : ((m : ℝ) + 2) ^ 2 ≤ ((m : ℝ) + 2) ^ 3 := pow_le_pow_right₀ hs (by norm_num)
    have h3 : (0 : ℝ) ≤ ((m : ℝ) + 2) ^ 2 := by positivity
    nlinarith
  have hA0 : 0 ≤ A := le_trans (by positivity) hA1
  set Mx : ℝ := max 1 (r0 ^ (-A)) with hMx
  have hMx0 : 0 < Mx := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨ε / (|Cst| * (|K| * Mx) + 1), by positivity, ?_⟩
  intro V _ _ _ Φ hΦ t c ht htδ hD
  have hb : DerivBound (max C₁ C₂ * (m + 2) ^ 2) (detSet (m + 1) Kc)
      (fun Z => (|K| * Mx) * min 1 (‖Z‖ ^ (-A))) Φ := by
    intro Z hZ
    obtain ⟨h1, h2⟩ := hΦ Z hZ
    refine ⟨h1, fun j hj => (h2 j hj).trans ?_⟩
    have hZr := hr Z hZ
    have ha0 : 0 ≤ ‖Z‖ ^ (-A) := Real.rpow_nonneg (norm_nonneg _) _
    have ha1 : ‖Z‖ ^ (-A) ≤ r0 ^ (-A) := Real.rpow_le_rpow_of_nonpos hr0 hZr (by linarith)
    have h3 := aux _ _ ha0 ha1
    calc K * ‖Z‖ ^ (-A) ≤ |K| * ‖Z‖ ^ (-A) := mul_le_mul_of_nonneg_right (le_abs_self K) ha0
      _ ≤ |K| * (Mx * min 1 (‖Z‖ ^ (-A))) := mul_le_mul_of_nonneg_left h3 (abs_nonneg K)
      _ = (|K| * Mx) * min 1 (‖Z‖ ^ (-A)) := by ring
  have := hC V Φ A (|K| * Mx) (max C₁ C₂ * (m + 2) ^ 2) hA1
    (Nat.mul_le_mul_right _ (le_max_right _ _)) hb t c ht hD
  refine this.trans ?_
  have hq : 0 ≤ |Cst| * (|K| * Mx) := by positivity
  have h5 : Cst * (|K| * Mx) * ‖t‖ ≤ |Cst| * (|K| * Mx) * ‖t‖ := by
    have : Cst * (|K| * Mx) ≤ |Cst| * (|K| * Mx) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  refine h5.trans ?_
  rw [lt_div_iff₀ (by positivity)] at htδ
  nlinarith [norm_nonneg t]

end Formalism.FourierDecayAlt.P
