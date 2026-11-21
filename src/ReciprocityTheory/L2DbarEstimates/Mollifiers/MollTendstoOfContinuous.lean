import ReciprocityTheory.L2DbarEstimates.Mollifiers.HasCompactSupport

section
namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

theorem Kernel.lintegral_ofReal (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) :
    ∫⁻ t, ENNReal.ofReal (K.toFun t) ∂μ = 1 := by
  have hint : Integrable K.toFun μ :=
    Integrable.of_integral_ne_zero (by rw [K.integral_eq_one]; exact one_ne_zero)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall K.nonneg),
    K.integral_eq_one, ENNReal.ofReal_one]

theorem moll_enorm_sq_le (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) {u : E → ℂ} (hu : AEStronglyMeasurable u μ)
    (x : E) :
    ‖moll K u x‖ₑ ^ 2 ≤ ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 ∂μ := by
  have hK0 := K.nonneg
  have hKm : Measurable K.toFun := K.smooth.continuous.measurable
  have h1 : ‖moll K u x‖ₑ ≤ ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ∂μ := by
    have hmoll : moll K u x = ∫ t, K.toFun t • u (x - t) ∂μ := rfl
    rw [hmoll]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun t => ?_
    rw [enorm_smul, Real.enorm_of_nonneg (hK0 t)]
  have hum : AEMeasurable (fun t => ‖u (x - t)‖ₑ) μ :=
    (hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x)).enorm
  set f : E → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.sqrt (K.toFun t)) with hfdef
  set g : E → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.sqrt (K.toFun t)) * ‖u (x - t)‖ₑ with hgdef
  have hf : AEMeasurable f μ := hKm.sqrt.ennreal_ofReal.aemeasurable
  have hg : AEMeasurable g μ := hf.mul hum
  have r2 : ∀ z : ℝ≥0∞, z ^ (2 : ℝ) = z ^ 2 := fun z => by
    rw [← ENNReal.rpow_natCast]; norm_num
  have hsq : ∀ t, ENNReal.ofReal (Real.sqrt (K.toFun t)) ^ 2 = ENNReal.ofReal (K.toFun t) := by
    intro t
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hK0 t)]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have e1 : ∫⁻ t, (f * g) t ∂μ = ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ∂μ := by
    refine lintegral_congr fun t => ?_
    simp only [Pi.mul_apply, hfdef, hgdef]
    rw [← mul_assoc, ← pow_two, hsq]
  have e2 : ∫⁻ t, f t ^ (2 : ℝ) ∂μ = 1 := by
    rw [← Kernel.lintegral_ofReal E μ K]
    refine lintegral_congr fun t => ?_
    simp only [hfdef]
    rw [r2, hsq]
  have e3 : ∫⁻ t, g t ^ (2 : ℝ) ∂μ = ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 ∂μ := by
    refine lintegral_congr fun t => ?_
    simp only [hgdef]
    rw [r2, mul_pow, hsq]
  rw [e1, e2, e3, ENNReal.one_rpow, one_mul] at hH
  calc ‖moll K u x‖ₑ ^ 2
      ≤ ((∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (h1.trans hH) 2
    _ = ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 ∂μ := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

theorem moll_young_sq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) (u : E → ℂ) (s : Set E) (hs : MeasurableSet s)
    (hu : AEStronglyMeasurable u μ) :
    ∫⁻ x in s, ‖moll K u x‖ₑ ^ 2 ∂μ ≤ ∫⁻ y in thickening K.r s, ‖u y‖ₑ ^ 2 ∂μ := by
  set T := thickening K.r s with hTdef
  have hT : MeasurableSet T := isOpen_thickening.measurableSet
  have hKm : Measurable K.toFun := K.smooth.continuous.measurable
  set F : E → E → ℝ≥0∞ := fun x t => ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 with hFdef
  have hF : AEMeasurable (Function.uncurry F) ((μ.restrict s).prod μ) := by
    have hq := hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ)
    have hF0 : AEMeasurable (Function.uncurry F) (μ.prod μ) :=
      (hKm.comp measurable_snd).ennreal_ofReal.aemeasurable.mul (hq.enorm.pow_const 2)
    exact hF0.mono_ac (Measure.restrict_le_self.absolutelyContinuous.prod
      (Measure.AbsolutelyContinuous.refl μ))
  have htrans : ∀ t, ∫⁻ x in (fun x => x - t) ⁻¹' T, ‖u (x - t)‖ₑ ^ 2 ∂μ =
      ∫⁻ y in T, ‖u y‖ₑ ^ 2 ∂μ := by
    intro t
    rw [← lintegral_indicator (hT.preimage (measurable_sub_const t)), ← lintegral_indicator hT,
      ← lintegral_sub_right_eq_self (T.indicator fun y => ‖u y‖ₑ ^ 2) t]
    refine lintegral_congr fun x => ?_
    first
    | rfl
    | (by_cases hx : x - t ∈ T <;> simp [Set.indicator_apply, hx])
  have hpt : ∀ t, ∫⁻ x in s, F x t ∂μ ≤ ENNReal.ofReal (K.toFun t) * ∫⁻ y in T, ‖u y‖ₑ ^ 2 ∂μ := by
    intro t
    simp only [hFdef]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    by_cases h0 : K.toFun t = 0
    · simp [h0]
    · have ht : t ∈ ball (0 : E) K.r := K.support_subset h0
      refine mul_le_mul' le_rfl ?_
      rw [← htrans t]
      refine lintegral_mono_set fun x hx => ?_
      simp only [Set.mem_preimage, hTdef]
      refine mem_thickening_iff.mpr ⟨x, hx, ?_⟩
      rw [mem_ball_zero_iff] at ht
      simpa [dist_eq_norm] using ht
  calc ∫⁻ x in s, ‖moll K u x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in s, ∫⁻ t, F x t ∂μ ∂μ :=
        lintegral_mono fun x => moll_enorm_sq_le E μ K hu x
    _ = ∫⁻ t, ∫⁻ x in s, F x t ∂μ ∂μ := lintegral_lintegral_swap hF
    _ ≤ ∫⁻ t, ENNReal.ofReal (K.toFun t) * ∫⁻ y in T, ‖u y‖ₑ ^ 2 ∂μ ∂μ := lintegral_mono hpt
    _ = ∫⁻ y in T, ‖u y‖ₑ ^ 2 ∂μ := by
        rw [lintegral_mul_const _ hKm.ennreal_ofReal, Kernel.lintegral_ofReal E μ K, one_mul]

theorem moll_young (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : YoungSt E μ := by
  intro K u s hs hu
  have h := moll_young_sq E μ K u s hs hu
  have e : ∀ z : ℝ≥0∞, z ^ (ENNReal.toReal 2) = z ^ 2 := fun z => by
    rw [ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast]; norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  simp_rw [e]
  exact ENNReal.rpow_le_rpow h (by norm_num)


end ReciprocityTheory.L2DbarEstimates.B
end

section
namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

theorem moll_tendsto_of_continuous (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {ι : Type*} {l : Filter ι} {K : ι → Kernel E μ}
    (hK : Tendsto (fun i => (K i).r) l (𝓝 0)) {g : E → ℂ} (hgs : HasCompactSupport g)
    (hgc : Continuous g) : Tendsto (fun i => eLpNorm (moll (K i) g - g) 2 μ) l (𝓝 0) := by
  have hgu : UniformContinuous g := hgs.uniformContinuous_of_continuous hgc
  set S := Metric.cthickening 1 (tsupport g) with hS
  have hSc : IsCompact S := hgs.isCompact.cthickening
  set C := μ S ^ ((2 : ℝ≥0∞).toReal⁻¹) with hC
  have hCfin : C ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hSc.measure_lt_top.ne
  have hgm : AEStronglyMeasurable g μ := hgc.aestronglyMeasurable
  have key : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in l, eLpNorm (moll (K i) g - g) 2 μ ≤ C * ENNReal.ofReal δ := by
    intro δ hδ
    obtain ⟨ρ, hρ, hρg⟩ := Metric.uniformContinuous_iff.1 hgu δ hδ
    filter_upwards [hK.eventually (gt_mem_nhds (lt_min hρ one_pos))] with i hi
    have hr : (K i).r < ρ := lt_of_lt_of_le hi (min_le_left _ _)
    have hr1 : (K i).r < 1 := lt_of_lt_of_le hi (min_le_right _ _)
    have hbound : ∀ x, ‖(moll (K i) g - g) x‖ ≤ δ := by
      intro x
      rw [Pi.sub_apply, ← dist_eq_norm]
      simp only [moll]
      exact dist_convolution_le hδ.le (K i).support_subset (K i).nonneg (K i).integral_eq_one hgm
        (fun y hy => (hρg (lt_trans (mem_ball.1 hy) hr)).le)
    have hsupp : Function.support (moll (K i) g - g) ⊆ S := by
      intro x hx
      by_contra hxS
      apply hx
      have hx0 : ∀ y ∈ ball x (K i).r, g y = 0 := by
        intro y hy
        by_contra hy0
        apply hxS
        refine Metric.mem_cthickening_of_dist_le x y 1 _ (subset_tsupport _ hy0) ?_
        rw [dist_comm]; exact le_of_lt (lt_trans (mem_ball.1 hy) hr1)
      have hgx : g x = 0 := hx0 x (mem_ball_self (K i).r_pos)
      have h0 : dist (moll (K i) g x) (0 : ℂ) ≤ 0 := by
        simp only [moll]
        exact dist_convolution_le le_rfl (K i).support_subset (K i).nonneg (K i).integral_eq_one hgm
          (fun y hy => by rw [hx0 y hy, dist_self])
      rw [Pi.sub_apply, hgx, sub_zero]
      exact dist_le_zero.1 h0
    rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
    refine (eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall hbound)).trans ?_
    rw [Measure.restrict_apply_univ]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨n, hn, hnε⟩ := ENNReal.exists_nnreal_pos_mul_lt hCfin hε.ne'
  filter_upwards [key n (NNReal.coe_pos.2 hn)] with i hi
  refine hi.trans ?_
  rw [ENNReal.ofReal_coe_nnreal, mul_comm]
  exact hnε.le

theorem moll_l2Tendsto (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (ι : Type*) : MollifierL2Tendsto E μ ι := by
  intro l K hK u hu
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hη : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' (by simp)).ne'
  obtain ⟨g, hgs, hug, hgc, hgL⟩ := hu.exists_hasCompactSupport_eLpNorm_sub_le (by simp) hη
  have hmid := moll_tendsto_of_continuous E μ hK hgs hgc
  rw [ENNReal.tendsto_nhds_zero] at hmid
  filter_upwards [hmid (ε / 3) (pos_iff_ne_zero.2 hη)] with i hi
  have hcs : HasCompactSupport (K i).toFun :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) (K i).r) (fun x hx => by
      by_contra h
      exact hx (ball_subset_closedBall ((K i).support_subset h)))
  have hKc : Continuous (K i).toFun := (K i).smooth.continuous
  have hug' : MemLp (u - g) 2 μ := hu.sub hgL
  have hli : LocallyIntegrable (u - g) μ := hug'.locallyIntegrable (by norm_num)
  have hgli : LocallyIntegrable g μ := hgL.locallyIntegrable (by norm_num)
  have hlin : moll (K i) u = moll (K i) (u - g) + moll (K i) g := by
    simp only [moll]
    rw [← ConvolutionExists.distrib_add (hcs.convolutionExists_left _ hKc hli)
      (hcs.convolutionExists_left _ hKc hgli), sub_add_cancel]
  have hc1 : Continuous (moll (K i) (u - g)) := hcs.continuous_convolution_left _ hKc hli
  have hc2 : Continuous (moll (K i) g) := hcs.continuous_convolution_left _ hKc hgli
  have hdec : moll (K i) u - u = moll (K i) (u - g) + (moll (K i) g - g) + (g - u) := by
    rw [hlin]; abel
  have hY : eLpNorm (moll (K i) (u - g)) 2 μ ≤ eLpNorm (u - g) 2 μ := by
    have h := moll_young E μ (K i) (u - g) Set.univ MeasurableSet.univ hug'.aestronglyMeasurable
    have hth : thickening (K i).r (Set.univ : Set E) = Set.univ :=
      Set.eq_univ_of_forall fun x => Metric.self_subset_thickening (K i).r_pos _ (Set.mem_univ x)
    simp only [hth, Measure.restrict_univ] at h
    exact h
  rw [hdec]
  calc eLpNorm (moll (K i) (u - g) + (moll (K i) g - g) + (g - u)) 2 μ
      ≤ eLpNorm (moll (K i) (u - g) + (moll (K i) g - g)) 2 μ + eLpNorm (g - u) 2 μ :=
        eLpNorm_add_le (hc1.aestronglyMeasurable.add (hc2.aestronglyMeasurable.sub hgc.aestronglyMeasurable))
          (hgc.aestronglyMeasurable.sub hu.aestronglyMeasurable) (by norm_num)
    _ ≤ eLpNorm (moll (K i) (u - g)) 2 μ + eLpNorm (moll (K i) g - g) 2 μ + eLpNorm (g - u) 2 μ := by
        gcongr
        exact eLpNorm_add_le hc1.aestronglyMeasurable
          (hc2.aestronglyMeasurable.sub hgc.aestronglyMeasurable) (by norm_num)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact hY.trans hug
        · rw [eLpNorm_sub_comm]; exact hug
    _ = ε := ENNReal.add_thirds ε

end ReciprocityTheory.L2DbarEstimates.B
end
