import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic

section
namespace ReciprocityTheory.AnForm.A

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Convolution

noncomputable section

variable {D : ℕ}

lemma finrank_fin_complex : Module.finrank ℝ (Fin D → ℂ) = 2 * D := by
  rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex, mul_comm]

section Scaled

variable (ρ : Mollifier D)

lemma scaled_nonneg {ε : ℝ} (hε : 0 < ε) (w : Fin D → ℂ) : 0 ≤ ρ.scaled ε w :=
  mul_nonneg (inv_nonneg.2 (pow_nonneg hε.le _)) (ρ.nonneg _)

lemma scaled_eq_zero {ε : ℝ} (hε : 0 < ε) {w : Fin D → ℂ} (hw : ε ≤ ‖w‖) :
    ρ.scaled ε w = 0 := by
  have : ρ.toFun (ε⁻¹ • w) = 0 := by
    by_contra h
    have h1 := ρ.support_subset h
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε)] at h1
    have h2 : ε⁻¹ * ε ≤ ε⁻¹ * ‖w‖ := mul_le_mul_of_nonneg_left hw (inv_pos.2 hε).le
    rw [inv_mul_cancel₀ hε.ne'] at h2
    linarith
  simp [Mollifier.scaled, this]

lemma norm_lt_of_scaled_ne_zero {ε : ℝ} (hε : 0 < ε) {w : Fin D → ℂ} (hw : ρ.scaled ε w ≠ 0) :
    ‖w‖ < ε :=
  lt_of_not_ge fun h => hw (scaled_eq_zero ρ hε h)

lemma scaled_contDiff (ε : ℝ) : ContDiff ℝ ∞ (ρ.scaled ε) :=
  contDiff_const.mul (ρ.contDiff.comp (contDiff_id.const_smul ε⁻¹))

lemma scaled_hasCompactSupport {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (ρ.scaled ε) :=
  HasCompactSupport.intro (isCompact_closedBall 0 ε) fun _ hw =>
    scaled_eq_zero ρ hε (le_of_lt (not_le.1 fun h => hw (mem_closedBall_zero_iff.2 h)))

lemma integral_scaled {ε : ℝ} (hε : 0 < ε) : ∫ w, ρ.scaled ε w = 1 := by
  simp only [Mollifier.scaled]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume ρ.toFun hε.le,
    finrank_fin_complex, ρ.integral_eq_one, smul_eq_mul, mul_one,
    inv_mul_cancel₀ (pow_pos hε _).ne']

lemma integrable_scaled {ε : ℝ} (hε : 0 < ε) : Integrable (ρ.scaled ε) :=
  (scaled_contDiff ρ ε).continuous.integrable_of_hasCompactSupport (scaled_hasCompactSupport ρ hε)

lemma molli_congr {ε : ℝ} (hε : 0 < ε) {U : Set (Fin D → ℂ)} {φ ψ : (Fin D → ℂ) → ℝ}
    {z : Fin D → ℂ} (hz : z ∈ shrink U ε) (h : EqOn φ ψ U) :
    molli ρ ε φ z = molli ρ ε ψ z := by
  unfold molli
  congr 1
  funext w
  by_cases hw : ρ.scaled ε w = 0
  · simp [hw]
  · rw [h (hz ?_)]
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]
    exact (norm_lt_of_scaled_ne_zero ρ hε hw).le

lemma conv_lip {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ε : ℝ} (hε : 0 < ε) {g : (Fin D → ℂ) → F} {L : NNReal} (hg : LipschitzWith L g)
    (z : Fin D → ℂ) : ‖(∫ w, ρ.scaled ε w • g (z - w)) - g z‖ ≤ L * ε := by
  have hc : Continuous fun w => ρ.scaled ε w • g (z - w) :=
    (scaled_contDiff ρ ε).continuous.smul (hg.continuous.comp (continuous_const.sub continuous_id))
  have hi : Integrable fun w => ρ.scaled ε w • g (z - w) :=
    hc.integrable_of_hasCompactSupport (scaled_hasCompactSupport ρ hε).smul_right
  have hi2 : Integrable fun w => ρ.scaled ε w • g z := (integrable_scaled ρ hε).smul_const _
  have e1 : g z = ∫ w, ρ.scaled ε w • g z := by
    rw [integral_smul_const, integral_scaled ρ hε, one_smul]
  rw [e1, ← integral_sub hi hi2]
  have hb : Integrable fun w => ρ.scaled ε w * (L * ε) := (integrable_scaled ρ hε).mul_const _
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun w => ?_)).trans ?_
  · rw [← smul_sub, norm_smul, Real.norm_of_nonneg (scaled_nonneg ρ hε w)]
    by_cases hw : ρ.scaled ε w = 0
    · simp [hw]
    · refine mul_le_mul_of_nonneg_left ?_ (scaled_nonneg ρ hε w)
      have h1 := hg.dist_le_mul (z - w) z
      rw [dist_eq_norm, dist_eq_norm, sub_sub_cancel_left, norm_neg] at h1
      calc ‖g (z - w) - g z‖ ≤ L * ‖w‖ := h1
        _ ≤ L * ε := mul_le_mul_of_nonneg_left (norm_lt_of_scaled_ne_zero ρ hε hw).le L.coe_nonneg
  · rw [integral_mul_const, integral_scaled ρ hε, one_mul]

lemma hasFDerivAt_conv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ε : ℝ} (hε : 0 < ε) {g : (Fin D → ℂ) → F} (hcg : HasCompactSupport g) (hg : ContDiff ℝ 1 g)
    (x : Fin D → ℂ) :
    HasFDerivAt (fun x => ∫ t, ρ.scaled ε t • g (x - t))
      (∫ t, ρ.scaled ε t • fderiv ℝ g (x - t)) x := by
  have h := hcg.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (integrable_scaled ρ hε).locallyIntegrable hg x
  have e1 : (ρ.scaled ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) =
      fun x => ∫ t, ρ.scaled ε t • g (x - t) := by
    funext y
    rw [convolution_def]
    rfl
  have e2 : (ρ.scaled ε ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR (Fin D → ℂ), volume]
      fderiv ℝ g) x = ∫ t, ρ.scaled ε t • fderiv ℝ g (x - t) := by
    rw [convolution_def]
    congr 1
  rw [e1, e2] at h
  exact h

end Scaled

lemma exists_cutoff {K U : Set (Fin D → ℂ)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ > 0, ∃ χ : (Fin D → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      cthickening δ K ⊆ U ∧ EqOn χ 1 (cthickening (δ / 2) K) := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨f, hfs, hf, hfr⟩ :=
    (isOpen_thickening (δ := δ) (E := K)).exists_contDiff_support_eq (n := ⊤)
  obtain ⟨g, hgs, hg, hgr⟩ :=
    (isClosed_cthickening (δ := δ / 2) (E := K)).isOpen_compl.exists_contDiff_support_eq (n := ⊤)
  have hts : cthickening (δ / 2) K ⊆ thickening δ K :=
    cthickening_subset_thickening' hδ (by linarith) K
  have hpos : ∀ x, 0 < f x + g x := by
    intro x
    have hf0 : 0 ≤ f x := (hfr (mem_range_self x)).1
    have hg0 : 0 ≤ g x := (hgr (mem_range_self x)).1
    by_cases hx : x ∈ cthickening (δ / 2) K
    · have : f x ≠ 0 := by rw [← Function.mem_support, hfs]; exact hts hx
      exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hf0 (Ne.symm this)) hg0
    · have : g x ≠ 0 := by rw [← Function.mem_support, hgs]; exact hx
      exact add_pos_of_nonneg_of_pos hf0 (lt_of_le_of_ne hg0 (Ne.symm this))
  have hsupp : tsupport (fun x => f x / (f x + g x)) ⊆ cthickening δ K := by
    refine (closure_mono ?_).trans (closure_thickening_subset_cthickening δ K)
    intro x hx
    rw [← hfs]
    intro h
    apply hx
    simp [h]
  refine ⟨δ, hδ, fun x => f x / (f x + g x), hf.div (hf.add hg) (fun x => (hpos x).ne'),
    (hK.cthickening).of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp.trans hδU, hδU, ?_⟩
  intro x hx
  have hg0 : g x = 0 := Function.notMem_support.1 (by rw [hgs]; exact fun h => h hx)
  have hf0 : f x ≠ 0 := by rw [← Function.mem_support, hfs]; exact hts hx
  simp [hg0, hf0]

lemma cutoff_mul {χ φ : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    (hχ : ContDiff ℝ ∞ χ) (hts : tsupport χ ⊆ U) (hφ : ContDiffOn ℝ 3 φ U) :
    ContDiff ℝ 3 (fun x => χ x * φ x) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · exact (contDiff_infty.1 hχ 3).contDiffAt.mul (hφ.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h => hx (hts h)
    have h0 : (fun x => χ x * φ x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h0

lemma mollificationSecondOrder_holds : MollificationSecondOrder := by
  intro D ρ U K φ hU hφ hK hKU
  obtain ⟨δ, hδ, χ, hχ, hχc, hχU, hδU, hχ1⟩ := exists_cutoff hK hU hKU
  set ψ : (Fin D → ℂ) → ℝ := fun x => χ x * φ x with hψ
  have hψd : ContDiff ℝ 3 ψ := cutoff_mul hU hχ hχU hφ
  have hψc : HasCompactSupport ψ := hχc.mul_right
  have hd1 : ContDiff ℝ 2 (fderiv ℝ ψ) := hψd.fderiv_right (by norm_num)
  have hd2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ ψ)) := hd1.fderiv_right (by norm_num)
  obtain ⟨L0, hL0⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hψc hψd (by norm_num)
  obtain ⟨L1, hL1⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hψc.fderiv ℝ) hd1 (by norm_num)
  obtain ⟨L2, hL2⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport ((hψc.fderiv ℝ).fderiv ℝ) hd2 (by norm_num)
  have hD1 : ∀ ε, 0 < ε → fderiv ℝ (fun x => ∫ t, ρ.scaled ε t • ψ (x - t)) =
      fun x => ∫ t, ρ.scaled ε t • fderiv ℝ ψ (x - t) := fun ε hε =>
    funext fun x => (hasFDerivAt_conv ρ hε hψc (hψd.of_le (by norm_num)) x).fderiv
  have hD2 : ∀ ε, 0 < ε → fderiv ℝ (fun x => ∫ t, ρ.scaled ε t • fderiv ℝ ψ (x - t)) =
      fun x => ∫ t, ρ.scaled ε t • fderiv ℝ (fderiv ℝ ψ) (x - t) := fun ε hε =>
    funext fun x => (hasFDerivAt_conv ρ hε (hψc.fderiv ℝ) (hd1.of_le (by norm_num)) x).fderiv
  set C : ℝ := max (max (L0 : ℝ) L1) L2 with hC
  refine ⟨C, δ / 4, by positivity, fun ε hε hεδ z hz => ?_⟩
  have hzU : z ∈ shrink U ε :=
    ((closedBall_subset_closedBall (by linarith : ε ≤ δ)).trans
      (closedBall_subset_cthickening hz δ)).trans hδU
  have hEq : EqOn φ ψ (cthickening (δ / 2) K) := fun y hy => by
    have : χ y = 1 := hχ1 hy
    simp [hψ, this]
  have hball : ∀ y ∈ ball z (δ / 4), closedBall y ε ⊆ cthickening (δ / 2) K := by
    intro y hy x hx
    apply closedBall_subset_cthickening hz (δ / 2)
    rw [mem_closedBall] at hx ⊢
    rw [mem_ball] at hy
    linarith [dist_triangle x y z]
  have hmol : molli ρ ε φ =ᶠ[𝓝 z] fun x => ∫ t, ρ.scaled ε t • ψ (x - t) := by
    filter_upwards [ball_mem_nhds z (by positivity : (0 : ℝ) < δ / 4)] with y hy
    rw [molli_congr ρ hε (hball y hy) hEq]
    simp only [molli, smul_eq_mul]
  have hφψ : φ =ᶠ[𝓝 z] ψ := by
    filter_upwards [ball_mem_nhds z (by positivity : (0 : ℝ) < δ / 2)] with y hy
    exact hEq (closedBall_subset_cthickening hz _ (ball_subset_closedBall hy))
  have hle : ∀ L : NNReal, (L : ℝ) ≤ C → (L : ℝ) * ε ≤ C * ε := fun L hL =>
    mul_le_mul_of_nonneg_right hL hε.le
  refine ⟨hzU, ?_, ?_, ?_⟩
  · rw [hmol.eq_of_nhds, hφψ.eq_of_nhds]
    have := conv_lip ρ hε hL0 z
    rw [Real.norm_eq_abs] at this
    exact this.trans (hle L0 (le_trans (le_max_left _ _) (le_max_left _ _)))
  · rw [hmol.fderiv_eq, hφψ.fderiv_eq, hD1 ε hε]
    exact (conv_lip ρ hε hL1 z).trans (hle L1 (le_trans (le_max_right _ _) (le_max_left _ _)))
  · rw [hmol.fderiv.fderiv_eq, hφψ.fderiv.fderiv_eq, hD1 ε hε, hD2 ε hε]
    exact (conv_lip ρ hε hL2 z).trans (hle L2 (le_max_right _ _))

end

end ReciprocityTheory.AnForm.A
end

section
namespace ReciprocityTheory.AnForm.A

open MeasureTheory Metric Filter Topology Set Real
open scoped ContDiff

noncomputable section

variable {D : ℕ}

lemma measurable_indicator_usc {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (hU : IsOpen U)
    (hφ : UpperSemicontinuousOn φ U) : Measurable (U.indicator φ) := by
  refine measurable_of_Iio fun a => ?_
  have hO : IsOpen {x | x ∈ U ∧ φ x < a} := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxU, hx⟩
    have h1 := hφ x hxU _ hx
    rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hxU)] at h1
    filter_upwards [h1, hU.mem_nhds hxU] with y hy hyU using ⟨hyU, hy⟩
  have : U.indicator φ ⁻¹' Iio a = {x | x ∈ U ∧ φ x < a} ∪ (Uᶜ ∩ {_x | (0 : ℝ) < a}) := by
    ext x
    by_cases hx : x ∈ U <;> simp [hx, Set.indicator]
  rw [this]
  exact hO.measurableSet.union (hU.measurableSet.compl.inter (MeasurableSet.const _))

lemma smul_measurePreserving {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    MeasurePreserving (fun y : Fin D → ℂ => ζ • y) ∧
      MeasurableEmbedding (fun y : Fin D → ℂ => ζ • y) := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  refine ⟨?_, (Homeomorph.smulOfNeZero ζ hζ0).measurableEmbedding⟩
  let c : Circle := ⟨ζ, by simp [Submonoid.unitSphere, hζ]⟩
  have h := volume_preserving_pi (ι := Fin D) (fun _ => (rotation c).measurePreserving)
  convert h using 1
  funext y i
  rw [Pi.smul_apply, smul_eq_mul, rotation_apply]

lemma circle_fubini {Φ : (Fin D → ℂ) → ℝ} (hΦm : Measurable Φ) (hΦi : Integrable Φ)
    {k : (Fin D → ℂ) → ℝ} (hk : Continuous k) (hkc : HasCompactSupport k)
    {P : ℂ → (Fin D → ℂ) → (Fin D → ℂ)} (hP : Continuous (Function.uncurry P))
    (hPm : ∀ ζ : ℂ, ‖ζ‖ = 1 → MeasurePreserving (P ζ) ∧ MeasurableEmbedding (P ζ)) :
    Integrable (fun y => k y * circleAverage (fun ζ => Φ (P ζ y)) 0 1) ∧
    ∫ y, k y * circleAverage (fun ζ => Φ (P ζ y)) 0 1 =
      circleAverage (fun ζ => ∫ y, k y * Φ (P ζ y)) 0 1 := by
  obtain ⟨M, hM⟩ := hk.bounded_above_of_compact_support hkc
  set μθ : Measure ℝ := volume.restrict (Ioc 0 (2 * π)) with hμθ
  set f : ℝ → (Fin D → ℂ) → ℝ := fun θ y => k y * Φ (P (circleMap 0 1 θ) y) with hf
  have hcm : ∀ θ, ‖circleMap 0 1 θ‖ = 1 := fun θ => by simp
  have hfm : Measurable (Function.uncurry f) := by
    have h1 : Continuous fun q : ℝ × (Fin D → ℂ) => P (circleMap 0 1 q.1) q.2 :=
      hP.comp (((continuous_circleMap 0 1).comp continuous_fst).prodMk continuous_snd)
    exact (hk.measurable.comp measurable_snd).mul (hΦm.comp h1.measurable)
  have hsec : ∀ θ, Integrable (f θ) ∧ ∫ y, ‖f θ y‖ ≤ M * ∫ y, |Φ y| := by
    intro θ
    obtain ⟨he, hee⟩ := hPm _ (hcm θ)
    have hi : Integrable fun y => Φ (P (circleMap 0 1 θ) y) :=
      (he.integrable_comp_emb hee).2 hΦi
    have hint : Integrable (f θ) :=
      hi.bdd_mul hk.aestronglyMeasurable (Eventually.of_forall hM)
    refine ⟨hint, ?_⟩
    calc ∫ y, ‖f θ y‖ ≤ ∫ y, M * |Φ (P (circleMap 0 1 θ) y)| := by
          refine integral_mono hint.norm (hi.abs.const_mul M) fun y => ?_
          simp only [hf, norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hM y) (abs_nonneg _)
      _ = M * ∫ y, |Φ y| := by
          rw [integral_const_mul, he.integral_comp hee (fun y => |Φ y|)]
  have hint : Integrable (Function.uncurry f) (μθ.prod volume) := by
    rw [integrable_prod_iff hfm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun θ => (hsec θ).1, ?_⟩
    refine Integrable.mono' (integrable_const (M * ∫ y, |Φ y|)) ?_
      (Eventually.of_forall fun θ => ?_)
    · exact hfm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hsec θ).2
  have hswap := integral_integral_swap hint
  have hpt : ∀ y, k y * circleAverage (fun ζ => Φ (P ζ y)) 0 1 =
      (2 * π)⁻¹ * ∫ θ, f θ y ∂μθ := by
    intro y
    rw [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le two_pi_pos.le,
      mul_left_comm, ← integral_const_mul]
  refine ⟨?_, ?_⟩
  · simp_rw [hpt]
    exact hint.integral_prod_right.const_mul _
  calc ∫ y, k y * circleAverage (fun ζ => Φ (P ζ y)) 0 1
      = ∫ y, (2 * π)⁻¹ * ∫ θ, f θ y ∂μθ := by simp_rw [hpt]
    _ = (2 * π)⁻¹ * ∫ θ, ∫ y, f θ y ∂volume ∂μθ := by rw [integral_const_mul, hswap]
    _ = circleAverage (fun ζ => ∫ y, k y * Φ (P ζ y)) 0 1 := by
        rw [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le two_pi_pos.le]

section Moll

variable (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}

lemma scaled_circle_inv {ε : ℝ} {c : ℂ} (hc : ‖c‖ = 1) (w : Fin D → ℂ) :
    ρ.scaled ε (c • w) = ρ.scaled ε w := by
  simp only [Mollifier.scaled]
  rw [smul_comm, ρ.circle_inv c _ hc]

lemma exists_thick (hU : IsOpen U) {ε : ℝ} (hε : 0 ≤ ε) {z : Fin D → ℂ} (hz : z ∈ shrink U ε) :
    ∃ δ > 0, closedBall z (ε + δ) ⊆ U := by
  obtain ⟨δ, hδ, h⟩ := (isCompact_closedBall z ε).exists_cthickening_subset_open hU hz
  rw [cthickening_closedBall hδ.le hε] at h
  exact ⟨δ, hδ, by rw [add_comm]; exact h⟩

lemma isOpen_shrink (hU : IsOpen U) {ε : ℝ} (hε : 0 < ε) : IsOpen (shrink U ε) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨δ, hδ, h⟩ := exists_thick hU hε.le hz
  filter_upwards [ball_mem_nhds z hδ] with y hy
  rw [mem_ball] at hy
  exact (closedBall_subset_closedBall' (by linarith)).trans h

lemma phiC (hU : IsOpen U) (hφ : IsPsh U φ) {C : Set (Fin D → ℂ)} (hC : IsCompact C)
    (hCU : C ⊆ U) : Measurable (C.indicator φ) ∧ Integrable (C.indicator φ) := by
  have e : C.indicator φ = C.indicator (U.indicator φ) := by
    ext x
    by_cases hx : x ∈ C
    · simp [hx, hCU hx]
    · simp [hx]
  refine ⟨e ▸ (measurable_indicator_usc hU hφ.1).indicator hC.isClosed.measurableSet, ?_⟩
  exact (integrable_indicator_iff hC.isClosed.measurableSet).2
    ((isPsh_locallyIntegrable_thm D U φ hU hφ).integrableOn_compact_subset hCU hC)

lemma molli_eq_C {ε : ℝ} (hε : 0 < ε) {C : Set (Fin D → ℂ)} {z : Fin D → ℂ}
    (hz : closedBall z ε ⊆ C) :
    molli ρ ε φ z = ∫ y, ρ.scaled ε y * C.indicator φ (z - y) := by
  rw [molli_congr ρ hε (U := C) hz (fun x hx => (indicator_of_mem hx φ).symm)]
  rfl

lemma integrable_kC {ε : ℝ} (hε : 0 < ε) {Φ : (Fin D → ℂ) → ℝ} (hΦ : Integrable Φ)
    (z : Fin D → ℂ) : Integrable fun y => ρ.scaled ε y * Φ (z - y) := by
  obtain ⟨M, hM⟩ := (scaled_contDiff ρ ε).continuous.bounded_above_of_compact_support
    (scaled_hasCompactSupport ρ hε)
  exact (hΦ.comp_sub_left z).bdd_mul (scaled_contDiff ρ ε).continuous.aestronglyMeasurable
    (Eventually.of_forall hM)

lemma mem_ball_sub {ε : ℝ} (hε : 0 < ε) {y : Fin D → ℂ} (hy : ρ.scaled ε y ≠ 0)
    (z : Fin D → ℂ) : z - y ∈ closedBall z ε := by
  rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]
  exact (norm_lt_of_scaled_ne_zero ρ hε hy).le

lemma le_molli (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε) {z : Fin D → ℂ}
    (hz : z ∈ shrink U ε) : φ z ≤ molli ρ ε φ z := by
  set C := closedBall z ε with hCdef
  obtain ⟨hm, hi⟩ := phiC hU hφ (isCompact_closedBall z ε) hz
  have hP : Continuous (Function.uncurry fun (ζ : ℂ) (y : Fin D → ℂ) => z - ζ • y) :=
    continuous_const.sub (continuous_fst.smul continuous_snd)
  have hPm : ∀ ζ : ℂ, ‖ζ‖ = 1 → MeasurePreserving (fun y : Fin D → ℂ => z - ζ • y) ∧
      MeasurableEmbedding (fun y : Fin D → ℂ => z - ζ • y) := by
    intro ζ hζ
    obtain ⟨h1, h2⟩ := smul_measurePreserving (D := D) hζ
    exact ⟨(Measure.measurePreserving_sub_left volume z).comp h1,
      (Homeomorph.subLeft z).measurableEmbedding.comp h2⟩
  obtain ⟨hFint, hF⟩ := circle_fubini hm hi (scaled_contDiff ρ ε).continuous
    (scaled_hasCompactSupport ρ hε) hP hPm
  have hrot : ∀ ζ ∈ sphere (0 : ℂ) |1|,
      (∫ y, ρ.scaled ε y * C.indicator φ (z - ζ • y)) = molli ρ ε φ z := by
    intro ζ hζ
    have hζ' : ‖ζ‖ = 1 := by simpa using hζ
    obtain ⟨h1, h2⟩ := smul_measurePreserving (D := D) hζ'
    have := h1.integral_comp h2 (fun u => ρ.scaled ε u * C.indicator φ (z - u))
    rw [molli_eq_C ρ hε (subset_refl _), ← this]
    congr 1
    funext y
    rw [scaled_circle_inv ρ hζ']
  rw [circleAverage_congr_sphere hrot, circleAverage_const] at hF
  rw [← hF]
  calc φ z = ∫ y, ρ.scaled ε y * φ z := by
        rw [integral_mul_const, integral_scaled ρ hε, one_mul]
    _ ≤ _ := by
      refine integral_mono ((integrable_scaled ρ hε).mul_const _) hFint fun y => ?_
      by_cases hy : ρ.scaled ε y = 0
      · simp [hy]
      refine mul_le_mul_of_nonneg_left ?_ (scaled_nonneg ρ hε y)
      have hyε := (norm_lt_of_scaled_ne_zero ρ hε hy).le
      have hdisc : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • (-y) ∈ C := by
        intro ζ hζ
        rw [hCdef, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_neg]
        nlinarith [norm_nonneg ζ, norm_nonneg y]
      obtain ⟨-, hmean⟩ := hφ.2 z (-y) (fun ζ hζ => hz (hdisc ζ hζ))
      refine hmean.trans (le_of_eq (circleAverage_congr_sphere fun ζ hζ => ?_))
      have hζ' : ‖ζ‖ ≤ 1 := by simp at hζ; linarith
      have h := hdisc ζ hζ'
      rw [smul_neg, ← sub_eq_add_neg] at h ⊢
      rw [indicator_of_mem h]

lemma molli_le_polyMax (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε)
    {z : Fin D → ℂ} (hz : z ∈ shrink U ε) : molli ρ ε φ z ≤ polyMax φ z ε := by
  obtain ⟨-, hi⟩ := phiC hU hφ (isCompact_closedBall z ε) hz
  rw [molli_eq_C ρ hε (subset_refl _)]
  calc _ ≤ ∫ y, ρ.scaled ε y * polyMax φ z ε := by
        refine integral_mono (integrable_kC ρ hε hi z) ((integrable_scaled ρ hε).mul_const _)
          fun y => ?_
        by_cases hy : ρ.scaled ε y = 0
        · simp [hy]
        refine mul_le_mul_of_nonneg_left ?_ (scaled_nonneg ρ hε y)
        have hmem := mem_ball_sub ρ hε hy z
        rw [indicator_of_mem hmem]
        exact (hφ.1.mono hz).bddAbove_of_isCompact (isCompact_closedBall z ε) |>.elim
          fun _ _ => le_csSup ((hφ.1.mono hz).bddAbove_of_isCompact (isCompact_closedBall z ε))
            (mem_image_of_mem φ hmem)
    _ = polyMax φ z ε := by rw [integral_mul_const, integral_scaled ρ hε, one_mul]

lemma molli_contDiffAt (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε)
    {z : Fin D → ℂ} (hz : z ∈ shrink U ε) : ContDiffAt ℝ ∞ (molli ρ ε φ) z := by
  obtain ⟨δ, hδ, hδU⟩ := exists_thick hU hε.le hz
  obtain ⟨-, hi⟩ := phiC hU hφ (isCompact_closedBall z (ε + δ)) hδU
  have hg := (scaled_hasCompactSupport ρ hε).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (n := ⊤) (scaled_contDiff ρ ε)
    hi.locallyIntegrable
  refine hg.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds z hδ] with y hy
  rw [mem_ball] at hy
  rw [molli_eq_C ρ hε (C := closedBall z (ε + δ)) (closedBall_subset_closedBall' (by linarith)),
    convolution_def]
  rfl

lemma molli_submean (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε)
    {z w : Fin D → ℂ} (hd : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ shrink U ε) :
    molli ρ ε φ z ≤ circleAverage (fun ζ : ℂ => molli ρ ε φ (z + ζ • w)) 0 1 := by
  set C : Set (Fin D → ℂ) :=
    (fun q : ℂ × (Fin D → ℂ) => z + q.1 • w + q.2) '' (closedBall 0 1 ×ˢ closedBall 0 ε) with hCdef
  have hC : IsCompact C :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image (by fun_prop)
  have hball : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → closedBall (z + ζ • w) ε ⊆ C := by
    intro ζ hζ x hx
    refine ⟨(ζ, x - (z + ζ • w)), ⟨by simpa using hζ, ?_⟩, by simp⟩
    rw [mem_closedBall, dist_eq_norm, sub_zero, ← dist_eq_norm]
    exact hx
  have hCU : C ⊆ U := by
    rintro _ ⟨⟨ζ, v⟩, ⟨hζ, hv⟩, rfl⟩
    refine hd ζ (by simpa using hζ) ?_
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    simpa using hv
  obtain ⟨hm, hi⟩ := phiC hU hφ hC hCU
  have hP : Continuous (Function.uncurry fun (ζ : ℂ) (y : Fin D → ℂ) => z + ζ • w - y) :=
    (continuous_const.add (continuous_fst.smul continuous_const)).sub continuous_snd
  have hPm : ∀ ζ : ℂ, ‖ζ‖ = 1 → MeasurePreserving (fun y : Fin D → ℂ => z + ζ • w - y) ∧
      MeasurableEmbedding (fun y : Fin D → ℂ => z + ζ • w - y) := fun ζ _ =>
    ⟨Measure.measurePreserving_sub_left volume _, (Homeomorph.subLeft _).measurableEmbedding⟩
  obtain ⟨hFint, hF⟩ := circle_fubini hm hi (scaled_contDiff ρ ε).continuous
    (scaled_hasCompactSupport ρ hε) hP hPm
  have hcirc : ∀ ζ ∈ sphere (0 : ℂ) |1|,
      (∫ y, ρ.scaled ε y * C.indicator φ (z + ζ • w - y)) = molli ρ ε φ (z + ζ • w) := by
    intro ζ hζ
    have hζ' : ‖ζ‖ ≤ 1 := by simp at hζ; linarith
    rw [molli_eq_C ρ hε (hball ζ hζ')]
  rw [circleAverage_congr_sphere hcirc] at hF
  have h0 : closedBall z ε ⊆ C := by simpa using hball 0 (by simp)
  rw [← hF, molli_eq_C ρ hε h0]
  refine integral_mono (integrable_kC ρ hε hi z) hFint fun y => ?_
  by_cases hy : ρ.scaled ε y = 0
  · simp [hy]
  refine mul_le_mul_of_nonneg_left ?_ (scaled_nonneg ρ hε y)
  have hyε := (norm_lt_of_scaled_ne_zero ρ hε hy).le
  have hin : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z - y + ζ • w ∈ C := by
    intro ζ hζ
    refine hball ζ hζ ?_
    rw [mem_closedBall, dist_eq_norm, show z - y + ζ • w - (z + ζ • w) = -y by abel, norm_neg]
    exact hyε
  obtain ⟨-, hmean⟩ := hφ.2 (z - y) w (fun ζ hζ => hCU (hin ζ hζ))
  have h00 : z - y ∈ C := by simpa using hin 0 (by simp)
  rw [indicator_of_mem h00]
  refine hmean.trans (le_of_eq (circleAverage_congr_sphere fun ζ hζ => ?_))
  have hζ' : ‖ζ‖ ≤ 1 := by simp at hζ; linarith
  show φ (z - y + ζ • w) = C.indicator φ (z + ζ • w - y)
  rw [show z + ζ • w - y = z - y + ζ • w by abel, indicator_of_mem (hin ζ hζ')]

lemma mollify_main (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε) :
    IsOpen (shrink U ε) ∧ ContDiffOn ℝ ∞ (molli ρ ε φ) (shrink U ε) ∧
      IsPsh (shrink U ε) (molli ρ ε φ) ∧
      ∀ z ∈ shrink U ε, φ z ≤ molli ρ ε φ z ∧ molli ρ ε φ z ≤ polyMax φ z ε := by
  have hcont : ContinuousOn (molli ρ ε φ) (shrink U ε) := fun z hz =>
    (molli_contDiffAt ρ hU hφ hε hz).continuousAt.continuousWithinAt
  refine ⟨isOpen_shrink hU hε, fun z hz => (molli_contDiffAt ρ hU hφ hε hz).contDiffWithinAt,
    ⟨hcont.upperSemicontinuousOn, fun z w hd => ⟨?_, molli_submean ρ hU hφ hε hd⟩⟩,
    fun z hz => ⟨le_molli ρ hU hφ hε hz, molli_le_polyMax ρ hU hφ hε hz⟩⟩
  refine ContinuousOn.circleIntegrable' ?_
  refine hcont.comp (by fun_prop : Continuous fun ζ : ℂ => z + ζ • w).continuousOn fun ζ hζ => ?_
  exact hd ζ (by simp at hζ; linarith)

end Moll

end

end ReciprocityTheory.AnForm.A
end

section
namespace ReciprocityTheory.AnForm.A

open MeasureTheory Metric Filter Topology Set

noncomputable section

variable {D : ℕ}

section PolyMax

variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}

lemma polyMax_bdd (hφ : UpperSemicontinuousOn φ U) {t : ℝ} (h : closedBall z t ⊆ U) :
    BddAbove (φ '' closedBall z t) :=
  (hφ.mono h).bddAbove_of_isCompact (isCompact_closedBall z t)

lemma le_polyMax (hφ : UpperSemicontinuousOn φ U) {t : ℝ} (h : closedBall z t ⊆ U) {x}
    (hx : x ∈ closedBall z t) : φ x ≤ polyMax φ z t :=
  le_csSup (polyMax_bdd hφ h) (mem_image_of_mem φ hx)

lemma polyMax_le' {t c : ℝ} (ht : 0 ≤ t) (h : ∀ x ∈ closedBall z t, φ x ≤ c) :
    polyMax φ z t ≤ c :=
  csSup_le ((nonempty_closedBall.2 ht).image φ) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

lemma polyMax_attained (hφ : UpperSemicontinuousOn φ U) {t : ℝ} (ht : 0 ≤ t)
    (h : closedBall z t ⊆ U) : ∃ x ∈ closedBall z t, φ x = polyMax φ z t := by
  obtain ⟨a, ha, hmax⟩ := (hφ.mono h).exists_isMaxOn (nonempty_closedBall.2 ht)
    (isCompact_closedBall z t)
  exact ⟨a, ha, le_antisymm (le_polyMax hφ h ha)
    (polyMax_le' ht fun x hx => isMaxOn_iff.1 hmax x hx)⟩

lemma polyMax_mono' (hφ : UpperSemicontinuousOn φ U) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (h : closedBall z t ⊆ U) : polyMax φ z s ≤ polyMax φ z t :=
  csSup_le_csSup (polyMax_bdd hφ h) ((nonempty_closedBall.2 hs).image φ)
    (image_mono (closedBall_subset_closedBall hst))

lemma polyMax_zero' : polyMax φ z 0 = φ z := by
  simp [polyMax, closedBall_zero]

lemma polyMax_usc (hU : IsOpen U) (hφ : UpperSemicontinuousOn φ U) {t : ℝ} (ht : 0 ≤ t)
    (h : closedBall z t ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, closedBall z (t + δ) ⊆ U ∧
      ∀ t', 0 ≤ t' → t' ≤ t + δ → polyMax φ z t' < polyMax φ z t + ε := by
  set V : Set (Fin D → ℂ) := {x | x ∈ U ∧ φ x < polyMax φ z t + ε} with hVdef
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxU, hx⟩
    have h1 := hφ x hxU _ hx
    rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hxU)] at h1
    filter_upwards [h1, hU.mem_nhds hxU] with y hy hyU using ⟨hyU, hy⟩
  have hsub : closedBall z t ⊆ V := fun x hx =>
    ⟨h hx, lt_of_le_of_lt (le_polyMax hφ h hx) (by linarith)⟩
  obtain ⟨δ, hδ, hδV⟩ := (isCompact_closedBall z t).exists_cthickening_subset_open hV hsub
  rw [cthickening_closedBall hδ.le ht, add_comm δ t] at hδV
  have hVU : closedBall z (t + δ) ⊆ U := fun x hx => (hδV hx).1
  refine ⟨δ, hδ, hVU, fun t' ht' ht'le => ?_⟩
  have hsub' : closedBall z t' ⊆ closedBall z (t + δ) := closedBall_subset_closedBall ht'le
  obtain ⟨x, hx, hxe⟩ := polyMax_attained hφ ht' (hsub'.trans hVU)
  rw [← hxe]
  exact (hδV (hsub' hx)).2

lemma polyMax_exp_usc (hU : IsOpen U) (hφ : UpperSemicontinuousOn φ U) {R : ℝ} (hR0 : 0 < R)
    (hR : closedBall z R ⊆ U) :
    UpperSemicontinuousOn (fun s => polyMax φ z (Real.exp s)) (Iic (Real.log R)) := by
  intro s hs y hy
  have hexp : Real.exp s ≤ R := (Real.exp_le_exp.2 hs).trans_eq (Real.exp_log hR0)
  have hsR : closedBall z (Real.exp s) ⊆ U := (closedBall_subset_closedBall hexp).trans hR
  obtain ⟨δ, hδ, -, hδ'⟩ := polyMax_usc hU hφ (Real.exp_pos s).le hsR (sub_pos.2 hy)
  have hev : ∀ᶠ s' in 𝓝 s, Real.exp s' < Real.exp s + δ :=
    (Real.continuous_exp.tendsto s) (Iio_mem_nhds (by linarith))
  apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
  filter_upwards [hev] with s' hs'
  have := hδ' _ (Real.exp_pos s').le hs'.le
  linarith

end PolyMax

lemma chord_to_convex {f : ℝ → ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    (h : ∀ x ∈ s, ∀ y ∈ s, x < y → ∀ α β : ℝ, f x ≤ α + β * x → f y ≤ α + β * y →
      ∀ p ∈ Icc x y, f p ≤ α + β * p) : ConvexOn ℝ s f := by
  have key : ∀ x ∈ s, ∀ y ∈ s, x < y → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a * x + b * y) ≤ a * f x + b * f y := by
    intro x hx y hy hxy a b ha hb hab
    have hyx : 0 < y - x := sub_pos.2 hxy
    set β := (f y - f x) / (y - x) with hβdef
    have hβ : β * (y - x) = f y - f x := div_mul_cancel₀ _ hyx.ne'
    have ha' : a = 1 - b := by linarith
    have e1 : a * x + b * y - x = b * (y - x) := by rw [ha']; ring
    have e2 : y - (a * x + b * y) = a * (y - x) := by rw [ha']; ring
    have hp : a * x + b * y ∈ Icc x y :=
      ⟨by nlinarith [mul_nonneg hb hyx.le], by nlinarith [mul_nonneg ha hyx.le]⟩
    have := h x hx y hy hxy (f x - β * x) β (by linarith) (by linarith [hβ]) _ hp
    calc f (a * x + b * y) ≤ f x - β * x + β * (a * x + b * y) := this
      _ = a * f x + b * f y := by rw [ha']; linear_combination b * hβ
  refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · exact key x hx y hy hxy a b ha hb hab
  · rw [← add_mul, hab, one_mul, ← add_mul, hab, one_mul]
  · have := key y hy x hx hxy b a hb ha (by linarith)
    rw [add_comm (b * y)] at this
    linarith

lemma ca_const_mul (c : ℝ) (f : ℂ → ℝ) :
    Real.circleAverage (fun ζ => c * f ζ) 0 1 = c * Real.circleAverage f 0 1 := by
  simp_rw [← smul_eq_mul]
  exact Real.circleAverage_fun_smul

lemma ca_re : Real.circleAverage (fun ζ : ℂ => ζ.re) 0 1 = 0 := by
  have h1 := Complex.reCLM.circleAverage_comp_comm (circleIntegrable_id (0 : ℂ) 1)
  have h2 : Real.circleAverage (fun ζ : ℂ => ζ) 0 1 = 0 := by
    have := (differentiable_id (𝕜 := ℂ) (E := ℂ)).diffContOnCl (s := ball (0 : ℂ) |1|)
    exact this.circleAverage
  simp only [Function.comp_def, Complex.reCLM_apply, h2, Complex.zero_re] at h1
  exact h1

section Chord

variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}

lemma polydiscMax_exp_chord_bound (hU : IsOpen U) (hφ : IsPsh U φ) {R : ℝ} (hR0 : 0 < R)
    (hR : closedBall z R ⊆ U) {a b α β : ℝ} (hab : a < b) (hb : b ≤ Real.log R)
    (ha' : polyMax φ z (Real.exp a) ≤ α + β * a) (hb' : polyMax φ z (Real.exp b) ≤ α + β * b)
    {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : s ∈ Icc a b) :
    polyMax φ z (Real.exp s) + δ * Real.exp s ^ 2 ≤ α + β * s + δ * Real.exp b ^ 2 := by
  set f : ℝ → ℝ := fun s => polyMax φ z (Real.exp s) with hf
  set H : ℝ → ℝ := fun s => f s + δ * Real.exp s ^ 2 - α - β * s - δ * Real.exp b ^ 2 with hH
  have hbR : Real.exp b ≤ R := (Real.exp_le_exp.2 hb).trans_eq (Real.exp_log hR0)
  have hfu : UpperSemicontinuousOn f (Icc a b) :=
    (polyMax_exp_usc hU hφ.1 hR0 hR).mono (fun x hx => hx.2.trans hb)
  have hHu : UpperSemicontinuousOn H (Icc a b) := by
    have hc : Continuous fun s : ℝ => δ * Real.exp s ^ 2 - α - β * s - δ * Real.exp b ^ 2 := by
      fun_prop
    have hHeq : H = fun x => f x + (δ * Real.exp x ^ 2 - α - β * x - δ * Real.exp b ^ 2) := by
      funext x
      show f x + δ * Real.exp x ^ 2 - α - β * x - δ * Real.exp b ^ 2 = _
      ring
    rw [hHeq]
    exact hfu.add (hc.upperSemicontinuous.upperSemicontinuousOn _)
  obtain ⟨s0, hs0, hmax⟩ := hHu.exists_isMaxOn ⟨a, left_mem_Icc.2 hab.le⟩ isCompact_Icc
  have hHs := isMaxOn_iff.1 hmax s hs
  suffices hneg : H s0 ≤ 0 by
    have : H s ≤ 0 := hHs.trans hneg
    simp only [hH, hf] at this
    linarith
  by_contra hpos
  push Not at hpos
  have hea : Real.exp a ^ 2 ≤ Real.exp b ^ 2 := by
    have := Real.exp_le_exp.2 hab.le
    have := Real.exp_pos a
    nlinarith
  have ha0 : a < s0 := by
    rcases eq_or_lt_of_le hs0.1 with h | h
    · rw [← h] at hpos
      simp only [hH, hf] at hpos
      nlinarith
    · exact h
  have hs0b : s0 < b := by
    rcases eq_or_lt_of_le hs0.2 with h | h
    · rw [h] at hpos
      simp only [hH, hf] at hpos
      nlinarith
    · exact h
  set r0 := Real.exp s0 with hr0
  have hr0pos : 0 < r0 := Real.exp_pos _
  have h1 : Real.exp a < r0 := Real.exp_lt_exp.2 ha0
  have h2 : r0 < Real.exp b := Real.exp_lt_exp.2 hs0b
  set ρ := min (r0 - Real.exp a) (Real.exp b - r0) with hρ
  have hρpos : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρ1 : ρ ≤ r0 - Real.exp a := min_le_left _ _
  have hρ2 : ρ ≤ Real.exp b - r0 := min_le_right _ _
  have hea0 : 0 < Real.exp a := Real.exp_pos a
  have hr0U : closedBall z r0 ⊆ U := (closedBall_subset_closedBall (by linarith)).trans hR
  obtain ⟨x0, hx0, hx0e⟩ := polyMax_attained hφ.1 hr0pos.le hr0U
  set u0 : Fin D → ℂ := ((r0 : ℂ)⁻¹) • (x0 - z) with hu0def
  have hr0c : (r0 : ℂ) ≠ 0 := by exact_mod_cast hr0pos.ne'
  have hu0 : ‖u0‖ ≤ 1 := by
    rw [mem_closedBall, dist_eq_norm] at hx0
    calc ‖u0‖ = r0⁻¹ * ‖x0 - z‖ := by
          simp [u0, norm_smul, abs_of_pos hr0pos]
      _ ≤ r0⁻¹ * r0 := by gcongr
      _ = 1 := inv_mul_cancel₀ hr0pos.ne'
  have hx0eq : x0 = z + (r0 : ℂ) • u0 := by
    rw [hu0def, smul_smul, mul_inv_cancel₀ hr0c, one_smul, add_sub_cancel]
  clear_value u0
  set P : ℂ → ℂ := fun ζ => (r0 : ℂ) + (ρ : ℂ) * ζ with hP
  have hPle : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → ‖P ζ‖ ≤ r0 + ρ := by
    intro ζ hζ
    calc ‖P ζ‖ ≤ ‖(r0 : ℂ)‖ + ‖(ρ : ℂ) * ζ‖ := norm_add_le _ _
      _ = r0 + ρ * ‖ζ‖ := by simp [abs_of_pos hr0pos, abs_of_pos hρpos]
      _ ≤ r0 + ρ := by nlinarith [norm_nonneg ζ]
  have hPge : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → r0 - ρ ≤ ‖P ζ‖ := by
    intro ζ hζ
    have := norm_sub_le (P ζ) ((ρ : ℂ) * ζ)
    have e : P ζ - (ρ : ℂ) * ζ = r0 := by simp [P]
    rw [e] at this
    have : ‖(r0 : ℂ)‖ = r0 := by simp [abs_of_pos hr0pos]
    have : ‖(ρ : ℂ) * ζ‖ = ρ * ‖ζ‖ := by simp [abs_of_pos hρpos]
    nlinarith [norm_nonneg ζ]
  have hPpos : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → 0 < ‖P ζ‖ := fun ζ hζ => by linarith [hPge ζ hζ]
  set w : Fin D → ℂ := (ρ : ℂ) • u0 with hw
  have hpt : ∀ ζ : ℂ, x0 + ζ • w = z + P ζ • u0 := by
    intro ζ
    rw [hx0eq, hw, smul_smul, add_assoc, ← add_smul]
    congr 2
    simp only [P]
    ring
  have hin : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → x0 + ζ • w ∈ closedBall z ‖P ζ‖ := by
    intro ζ hζ
    rw [hpt, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    nlinarith [norm_nonneg (P ζ)]
  have hballU : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → closedBall z ‖P ζ‖ ⊆ U := fun ζ hζ =>
    (closedBall_subset_closedBall (by linarith [hPle ζ hζ])).trans hR
  obtain ⟨hint, hmean⟩ := hφ.2 x0 w (fun ζ hζ => hballU ζ hζ (hin ζ hζ))

  set K := H s0 + α + δ * Real.exp b ^ 2 with hK
  set g : ℂ → ℝ := fun ζ => K - δ * ‖P ζ‖ ^ 2 + β * Real.log ‖P ζ‖ with hg
  have hbound : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → φ (x0 + ζ • w) ≤ g ζ := by
    intro ζ hζ
    have hpos := hPpos ζ hζ
    have hX : Real.log ‖P ζ‖ ∈ Icc a b := by
      constructor
      · rw [Real.le_log_iff_exp_le hpos]; linarith [hPge ζ hζ]
      · rw [Real.log_le_iff_le_exp hpos]; linarith [hPle ζ hζ]
    have hHX := isMaxOn_iff.1 hmax _ hX
    simp only [hH, hf, Real.exp_log hpos] at hHX
    have := le_polyMax hφ.1 (hballU ζ hζ) (hin ζ hζ)
    simp only [hg, hK]
    linarith
  have hsph : ∀ ζ ∈ sphere (0 : ℂ) |1|, ‖ζ‖ = 1 := by intro ζ hζ; simpa using hζ
  have hcb : ∀ ζ ∈ closedBall (0 : ℂ) |1|, ‖ζ‖ ≤ 1 := by intro ζ hζ; simpa using hζ
  have hPd : Differentiable ℂ P := by rw [hP]; fun_prop
  have hPcont : Continuous P := hPd.continuous
  have hlogc : ContinuousOn (fun ζ => Real.log ‖P ζ‖) (sphere (0 : ℂ) |1|) :=
    (hPcont.norm.continuousOn).log (fun ζ hζ => (hPpos ζ (hsph ζ hζ).le).ne')
  have hsqc : Continuous (fun ζ => ‖P ζ‖ ^ 2) := hPcont.norm.pow 2
  have hA2 : Real.circleAverage (fun ζ => Real.log ‖P ζ‖) 0 1 = s0 := by
    have han : AnalyticOnNhd ℂ P (closedBall 0 |1|) := fun x _ => hPd.analyticAt x
    rw [AnalyticOnNhd.circleAverage_log_norm_of_ne_zero han
      (fun u hu => norm_ne_zero_iff.1 (hPpos u (hcb u hu)).ne')]
    have : P 0 = (r0 : ℂ) := by simp [hP]
    rw [this, Complex.norm_real, Real.norm_of_nonneg hr0pos.le, hr0, Real.log_exp]
  have hA1 : Real.circleAverage (fun ζ => ‖P ζ‖ ^ 2) 0 1 = r0 ^ 2 + ρ ^ 2 := by
    have heq : Set.EqOn (fun ζ => ‖P ζ‖ ^ 2) (fun ζ => (r0 ^ 2 + ρ ^ 2) + (2 * r0 * ρ) * ζ.re)
        (sphere (0 : ℂ) |1|) := by
      intro ζ hζ
      have hn := hsph ζ hζ
      have h1 : ζ.re * ζ.re + ζ.im * ζ.im = 1 := by
        rw [← Complex.normSq_apply, ← Complex.sq_norm, hn]; norm_num
      simp only [hP]
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
      linear_combination ρ ^ 2 * h1
    rw [Real.circleAverage_congr_sphere heq, Real.circleAverage_fun_add (circleIntegrable_const _ _ _)
      ((by fun_prop : Continuous (fun ζ : ℂ => 2 * r0 * ρ * ζ.re)).continuousOn.circleIntegrable'),
      Real.circleAverage_const, ca_const_mul, ca_re]
    ring
  have hgint : CircleIntegrable g 0 1 := by
    apply ContinuousOn.circleIntegrable'
    exact (continuousOn_const.sub (continuousOn_const.mul hsqc.continuousOn)).add
      (continuousOn_const.mul hlogc)
  have hCAg : Real.circleAverage g 0 1 = K - δ * (r0 ^ 2 + ρ ^ 2) + β * s0 := by
    have i1 : CircleIntegrable (fun ζ => K - δ * ‖P ζ‖ ^ 2) 0 1 :=
      (continuous_const.sub (continuous_const.mul hsqc)).continuousOn.circleIntegrable'
    have i2 : CircleIntegrable (fun ζ => β * Real.log ‖P ζ‖) 0 1 :=
      (continuousOn_const.mul hlogc).circleIntegrable'
    have i3 : CircleIntegrable (fun ζ => δ * ‖P ζ‖ ^ 2) 0 1 :=
      (continuous_const.mul hsqc).continuousOn.circleIntegrable'
    rw [hg, Real.circleAverage_fun_add i1 i2, Real.circleAverage_fun_sub
      (circleIntegrable_const _ _ _) i3,
      Real.circleAverage_const, ca_const_mul, ca_const_mul, hA1, hA2]
  have hφx0 : φ x0 = H s0 - δ * r0 ^ 2 + α + β * s0 + δ * Real.exp b ^ 2 := by
    rw [hx0e]
    show polyMax φ z r0 = (polyMax φ z r0 + δ * r0 ^ 2 - α - β * s0 - δ * Real.exp b ^ 2)
      - δ * r0 ^ 2 + α + β * s0 + δ * Real.exp b ^ 2
    ring
  have hle := hmean.trans
    (Real.circleAverage_mono hint hgint (fun ζ hζ => hbound ζ (hsph ζ hζ).le))
  rw [hCAg, hφx0] at hle
  linarith [hK, mul_pos hδ (pow_pos hρpos 2)]

end Chord

theorem polyMaxLogConvex_thm : PolyMaxLogConvexStatement := by
  intro D U φ z R hU hφ hR0 hR
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine chord_to_convex (convex_Iic _) fun x hx y hy hxy α β hx' hy' p hp => ?_
    refine le_of_forall_pos_le_add fun e he => ?_
    have hB : 0 < Real.exp y ^ 2 + 1 := by positivity
    have key := polydiscMax_exp_chord_bound hU hφ hR0 hR hxy hy hx' hy' (div_pos he hB) hp
    have h2 : e / (Real.exp y ^ 2 + 1) * Real.exp y ^ 2 ≤ e := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hB]; nlinarith
    have h3 : 0 ≤ e / (Real.exp y ^ 2 + 1) * Real.exp p ^ 2 := by positivity
    linarith
  · exact fun s hs t ht hst =>
      polyMax_mono' hφ.1 hs.1.le hst ((closedBall_subset_closedBall ht.2).trans hR)
  · exact fun t ht0 htR => polyMax_attained hφ.1 ht0 ((closedBall_subset_closedBall htR).trans hR)
  · have h0U : closedBall z 0 ⊆ U := (closedBall_subset_closedBall hR0.le).trans hR
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hR0)] with t ht htR
      have hsub : closedBall z t ⊆ U :=
        (closedBall_subset_closedBall (le_of_lt htR)).trans hR
      have := le_polyMax hφ.1 hsub (mem_closedBall_self (le_of_lt ht))
      linarith
    · obtain ⟨δ, hδ, -, hδ'⟩ := polyMax_usc hU hφ.1 le_rfl h0U (sub_pos.2 ha)
      rw [polyMax_zero'] at hδ'
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with t ht htδ
      have := hδ' t (le_of_lt ht) (by simp only [zero_add]; exact le_of_lt htδ)
      linarith

theorem mollify_thm : MollifyStatement := by
  intro D ρ U φ hU hφ
  refine ⟨fun ε hε => mollify_main ρ hU hφ hε, fun z hz => ?_⟩
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z hz
  have hR0 : 0 < r / 2 := by positivity
  have hRU : closedBall z (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  have hlim := (polyMaxLogConvex_thm D U φ z (r / 2) hU hφ hR0 hRU).2.2.2
  have hsh : ∀ ε, 0 < ε → ε < r / 2 → z ∈ shrink U ε := fun ε _ hεR =>
    (closedBall_subset_closedBall hεR.le).trans hRU
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hR0)] with ε hε hεR
    exact ((mollify_main ρ hU hφ hε).2.2.2 z (hsh ε hε hεR)).1
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hR0)] with ε hε hεR
    exact ((mollify_main ρ hU hφ hε).2.2.2 z (hsh ε hε hεR)).2

theorem mollification_second_order : MollificationSecondOrder :=
  mollificationSecondOrder_holds

end

end ReciprocityTheory.AnForm.A
end
