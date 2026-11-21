import ReciprocityTheory.L2DbarEstimates.LeviForms.FixedA

section
namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

theorem fx_lintegral_ball_translate {n : ℕ} (y₀ : V n) (ρ : ℝ) (Φ : V n → ℝ≥0∞) :
    ∫⁻ y in ball (0 : V n) ρ, Φ (y₀ + y) = ∫⁻ y in ball y₀ ρ, Φ y := by
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
  have h : ∀ y, (ball (0 : V n) ρ).indicator (fun y => Φ (y₀ + y)) y =
      (ball y₀ ρ).indicator Φ (y₀ + y) := fun y => by
    simp [Set.indicator, mem_ball, dist_eq_norm]
  simp_rw [h]
  exact lintegral_add_left_eq_self ((ball y₀ ρ).indicator Φ) y₀

theorem fx_tendsto_zero_of_weighted {M : Type*} [TopologicalSpace M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (hn : 1 ≤ n) (hV : VanishStatement n)
    (z : M → V n) (hz : IsLocalHomeomorph z) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) (p : M) (hp : p ∈ e.source) (ρ : ℝ) (hρ : 0 < ρ)
    (hball : ball (z p) ρ ⊆ e.target) (c₀ C' Cb : ℝ) (hc₀ : 0 < c₀) (hC' : 0 < C')
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝[>] 0)) (u : ℕ → M → ℂ) (w : ℕ → M → ℝ)
    (hu : ∀ k, Measurable (u k)) (hw : ∀ k, Measurable (w k))
    (hdiff : ∀ k, DifferentiableOn ℂ (fun y => u k (e.symm y)) (ball (z p) ρ))
    (hlow : ∀ k, ∀ y ∈ ball (z p) ρ,
      c₀ * (C' * ‖y - z p‖ ^ 2 + δ k) ^ (-(n : ℝ)) ≤ w k (e.symm y))
    (hint : ∀ k, ∫⁻ x, ENNReal.ofReal (‖u k x‖ ^ 2 * w k x) ∂vol n z ≤ ENNReal.ofReal Cb) :
    Tendsto (fun k => u k p) atTop (𝓝 0) := by
  have hzp : e.symm (z p) = p := by rw [he hp]; exact e.left_inv hp
  have key := hV hn ρ C' (c₀⁻¹ * Cb) δ (fun k y => u k (e.symm (z p + y))) hρ hC' hδ ?_ ?_
  · simpa [hzp] using key
  · intro k
    refine (hdiff k).comp ((differentiableOn_const _).add differentiableOn_id) fun y hy => ?_
    simpa [mem_ball, dist_eq_norm] using hy
  · intro k
    have h1 := fx_lintegral_ball_translate (z p) ρ
      (fun y => ENNReal.ofReal (‖u k (e.symm y)‖ ^ 2 * (C' * ‖y - z p‖ ^ 2 + δ k) ^ (-(n : ℝ))))
    simp only [add_sub_cancel_left] at h1
    rw [h1]
    set f' : M → ℝ≥0∞ := e.source.indicator fun x => ENNReal.ofReal (‖u k x‖ ^ 2 * w k x)
      with hf'
    have hf'm : Measurable f' :=
      (ENNReal.measurable_ofReal.comp (((hu k).norm.pow_const 2).mul (hw k))).indicator
        e.open_source.measurableSet
    have hchart := lintegral_vol_chart n z hz e he f' hf'm
      (fun x hx => by simp [hf', hx])
    calc ∫⁻ y in ball (z p) ρ,
          ENNReal.ofReal (‖u k (e.symm y)‖ ^ 2 * (C' * ‖y - z p‖ ^ 2 + δ k) ^ (-(n : ℝ)))
        ≤ ∫⁻ y in ball (z p) ρ, ENNReal.ofReal c₀⁻¹ * f' (e.symm y) := by
          refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
          have hs : e.symm y ∈ e.source := e.map_target (hball hy)
          rw [hf', Set.indicator_of_mem hs, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc₀.le)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h2 := hlow k y hy
          have h3 : (C' * ‖y - z p‖ ^ 2 + δ k) ^ (-(n : ℝ)) ≤ c₀⁻¹ * w k (e.symm y) := by
            rw [le_inv_mul_iff₀ hc₀]; exact h2
          calc ‖u k (e.symm y)‖ ^ 2 * (C' * ‖y - z p‖ ^ 2 + δ k) ^ (-(n : ℝ))
              ≤ ‖u k (e.symm y)‖ ^ 2 * (c₀⁻¹ * w k (e.symm y)) :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = _ := by ring
      _ = ENNReal.ofReal c₀⁻¹ * ∫⁻ y in ball (z p) ρ, f' (e.symm y) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c₀⁻¹ * ∫⁻ y in e.target, f' (e.symm y) := by
          gcongr
      _ = ENNReal.ofReal c₀⁻¹ * ∫⁻ x, f' x ∂vol n z := by rw [hchart]
      _ ≤ ENNReal.ofReal c₀⁻¹ * ENNReal.ofReal Cb := by
          gcongr
          refine (lintegral_mono fun x => ?_).trans (hint k)
          exact Set.indicator_le_self _ _ x
      _ = ENNReal.ofReal (c₀⁻¹ * Cb) := (ENNReal.ofReal_mul (inv_nonneg.mpr hc₀.le)).symm

theorem fx_exists_ball_bounds {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph ph2 : M → ℝ)
    (hph : SmoothR n z ph) (hph2 : SmoothR n z ph2) (r : ℝ) (hr : 0 < r) (j : ℕ) (ε : ℝ)
    (hε : 0 < ε) (p : M) (hp : p ∈ zeroSet n g) (U : Set M) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ p ∈ e.source ∧
      ∃ ρ > 0, ∃ C1 > 0, ∃ A : ℝ, ball (z p) ρ ⊆ e.target ∧ ∀ y ∈ ball (z p) ρ,
        e.symm y ∈ U ∧ ev n g ph r (e.symm y) ≤ ε ^ 2 / 2 ∧
        ev n g ph r (e.symm y) ≤ C1 * ‖y - z p‖ ^ 2 ∧
        ph2 (e.symm y) + ((n : ℝ) + j) * ph (e.symm y) ≤ A := by
  obtain ⟨e, he, hpe⟩ := exists_chart n z hz p
  have hzp : z p ∈ e.target := by rw [he hpe]; exact e.map_source hpe
  have hsp : e.symm (z p) = p := by rw [he hpe]; exact e.left_inv hpe
  have hcs : ContinuousAt e.symm (z p) := e.continuousAt_symm hzp
  have hre : ∀ f : M → ℝ, SmoothR n z f → Continuous f := fun f hf =>
    (Complex.continuous_re.comp (Smooth.continuous n z hz _ hf)).congr fun x => by simp
  have hev0 : ev n g ph r p = 0 := fx_ev_eq_zero n g ph r p hp

  have hlip : ∀ i, ∃ c : ℝ, ∀ᶠ y in 𝓝 (z p), ‖g i (e.symm y)‖ ≤ c * ‖y - z p‖ := by
    intro i
    have hd : DifferentiableAt ℂ (fun y => g i (e.symm y)) (z p) :=
      (hg i e he).differentiableAt (e.open_target.mem_nhds hzp)
    obtain ⟨c, hc⟩ := hd.hasFDerivAt.isBigO_sub.bound
    refine ⟨c, hc.mono fun y hy => ?_⟩
    have h0 : g i (e.symm (z p)) = 0 := by rw [hsp]; exact hp i
    simpa [h0] using hy
  choose c hc using hlip
  have h1 : ∀ᶠ y in 𝓝 (z p), y ∈ e.target := e.open_target.mem_nhds hzp
  have h2 : ∀ᶠ y in 𝓝 (z p), e.symm y ∈ U := hcs.preimage_mem_nhds (by rw [hsp]; exact hU.mem_nhds hpU)
  have hevc : ContinuousAt (fun y => ev n g ph r (e.symm y)) (z p) :=
    (fx_continuous_ev n z hz g hg ph hph r).continuousAt.comp hcs
  have h3 : ∀ᶠ y in 𝓝 (z p), ev n g ph r (e.symm y) < ε ^ 2 / 2 := by
    refine hevc.eventually (gt_mem_nhds ?_)
    show ev n g ph r (e.symm (z p)) < _
    rw [hsp, hev0]; positivity
  have hψc : ContinuousAt (fun y => ph2 (e.symm y) + ((n : ℝ) + j) * ph (e.symm y)) (z p) :=
    (((hre _ hph2).add (continuous_const.mul (hre _ hph))).continuousAt).comp hcs
  have h4 : ∀ᶠ y in 𝓝 (z p), ph2 (e.symm y) + ((n : ℝ) + j) * ph (e.symm y) <
      ph2 p + ((n : ℝ) + j) * ph p + 1 := by
    refine hψc.eventually (gt_mem_nhds ?_)
    simp only [hsp]; linarith
  have hxc : ContinuousAt (fun y => Real.exp (-ph (e.symm y))) (z p) :=
    ((Real.continuous_exp.comp (hre _ hph).neg).continuousAt).comp hcs
  have h5 : ∀ᶠ y in 𝓝 (z p), Real.exp (-ph (e.symm y)) < Real.exp (-ph p) + 1 := by
    refine hxc.eventually (gt_mem_nhds ?_)
    simp only [hsp]; linarith
  have h6 : ∀ᶠ y in 𝓝 (z p), ∀ i, ‖g i (e.symm y)‖ ≤ c i * ‖y - z p‖ :=
    Filter.eventually_all.2 hc
  obtain ⟨ρ, hρ, hall⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and (h2.and (h3.and (h4.and (h5.and h6)))))
  set C1 : ℝ := (∑ i, c i ^ 2) * (Real.exp (-ph p) + 1) / r ^ 2 + 1 with hC1
  have hC1pos : 0 < C1 := by positivity
  refine ⟨e, he, hpe, ρ, hρ, C1, hC1pos, ph2 p + ((n : ℝ) + j) * ph p + 1,
    fun y hy => (hall y hy).1, fun y hy => ?_⟩
  obtain ⟨-, hU', h3', h4', h5', h6'⟩ := hall y hy
  refine ⟨hU', h3'.le, ?_, h4'.le⟩
  have hs : ∑ i, ‖g i (e.symm y)‖ ^ 2 ≤ (∑ i, c i ^ 2) * ‖y - z p‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h6' i) 2
  have hr2 : 0 < r ^ 2 := by positivity
  unfold ev
  rw [div_le_iff₀ hr2]
  have hsum0 : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc (∑ i, ‖g i (e.symm y)‖ ^ 2) * Real.exp (-ph (e.symm y))
      ≤ ((∑ i, c i ^ 2) * ‖y - z p‖ ^ 2) * (Real.exp (-ph p) + 1) :=
        mul_le_mul hs h5'.le (Real.exp_pos _).le (by positivity)
    _ ≤ C1 * ‖y - z p‖ ^ 2 * r ^ 2 := by
        rw [hC1, add_mul, add_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_cancel_right₀ _ hr2.ne']
        nlinarith [sq_nonneg ‖y - z p‖, sq_nonneg r, mul_nonneg hsum0 (sq_nonneg ‖y - z p‖)]

end

end ReciprocityTheory.L2DbarEstimates.I
end

section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

theorem fx_lp_norm_sq_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (v : Lp ℂ 2 μ)
    (G : α → ℂ) (h : (v : α → ℂ) =ᵐ[μ] G) :
    eLpNorm G 2 μ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [eLpNorm_congr_ae h.symm, Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top v), ENNReal.rpow_two]

theorem fx_exists_holo_limit {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (n : ℕ) (X : EtaleStein n M) (ps : M → ℝ) (hps : SmoothR n X.z ps)
    (hC : HoloClosedNeed n M) (hE : EvalNeed n M) (hCVX : CVXNeed.{u})
    (S : Set M) (hS : S.Finite) (a : M → ℂ) (B : ℝ) (hB0 : 0 ≤ B)
    (F : ℕ → M → ℂ) (hF : ∀ k, Holo n X.z (F k))
    (hB : ∀ k, wint n X.z (F k) ps ≤ ENNReal.ofReal B)
    (hlim : ∀ p ∈ S, Tendsto (fun k => F k p) atTop (𝓝 (a p))) :
    ∃ G : M → ℂ, Holo n X.z G ∧ (∀ p ∈ S, G p = a p) ∧ wint n X.z G ps ≤ ENNReal.ofReal B := by
  have hz := X.isLocalHomeomorph
  have hpsc : Continuous ps := by
    have := Complex.continuous_re.comp (Smooth.continuous n X.z hz _ hps)
    exact this.congr fun x => by simp
  set μ : Measure M := (vol n X.z).withDensity (fun x => ENNReal.ofReal (Real.exp (-ps x)))
    with hμ
  have hkey : ∀ f : M → ℂ, wint n X.z f ps = eLpNorm f 2 μ ^ (2 : ℝ) := fun f => by
    rw [fx_wint_eq_withDensity n X.z ps hpsc.measurable f, fx_lintegral_enorm_sq_eq]
  have hN : ∀ (v : Lp ℂ 2 μ) (G : M → ℂ), (v : M → ℂ) =ᵐ[μ] G →
      wint n X.z G ps = ENNReal.ofReal (‖v‖ ^ 2) := fun v G h => by
    rw [hkey, fx_lp_norm_sq_eq μ v G h]
  have hcont : ∀ G : M → ℂ, Holo n X.z G → Continuous G := fun G hG =>
    Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hG)

  have hEv : ∀ p ∈ S, ∃ C : ℝ, 0 ≤ C ∧ ∀ (G₁ G₂ : M → ℂ), Holo n X.z G₁ → Holo n X.z G₂ →
      ∀ w : Lp ℂ 2 μ, (w : M → ℂ) =ᵐ[μ] (fun x => G₁ x - G₂ x) → ‖G₁ p - G₂ p‖ ≤ C * ‖w‖ := by
    intro p _
    obtain ⟨C, hC⟩ := hE X ps p hps
    refine ⟨Real.sqrt (max C 0), Real.sqrt_nonneg _, fun G₁ G₂ h₁ h₂ w hw => ?_⟩
    have h := hC _ (Holo.sub n X.z _ _ h₁ h₂)
    rw [hN w _ hw] at h
    have h' : ENNReal.ofReal (‖G₁ p - G₂ p‖ ^ 2) ≤ ENNReal.ofReal (max C 0 * ‖w‖ ^ 2) := by
      rw [ENNReal.ofReal_mul (le_max_right _ _)]
      exact h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h'
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow,
      Real.sq_sqrt (le_max_right _ _)]
    exact h'
  choose! Cev hCev0 hCev using hEv
  have hmem : ∀ k, MemLp (F k) 2 μ := fun k => by
    refine ⟨(hcont _ (hF k)).aestronglyMeasurable, ?_⟩
    have h := ((hkey (F k)).symm.trans_le (hB k)).trans_lt ENNReal.ofReal_lt_top
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp h
  let K : ℕ → Set (Lp ℂ 2 μ) := fun m => {v | ∃ G : M → ℂ, Holo n X.z G ∧
    (v : M → ℂ) =ᵐ[μ] G ∧ ‖v‖ ^ 2 ≤ B + 1 / ((m : ℝ) + 1) ∧
    ∀ p ∈ S, ‖G p - a p‖ ≤ 1 / ((m : ℝ) + 1)}
  have hanti : Antitone K := by
    intro m₁ m₂ h v hv
    obtain ⟨G, hG, hvG, hn, hp⟩ := hv
    have : 1 / ((m₂ : ℝ) + 1) ≤ 1 / ((m₁ : ℝ) + 1) := by
      gcongr
    exact ⟨G, hG, hvG, hn.trans (by linarith), fun p hp' => (hp p hp').trans this⟩
  have hne : ∀ m, (K m).Nonempty := by
    intro m
    have hev : ∀ᶠ k in atTop, ∀ p ∈ S, ‖F k p - a p‖ ≤ 1 / ((m : ℝ) + 1) := by
      refine (Filter.eventually_all_finite hS).2 fun p hp => ?_
      have := (Metric.tendsto_nhds.mp (hlim p hp)) (1 / ((m : ℝ) + 1)) (by positivity)
      filter_upwards [this] with k hk
      rw [← dist_eq_norm]; exact hk.le
    obtain ⟨k, hk⟩ := hev.exists
    refine ⟨(hmem k).toLp (F k), F k, hF k, MemLp.coeFn_toLp _, ?_, hk⟩
    have h := (hN ((hmem k).toLp (F k)) (F k) (MemLp.coeFn_toLp (hmem k))).symm.trans_le (hB k)
    rw [ENNReal.ofReal_le_ofReal_iff hB0] at h
    have : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
    linarith
  have hclosed : ∀ m, IsClosed (K m) := by
    intro m
    refine IsSeqClosed.isClosed fun vs v hvs hlimv => ?_
    have hvs' : ∀ i, ∃ G : M → ℂ, Holo n X.z G ∧
        (vs i : M → ℂ) =ᵐ[μ] G ∧ ‖vs i‖ ^ 2 ≤ B + 1 / ((m : ℝ) + 1) ∧
        ∀ p ∈ S, ‖G p - a p‖ ≤ 1 / ((m : ℝ) + 1) := hvs
    choose G hG hvG hnG hpG using hvs'
    have hvm : Measurable (v : M → ℂ) := (Lp.stronglyMeasurable v).measurable
    have hd : ∀ i, (⇑(vs i - v) : M → ℂ) =ᵐ[μ] fun x => G i x - (v : M → ℂ) x := fun i => by
      filter_upwards [Lp.coeFn_sub (vs i) v, hvG i] with x h1 h2
      rw [h1, Pi.sub_apply, h2]
    have hlim0 : Tendsto (fun i => ‖vs i - v‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hlimv
    have hw : Tendsto (fun i => wint n X.z (fun x => G i x - (v : M → ℂ) x) ps) atTop (𝓝 0) := by
      have he : (fun i => wint n X.z (fun x => G i x - (v : M → ℂ) x) ps) =
          fun i => ENNReal.ofReal (‖vs i - v‖ ^ 2) := funext fun i => hN _ _ (hd i)
      rw [he]
      have : Tendsto (fun i => ENNReal.ofReal (‖vs i - v‖ ^ 2)) atTop
          (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ 2))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp (hlim0.pow 2)
      simpa using this
    obtain ⟨Gl, hGl, hfG⟩ := hC X ps G (v : M → ℂ) hps hG hvm hw
    have hvGl : (v : M → ℂ) =ᵐ[μ] Gl := (withDensity_absolutelyContinuous _ _).ae_le hfG
    refine ⟨Gl, hGl, hvGl, ?_, fun p hp => ?_⟩
    · exact le_of_tendsto (((continuous_norm.tendsto v).comp hlimv).pow 2)
        (Eventually.of_forall hnG)
    · have hd2 : ∀ i, (⇑(vs i - v) : M → ℂ) =ᵐ[μ] fun x => G i x - Gl x := fun i => by
        filter_upwards [hd i, hvGl] with x h1 h2
        rw [h1, h2]
      have hb : ∀ i, ‖Gl p - a p‖ ≤ Cev p * ‖vs i - v‖ + 1 / ((m : ℝ) + 1) := fun i => by
        have h1 := hCev p hp (G i) Gl (hG i) hGl _ (hd2 i)
        calc ‖Gl p - a p‖ ≤ ‖Gl p - G i p‖ + ‖G i p - a p‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ = ‖G i p - Gl p‖ + ‖G i p - a p‖ := by rw [norm_sub_rev (Gl p)]
          _ ≤ _ := add_le_add h1 (hpG i p hp)
      have ht : Tendsto (fun i => Cev p * ‖vs i - v‖ + 1 / ((m : ℝ) + 1)) atTop
          (𝓝 (Cev p * 0 + 1 / ((m : ℝ) + 1))) := (hlim0.const_mul _).add_const _
      simpa using ge_of_tendsto' ht hb
  have hmid : ∀ m, ∀ v ∈ K m, ∀ w ∈ K m, (2 : ℂ)⁻¹ • (v + w) ∈ K m := by
    rintro m v ⟨G, hG, hvG, hnv, hpv⟩ w ⟨G', hG', hwG, hnw, hpw⟩
    refine ⟨fun x => (2 : ℂ)⁻¹ * (G x + G' x),
      Holo.mul n X.z _ _ (Holo.const n X.z _) (Holo.add n X.z _ _ hG hG'), ?_, ?_, fun p hp => ?_⟩
    · filter_upwards [Lp.coeFn_smul (2 : ℂ)⁻¹ (v + w), Lp.coeFn_add v w, hvG, hwG]
        with x h1 h2 h3 h4
      rw [h1, Pi.smul_apply, h2, Pi.add_apply, h3, h4, smul_eq_mul]
    · have h1 : ‖(2 : ℂ)⁻¹ • (v + w)‖ ≤ (‖v‖ + ‖w‖) / 2 := by
        rw [norm_smul, norm_inv, Complex.norm_two]
        have := norm_add_le v w
        linarith
      have h0 : 0 ≤ ‖(2 : ℂ)⁻¹ • (v + w)‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖v‖ - ‖w‖), mul_le_mul h1 h1 h0 (by positivity),
        norm_nonneg v, norm_nonneg w]
    · calc ‖(2 : ℂ)⁻¹ * (G p + G' p) - a p‖ = ‖(2 : ℂ)⁻¹ * ((G p - a p) + (G' p - a p))‖ := by
            congr 1; ring
        _ ≤ 2⁻¹ * (‖G p - a p‖ + ‖G' p - a p‖) := by
            rw [norm_mul, norm_inv, Complex.norm_two]
            exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
        _ ≤ 1 / ((m : ℝ) + 1) := by linarith [hpv p hp, hpw p hp]
  have hbdd : Bornology.IsBounded (K 0) := by
    refine (Metric.isBounded_closedBall (x := (0 : Lp ℂ 2 μ)) (r := B + 2)).subset ?_
    rintro v ⟨G, -, -, hn, -⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    norm_num at hn
    nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - 1)]
  obtain ⟨v, hv⟩ := hCVX (Lp ℂ 2 μ) K hanti hne hclosed hmid hbdd
  obtain ⟨G, hG, hvG, -, -⟩ := hv 0
  refine ⟨G, hG, fun p hp => ?_, ?_⟩
  · have hb : ∀ m : ℕ, ‖G p - a p‖ ≤ 1 / ((m : ℝ) + 1) := fun m => by
      obtain ⟨G', hG', hvG', -, hp'⟩ := hv m
      have h0 : (⇑(0 : Lp ℂ 2 μ) : M → ℂ) =ᵐ[μ] fun x => G x - G' x := by
        filter_upwards [Lp.coeFn_zero ℂ 2 μ, hvG, hvG'] with x h1 h2 h3
        rw [h1, Pi.zero_apply, ← h2, ← h3, sub_self]
      have h1 := hCev p hp G G' hG hG' 0 h0
      rw [norm_zero, mul_zero] at h1
      calc ‖G p - a p‖ ≤ ‖G p - G' p‖ + ‖G' p - a p‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 0 + 1 / ((m : ℝ) + 1) := add_le_add h1 (hp' p hp)
        _ = _ := zero_add _
    have h := ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat hb
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  · rw [hN v G hvG]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb : ∀ m : ℕ, ‖v‖ ^ 2 ≤ B + 1 / ((m : ℝ) + 1) := fun m => (hv m).choose_spec.2.2.1
    have ht : Tendsto (fun m : ℕ => B + 1 / ((m : ℝ) + 1)) atTop (𝓝 (B + 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.const_add B
    simpa using ge_of_tendsto' ht hb

end

end ReciprocityTheory.L2DbarEstimates.I
end

section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

theorem fx_ev_nonneg {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (x : M) :
    0 ≤ ev n g ph r x := by
  unfold ev; positivity

theorem fx_exp_neg_wgt {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph ph2 : M → ℝ) (r : ℝ) (j : ℕ)
    (δ : ℝ) (x : M) (h : 0 < ev n g ph r x + δ ^ 2) :
    Real.exp (-wgt n g ph ph2 r j δ x) =
      Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * (ev n g ph r x + δ ^ 2) ^ (-(n : ℝ)) := by
  unfold wgt lw
  rw [Real.rpow_def_of_pos h, ← Real.exp_add]
  congr 1; ring

theorem fx_exp_neg_wgt_le_shell {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph ph2 : M → ℝ) (r : ℝ)
    (j : ℕ) (ε δ : ℝ) (hε : 0 < ε) (x : M) (hx : ε ^ 2 / 2 ≤ ev n g ph r x) :
    Real.exp (-wgt n g ph ph2 r j δ x) ≤
      Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ)) := by
  have ht : 0 < ev n g ph r x := lt_of_lt_of_le (by positivity) hx
  rw [fx_exp_neg_wgt n g ph ph2 r j δ x (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact Real.rpow_le_rpow_of_nonpos ht (by nlinarith [sq_nonneg δ])
    (neg_nonpos.mpr (Nat.cast_nonneg n))

theorem fx_denom_bounds {M : Type*} (n : ℕ) (hB : BasicStatement n M) (g : Fin n → M → ℂ)
    (ph ph2 : M → ℝ) (r : ℝ) (j : ℕ) (ε : ℝ) (hr : 0 < r) (hε : 0 < ε)
    (hbound : ∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) :
    ∃ Dm > 0, ∀ x, 0 < (xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x ∧
      (xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x ≤ Dm := by
  obtain ⟨h1, ⟨Ct, hCt⟩, -, -⟩ := hB g ph ph2 r j ε ε hr hε hbound
  refine ⟨(Real.exp Ct + 1) ^ 2 + Real.exp Ct, by positivity, fun x => ?_⟩
  obtain ⟨hx1, hη1, -, -⟩ := h1 x
  have hlog : Real.log (eta n g ph r ε x) ≤ Ct := by
    have := hCt x
    unfold twist at this
    rw [abs_neg] at this
    exact (le_abs_self _).trans this
  have hηle : eta n g ph r ε x ≤ Real.exp Ct :=
    (Real.log_le_iff_le_exp (by linarith)).mp hlog
  have hxη : xx n g ph r ε x ≤ eta n g ph r ε x := by
    unfold eta
    have := Real.log_nonneg hx1
    linarith
  refine ⟨by positivity, ?_⟩
  have h2 : xx n g ph r ε x + 1 ≤ Real.exp Ct + 1 := by linarith
  have h3 : 0 ≤ xx n g ph r ε x + 1 := by linarith
  nlinarith [mul_le_mul h2 h2 h3 (by positivity)]

theorem fixed (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    (hA : ApplyStatement n M) (hB : BasicStatement n M) (hV : VanishStatement n)
    (hC : HoloClosedNeed n M) (hE : EvalNeed n M) (hCVX : CVXNeed.{u}) : FixedStatement n M := by
  intro X g ph ph2 r j c W m χ ε hn hg hph hlph hph2 hlph2 hr hj hbound hS hJ hL hχ hε hε50 hm
  have hz := X.isLocalHomeomorph
  have hre : ∀ f : M → ℝ, SmoothR n X.z f → Continuous f := fun f hf =>
    (Complex.continuous_re.comp (Smooth.continuous n X.z hz _ hf)).congr fun x => by simp
  have hphc := hre ph hph
  have hph2c := hre ph2 hph2
  have hevc := fx_continuous_ev n X.z hz g hg ph hph r
  have hJc := fx_continuous_jac n X.z hz g hg
  have hψ₀s : SmoothR n X.z (fun x => ph2 x + ((n : ℝ) + j) * ph x) :=
    SmoothR.add n X.z _ _ hph2 (SmoothR.mul n X.z _ _ (smoothR_const n X.z _) hph)
  have hψ₀c : Continuous (fun x => ph2 x + ((n : ℝ) + j) * ph x) :=
    hph2c.add (continuous_const.mul hphc)
  have hF0m : Measurable (cutExt n X.z g ph r c W χ ε) :=
    fx_measurable_cutExt n X.z hz g hg ph hph r c W m χ hχ ε hS hL
  have hshm : MeasurableSet (shell n g ph r ε) :=
    ((isClosed_le continuous_const hevc).inter (isClosed_le hevc continuous_const)).measurableSet
  have := vol_isFiniteMeasureOnCompacts n X.z hz
  have hKc : IsCompact (⋃ q ∈ zeroSet n g, closure (W q)) :=
    hS.isCompact_biUnion fun q hq => (hL.2 q hq).2.2.1
  set s0 : ℝ := ∑ q ∈ hS.toFinset, ‖c q‖ with hs0
  have hgt_le : ∀ x, ‖gt n X.z g c W x‖ ≤ s0 * ‖jac n X.z g x‖ := fun x => by
    rw [hs0, Finset.sum_mul]; exact fx_norm_gt_le n X.z g c W hS x
  set G := ∫⁻ x in shell n g ph r ε, ENNReal.ofReal (‖gt n X.z g c W x‖ ^ 2 *
      Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) ∂vol n X.z with hG
  have hGfin : G < ⊤ := by
    rw [hG, ← lintegral_indicator hshm]
    refine fx_lintegral_lt_top_of_le_indicator _ _ hKc
      (fun x => (s0 * ‖jac n X.z g x‖) ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) *
        (ε ^ 2 / 2) ^ (-(n : ℝ))) (by fun_prop) _ fun x => ?_
    by_cases hxs : x ∈ shell n g ph r ε
    · rw [indicator_of_mem hxs]
      by_cases hxK : x ∈ ⋃ q ∈ zeroSet n g, closure (W q)
      · rw [indicator_of_mem hxK]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : ‖gt n X.z g c W x‖ ^ 2 ≤ (s0 * ‖jac n X.z g x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hgt_le x) 2
        have h2 : ev n g ph r x ^ (-(n : ℝ)) ≤ (ε ^ 2 / 2) ^ (-(n : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hxs.1 (neg_nonpos.mpr (Nat.cast_nonneg n))
        exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) h2
          (Real.rpow_nonneg (fx_ev_nonneg n g ph r x) _) (by positivity)
      · rw [fx_gt_eq_zero n X.z g c W hS x hxK]; simp
    · rw [indicator_of_notMem hxs]; exact bot_le
  have hF0fin : otNorm n X.z ph ph2 j (cutExt n X.z g ph r c W χ ε) < ⊤ := by
    unfold otNorm
    refine fx_lintegral_lt_top_of_le_indicator _ _ hKc
      (fun x => (s0 * ‖jac n X.z g x‖) ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x))
      (by fun_prop) _ fun x => ?_
    by_cases hxK : x ∈ ⋃ q ∈ zeroSet n g, closure (W q)
    · rw [indicator_of_mem hxK]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((fx_norm_cutExt_le n X.z g ph r c W χ hχ ε x).trans (hgt_le x)) 2
    · have : cutExt n X.z g ph r c W χ ε x = 0 := by
        unfold cutExt; rw [fx_gt_eq_zero n X.z g c W hS x hxK, mul_zero]
      rw [this]; simp
  set κ' : ℝ := 2 * Real.exp 1 * (1 + ε ^ 2) ^ n with hκ'
  have hκ'pos : 0 < κ' := by positivity
  set δ : ℕ → ℝ := fun k => ε / ((k : ℝ) + 2) with hδ
  have hδpos : ∀ k, 0 < δ k := fun k => by simp only [hδ]; positivity
  have hδle : ∀ k, δ k ≤ ε := fun k => by
    simp only [hδ]
    exact div_le_self hε.le (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hApp := fun k => hA X g ph ph2 r j c W m χ ε (δ k) hg hph hlph hph2 hlph2 hr hj hbound hS
    hJ hL hχ hε hε50 hm (hδpos k) (hδle k)
  choose Fk hFk hFkb using hApp
  have hFkm : ∀ k, Measurable (Fk k) := fun k =>
    (Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ (hFk k))).measurable
  have hshell : ∀ k, ∫⁻ x in shell n g ph r ε, ENNReal.ofReal (‖gt n X.z g c W x‖ ^ 2 *
      Real.exp (-wgt n g ph ph2 r j (δ k) x)) ∂vol n X.z ≤ G := by
    intro k
    refine setLIntegral_mono' hshm fun x hx => ENNReal.ofReal_le_ofReal ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (fx_exp_neg_wgt_le_shell n g ph ph2 r j ε (δ k) hε x hx.1)
      (sq_nonneg _)
  have hdiff : ∀ k, otNorm n X.z ph ph2 j (fun x => cutExt n X.z g ph r c W χ ε x - Fk k x) ≤
      ENNReal.ofReal (κ' * 72) * G := by
    intro k
    have h4 := (hB g ph ph2 r j ε (δ k) hr hε hbound).2.2.2 hn (hδpos k) (hδle k)
    calc otNorm n X.z ph ph2 j (fun x => cutExt n X.z g ph r c W χ ε x - Fk k x)
        ≤ ∫⁻ x, ENNReal.ofReal κ' * ENNReal.ofReal (‖cutExt n X.z g ph r c W χ ε x - Fk k x‖ ^ 2 *
            (Real.exp (-wgt n g ph ph2 r j (δ k) x) /
              ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))) ∂vol n X.z := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul hκ'pos.le]
          refine ENNReal.ofReal_le_ofReal ?_
          calc _ ≤ ‖cutExt n X.z g ph r c W χ ε x - Fk k x‖ ^ 2 *
                (κ' * (Real.exp (-wgt n g ph ph2 r j (δ k) x) /
                  ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))) :=
                mul_le_mul_of_nonneg_left (h4 x) (sq_nonneg _)
            _ = _ := by ring
      _ = ENNReal.ofReal κ' * ∫⁻ x, ENNReal.ofReal (‖cutExt n X.z g ph r c W χ ε x - Fk k x‖ ^ 2 *
            (Real.exp (-wgt n g ph ph2 r j (δ k) x) /
              ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))) ∂vol n X.z :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal κ' * (72 * G) := by
          gcongr
          exact (hFkb k).trans (by gcongr; exact hshell k)
      _ = ENNReal.ofReal (κ' * 72) * G := by
          rw [ENNReal.ofReal_mul hκ'pos.le, ENNReal.ofReal_ofNat, mul_assoc]
  set B := ((ENNReal.ofReal (κ' * 72) * G) ^ (1 / 2 : ℝ) +
    otNorm n X.z ph ph2 j (cutExt n X.z g ph r c W χ ε) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) with hBdef
  have hBfin : B ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.add_ne_top.2 ⟨?_, ?_⟩)
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGfin.ne)
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hF0fin.ne
  set μ : Measure M := (vol n X.z).withDensity
    (fun x => ENNReal.ofReal (Real.exp (-(ph2 x + ((n : ℝ) + j) * ph x)))) with hμ
  have hot : ∀ f : M → ℂ, otNorm n X.z ph ph2 j f = eLpNorm f 2 μ ^ (2 : ℝ) := fun f => by
    rw [fx_otNorm_eq_wint, fx_wint_eq_withDensity n X.z _ hψ₀c.measurable f, fx_lintegral_enorm_sq_eq]
  have hsq : ∀ f : M → ℂ, eLpNorm f 2 μ = otNorm n X.z ph ph2 j f ^ (1 / 2 : ℝ) := fun f => by
    rw [hot, ← ENNReal.rpow_mul]; norm_num
  have hFkB : ∀ k, otNorm n X.z ph ph2 j (Fk k) ≤ B := by
    intro k
    have htri : eLpNorm (Fk k) 2 μ ≤ eLpNorm (cutExt n X.z g ph r c W χ ε) 2 μ +
        eLpNorm (cutExt n X.z g ph r c W χ ε - Fk k) 2 μ := by
      have := eLpNorm_sub_le (p := 2) (μ := μ) hF0m.aestronglyMeasurable
        (hF0m.sub (hFkm k)).aestronglyMeasurable one_le_two
      convert this using 2
      funext x; simp
    rw [hot, hBdef]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [hsq (cutExt n X.z g ph r c W χ ε), hsq (cutExt n X.z g ph r c W χ ε - Fk k)] at htri
    refine htri.trans ?_
    rw [add_comm]
    gcongr
    exact hdiff k
  have hevm : Measurable (ev n g ph r) := hevc.measurable
  have hlwm : ∀ t, Measurable (lw n g ph r t) := fun t => by
    unfold lw; exact (hevm.add_const _).log
  have hxxm : Measurable (xx n g ph r ε) := by
    unfold xx; exact measurable_const.sub (hlwm ε)
  have hetam : Measurable (eta n g ph r ε) := by
    unfold eta; exact hxxm.add hxxm.log
  have hwm : ∀ k, Measurable fun x => Real.exp (-wgt n g ph ph2 r j (δ k) x) /
      ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x) := fun k => by
    have : Measurable (wgt n g ph ph2 r j (δ k)) := by
      unfold wgt
      exact (hph2c.measurable.add (measurable_const.mul hphc.measurable)).add
        (measurable_const.mul (hlwm (δ k)))
    exact (Real.measurable_exp.comp this.neg).div (((hxxm.add_const 1).pow_const 2).add hetam)
  obtain ⟨Dm, hDm, hD⟩ := fx_denom_bounds n hB g ph ph2 r j ε hr hε hbound
  have hlim : ∀ p ∈ zeroSet n g, Tendsto (fun k => Fk k p) atTop (𝓝 (c p * jac n X.z g p)) := by
    intro p hp
    obtain ⟨e, he, hpe, ρ, hρ, C1, hC1, A, hball, hbb⟩ := fx_exists_ball_bounds n X.z hz g hg ph ph2
      hph hph2 r hr j ε hε p hp (W p) (hL.2 p hp).1 (hL.2 p hp).2.1
    have hF0p : cutExt n X.z g ph r c W χ ε p = c p * jac n X.z g p :=
      fx_cutExt_eq_of_mem n X.z g ph r c W m χ hχ ε hε hS hL p hp p (hL.2 p hp).2.1
        (by rw [fx_ev_eq_zero n g ph r p hp]; positivity)
    have hδ2 : Tendsto (fun k => δ k ^ 2) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
      · simpa using hδlim.pow 2
      · exact pow_pos (hδpos k) 2
    have key := fx_tendsto_zero_of_weighted n hn hV X.z hz e he p hpe ρ hρ hball
      (Real.exp (-A) / Dm) C1 (72 * G.toReal) (by positivity) hC1 (fun k => δ k ^ 2) hδ2
      (fun k x => cutExt n X.z g ph r c W χ ε x - Fk k x)
      (fun k x => Real.exp (-wgt n g ph ph2 r j (δ k) x) /
        ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))
      (fun k => hF0m.sub (hFkm k)) hwm ?_ ?_ ?_
    · have := key.const_sub (c p * jac n X.z g p)
      simpa [hF0p] using this
    · intro k
      have h1 : DifferentiableOn ℂ (fun y => c p * jac n X.z g (e.symm y) - Fk k (e.symm y))
          (ball (X.z p) ρ) :=
        (((fx_differentiableOn_jac_chart n X.z g hg e he).mono hball).const_mul (c p)).sub
          ((hFk k e he).mono hball)
      refine h1.congr fun y hy => ?_
      obtain ⟨hU, hev, -, -⟩ := hbb y hy
      show cutExt n X.z g ph r c W χ ε (e.symm y) - Fk k (e.symm y) = _
      rw [fx_cutExt_eq_of_mem n X.z g ph r c W m χ hχ ε hε hS hL p hp _ hU hev]
    · intro k y hy
      obtain ⟨-, -, hevC, hψA⟩ := hbb y hy
      have hDx := hD (e.symm y)
      have hpos : 0 < ev n g ph r (e.symm y) + δ k ^ 2 := by
        have := fx_ev_nonneg n g ph r (e.symm y); have := hδpos k; positivity
      rw [fx_exp_neg_wgt n g ph ph2 r j (δ k) _ hpos]
      have h1 : (C1 * ‖y - X.z p‖ ^ 2 + δ k ^ 2) ^ (-(n : ℝ)) ≤
          (ev n g ph r (e.symm y) + δ k ^ 2) ^ (-(n : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hpos (by linarith) (neg_nonpos.mpr (Nat.cast_nonneg n))
      have h2 : Real.exp (-A) ≤ Real.exp (-ph2 (e.symm y) - ((n : ℝ) + j) * ph (e.symm y)) :=
        Real.exp_le_exp.mpr (by linarith)
      have hR : 0 ≤ (C1 * ‖y - X.z p‖ ^ 2 + δ k ^ 2) ^ (-(n : ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hDm hDx.1]
      exact mul_le_mul (mul_le_mul h2 h1 hR (Real.exp_pos _).le) hDx.2 hDx.1.le
        (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hpos.le _))
    · intro k
      refine (hFkb k).trans ?_
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hGfin.ne, ENNReal.ofReal_ofNat]
      gcongr
      exact hshell k
  obtain ⟨Fl, hFl, hFlp, hFlB⟩ := fx_exists_holo_limit n X _ hψ₀s hC hE hCVX (zeroSet n g) hS
    (fun p => c p * jac n X.z g p) B.toReal ENNReal.toReal_nonneg Fk hFk
    (fun k => by rw [← fx_otNorm_eq_wint, ENNReal.ofReal_toReal hBfin]; exact hFkB k) hlim
  refine ⟨Fl, hFl, hFlp, ?_⟩
  rw [fx_otNorm_eq_wint]
  exact hFlB.trans (ENNReal.ofReal_toReal hBfin).le

end

end ReciprocityTheory.L2DbarEstimates.I
end
