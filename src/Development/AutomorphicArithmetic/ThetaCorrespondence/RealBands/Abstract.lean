import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvEig
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvAssoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BandCc
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand

section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

private theorem exists_compact_tail {G : Type} [TopologicalSpace G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (f : G → ℂ)
    (hf : Integrable f μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : Set G, IsCompact D ∧ ∫ g, Dᶜ.indicator (fun g => ‖f g‖) g ∂μ ≤ ε := by
  have hm : ∀ n, MeasurableSet (compactCovering G n)ᶜ := fun n =>
    (isCompact_compactCovering G n).isClosed.measurableSet.compl
  have ht : Tendsto (fun n => ∫ g, (compactCovering G n)ᶜ.indicator (fun g => ‖f g‖) g ∂μ) atTop
      (𝓝 (∫ _g, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun g => ‖f g‖)
      (fun n => (hf.norm.indicator (hm n)).aestronglyMeasurable) hf.norm (fun n => ?_) ?_
    · refine Eventually.of_forall fun g => ?_
      simpa using norm_indicator_le_norm_self (s := (compactCovering G n)ᶜ) (fun g => ‖f g‖) g
    · refine Eventually.of_forall fun g => ?_
      obtain ⟨n, hn⟩ := exists_mem_compactCovering g
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n] with m hm'
      have : g ∈ compactCovering G m := compactCovering_subset G hm' hn
      simp [this]
  rw [integral_zero] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds hε)).exists
  exact ⟨_, isCompact_compactCovering G n, hn⟩

private theorem isEig_twist {G : Type} [Group G] [TopologicalSpace G] {N : Set G} {a : ℝ → G} {H : G → ℝ}
    (hr : IsRay N a H) {s s' C : ℝ} {h : G → ℂ} (hh : IsEig N a s' C h) :
    IsEig N a s C (fun g => Complex.exp (Complex.I * (((s - s') * H g : ℝ) : ℂ)) * h g) := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hH := hr.contH
  refine ⟨by fun_prop, fun g => ?_, fun g m hm => ?_, fun g t => ?_⟩
  · rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]; exact h2 g
  · simp only [hr.inv g m hm, h3 g m hm]
  · simp only [hr.move g t, h4 g t]
    rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast
    ring

theorem UpperTheory.Lit.Cusp.opLe_near :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (f : G → ℂ),
      IsRay N a H → Integrable f μ → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s s' r : ℝ, |s - s'| < δ → OpLe μ N a f s r → OpLe μ N a f s' (r + ε) := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H f hr hf ε hε
  obtain ⟨D, hD, hDε⟩ := exists_compact_tail μ f hf (ε / 4) (by positivity)
  obtain ⟨c, hc⟩ := hr.bdd D hD
  have hmD : MeasurableSet Dᶜ := hD.isClosed.measurableSet.compl
  set A : ℝ := ∫ g, ‖f g‖ ∂μ with hA
  have hA0 : 0 ≤ A := integral_nonneg fun g => norm_nonneg _
  set δ : ℝ := ε / 2 / ((|c| + 1) * (A + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδe : δ * ((|c| + 1) * (A + 1)) = ε / 2 := by rw [hδ]; field_simp
  refine ⟨δ, hδ0, fun s s' r hs hop C h hh x => ?_⟩
  have hC : 0 ≤ C := (norm_nonneg _).trans (hh.2.1 1)
  have ht := isEig_twist (s := s) hr hh
  have h1 := hop C _ ht x
  have hint : ∀ {t : ℝ} {k : G → ℂ}, IsEig N a t C k → Integrable (fun g => f g * k (g⁻¹ * x)) μ := by
    intro t k hk
    have hk1 := hk.1
    have hc : Continuous fun g : G => k (g⁻¹ * x) := by fun_prop
    exact hf.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall fun g => hk.2.1 _)
  set u : ℂ := Complex.exp (Complex.I * ((-((s - s') * H x) : ℝ) : ℂ)) with hu
  have hu1 : ‖u‖ = 1 := Complex.norm_exp_I_mul_ofReal _
  set k : G → ℂ := fun g => Complex.exp (Complex.I * (((s - s') * H g : ℝ) : ℂ)) * h g with hk
  have hdiff : u * conv μ f k x - conv μ f h x
      = ∫ g, (u * (f g * k (g⁻¹ * x)) - f g * h (g⁻¹ * x)) ∂μ := by
    rw [integral_sub ((hint ht).const_mul u) (hint hh), integral_const_mul]
    rfl
  have hpt : ∀ g, ‖u * (f g * k (g⁻¹ * x)) - f g * h (g⁻¹ * x)‖
      ≤ C * (δ * (|c| + 1) * ‖f g‖ + 2 * Dᶜ.indicator (fun g => ‖f g‖) g) := by
    intro g
    have e : u * (f g * k (g⁻¹ * x)) - f g * h (g⁻¹ * x)
        = h (g⁻¹ * x) * ((Complex.exp (Complex.I * (((s - s') * (H (g⁻¹ * x) - H x) : ℝ) : ℂ)) - 1) * f g) := by
      have : Complex.exp (Complex.I * (((s - s') * (H (g⁻¹ * x) - H x) : ℝ) : ℂ))
          = u * Complex.exp (Complex.I * (((s - s') * H (g⁻¹ * x) : ℝ) : ℂ)) := by
        rw [hu, ← Complex.exp_add]; congr 1; push_cast; ring
      rw [this, hk]; ring
    rw [e, norm_mul, norm_mul]
    refine mul_le_mul (hh.2.1 _) ?_ (by positivity) hC
    by_cases hg : g ∈ D
    · have h2 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (s - s') * (H (g⁻¹ * x) - H x))
      have h3 : ‖(s - s') * (H (g⁻¹ * x) - H x)‖ ≤ δ * (|c| + 1) := by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul hs.le ((hc g hg x).trans (by linarith [le_abs_self c])) (abs_nonneg _) hδ0.le
      have h4 : Dᶜ.indicator (fun g => ‖f g‖) g = 0 := by simp [hg]
      rw [h4, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_right (h2.trans h3) (norm_nonneg _)
    · have h2 : ‖Complex.exp (Complex.I * (((s - s') * (H (g⁻¹ * x) - H x) : ℝ) : ℂ)) - 1‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_exp_I_mul_ofReal, norm_one]; norm_num
      have h4 : Dᶜ.indicator (fun g => ‖f g‖) g = ‖f g‖ := by simp [hg]
      rw [h4]
      have h5 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (f g))
      have h6 : 0 ≤ δ * (|c| + 1) * ‖f g‖ := by positivity
      linarith
  have hi1 : Integrable (fun g => δ * (|c| + 1) * ‖f g‖) μ := hf.norm.const_mul _
  have hi2 : Integrable (fun g => 2 * Dᶜ.indicator (fun g => ‖f g‖) g) μ :=
    (hf.norm.indicator hmD).const_mul _
  have hb : ‖u * conv μ f k x - conv μ f h x‖ ≤ C * ε := by
    rw [hdiff]
    refine (norm_integral_le_of_norm_le ((hi1.add hi2).const_mul C) (Eventually.of_forall hpt)).trans ?_
    simp only [Pi.add_apply]
    rw [integral_const_mul, integral_add hi1 hi2, integral_const_mul, integral_const_mul, ← hA]
    refine mul_le_mul_of_nonneg_left ?_ hC
    have : 0 ≤ δ * (|c| + 1) := by positivity
    nlinarith
  have h2 : ‖u * conv μ f k x‖ ≤ r * C := by rw [norm_mul, hu1, one_mul]; exact h1
  have h3 : ‖conv μ f h x‖ ≤ ‖u * conv μ f k x‖ + ‖u * conv μ f k x - conv μ f h x‖ := by
    simpa using norm_sub_le (u * conv μ f k x) (u * conv μ f k x - conv μ f h x)
  linarith
end

section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.transl_small :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (f : G → ℂ), Integrable f μ →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ b in 𝓝 (1 : G), ∫ g, ‖f (b * g) - f g‖ ∂μ ≤ ε := by
  intro G _ _ _ _ _ _ _ _ μ _ f hf ε hε
  haveI : Fact ((1 : ENNReal) ≠ ⊤) := ⟨ENNReal.one_ne_top⟩
  have hm : MemLp f 1 μ := memLp_one_iff_integrable.2 hf
  set F : Lp ℂ 1 μ := hm.toLp f with hF
  have hc : Continuous fun b : G => ‖(DomMulAct.mk b) • F - F‖ :=
    ((DomMulAct.continuous_mk.smul continuous_const).sub continuous_const).norm
  have h1 : ‖(DomMulAct.mk (1 : G)) • F - F‖ < ε := by
    have : (DomMulAct.mk (1 : G)) • F = F := one_smul Gᵈᵐᵃ F
    rw [this, sub_self, norm_zero]; exact hε
  have hev := hc.continuousAt.eventually_lt continuousAt_const h1
  filter_upwards [hev] with b hb
  refine le_of_eq_of_le ?_ hb.le
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  have hFf : F =ᵐ[μ] f := hm.coeFn_toLp
  have h2 : (fun g => F (b * g)) =ᵐ[μ] fun g => f (b * g) :=
    (measurePreserving_mul_left μ b).quasiMeasurePreserving.ae_eq_comp hFf
  filter_upwards [Lp.coeFn_sub ((DomMulAct.mk b) • F) F, DomMulAct.smul_Lp_ae_eq (DomMulAct.mk b) F, hFf, h2] with g e1 e2 e3 e4
  rw [e1, Pi.sub_apply, e2, e3, ← e4]
  rfl
end

section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.opLe_half :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (f : G → ℂ),
      IsRay N a H → Integrable f μ → ∃ s : ℝ, OpLe μ N a f s (1 / 2) := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H f hR hf
  have hU := transl_small G μ f hf 1 one_pos
  have a0 : a 0 = 1 := by
    have := hR.add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  obtain ⟨D, hD, hk⟩ := hR.cpt
  have hc : Continuous fun p : ℝ × G => p.2 * a p.1 * p.2⁻¹ :=
    (continuous_snd.mul (hR.cont.comp continuous_fst)).mul continuous_snd.inv
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ k ∈ D, ∫ g, ‖f ((k * a t * k⁻¹) * g) - f g‖ ∂μ ≤ 1 := by
    apply hD.eventually_forall_of_forall_eventually
    intro k _
    have ht : Tendsto (fun p : ℝ × G => p.2 * a p.1 * p.2⁻¹) (𝓝 (0, k)) (𝓝 1) := by
      have := hc.tendsto (0, k)
      simpa [a0] using this
    exact ht.eventually hU
  have hev' : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k ∈ D, ∫ g, ‖f ((k * a t * k⁻¹) * g) - f g‖ ∂μ ≤ 1 :=
    hev.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, htpos⟩ := (hev'.and self_mem_nhdsWithin).exists
  have htpos : 0 < t := htpos
  refine ⟨Real.pi / t, ?_⟩
  rintro C h ⟨hcont, hbd, hN, hE⟩ x
  obtain ⟨k, hkD, hk⟩ := hk x
  obtain ⟨m, hm, hkm⟩ := hk t
  have hb := ht k hkD
  set b := k * a t * k⁻¹ with hbdef
  have hneg : ∀ g, h (g⁻¹ * b * x) = - h (g⁻¹ * x) := by
    intro g
    have e : g⁻¹ * b * x = g⁻¹ * x * a t * m := by
      rw [mul_assoc, hkm]; simp only [mul_assoc]
    rw [e, hN _ m hm, hE]
    have : Real.pi / t * t = Real.pi := by field_simp
    rw [this, Complex.exp_pi_mul_I]; ring
  have h1 : ∫ g, f (b * g) * h (g⁻¹ * x) ∂μ = - conv μ f h x := by
    have := integral_mul_left_eq_self (μ := μ) (fun g => f g * h (g⁻¹ * b * x)) b
    simp only [mul_inv_rev, inv_mul_cancel_right] at this
    rw [this, conv, ← integral_neg]
    congr 1
    ext g
    rw [hneg]; ring
  have hfb : Integrable (fun g => f (b * g)) μ := hf.comp_mul_left b
  have hmeas : AEStronglyMeasurable (fun g => h (g⁻¹ * x)) μ :=
    (hcont.comp (continuous_inv.mul continuous_const)).aestronglyMeasurable
  have i1 : Integrable (fun g => f (b * g) * h (g⁻¹ * x)) μ :=
    hfb.mul_bdd hmeas (Eventually.of_forall fun g => hbd _)
  have i2 : Integrable (fun g => f g * h (g⁻¹ * x)) μ :=
    hf.mul_bdd hmeas (Eventually.of_forall fun g => hbd _)
  have h2 : ∫ g, (f (b * g) - f g) * h (g⁻¹ * x) ∂μ = -2 * conv μ f h x := by
    simp only [sub_mul]
    rw [integral_sub i1 i2, h1, conv]; ring
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbd 1)
  have h3 : ‖∫ g, (f (b * g) - f g) * h (g⁻¹ * x) ∂μ‖ ≤ C := by
    calc _ ≤ ∫ g, ‖f (b * g) - f g‖ * C ∂μ := by
          apply norm_integral_le_of_norm_le ((hfb.sub hf).norm.mul_const C)
          refine Eventually.of_forall fun g => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hbd _) (norm_nonneg _)
      _ = (∫ g, ‖f (b * g) - f g‖ ∂μ) * C := integral_mul_const _ _
      _ ≤ 1 * C := mul_le_mul_of_nonneg_right hb hC
      _ = C := one_mul C
  rw [h2, norm_mul] at h3
  simp at h3
  linarith
end

section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.kills_of_idem :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (e : G → ℂ),
      IsRay N a H → Continuous e → Integrable e μ → (∀ x, conv μ e e x = e x) → Kills μ N a e := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H e hR hc hi hid
  have step1 : ∀ s, OpLe μ N a e s (1 / 2) → OpLe μ N a e s 0 := by
    intro s hs
    have hk : ∀ k : ℕ, OpLe μ N a e s ((1 / 2) ^ (k + 1)) := by
      intro k
      induction k with
      | zero => simpa using hs
      | succ k ih =>
        intro C h hh x
        have h1 := conv_isEig G μ N a e h s C hi hh
        have h2 : IsEig N a s (1 / 2 * C) (conv μ e h) := ⟨h1.1, hs C h hh, h1.2.2.1, h1.2.2.2⟩
        have h3 := ih _ _ h2 x
        rw [← conv_assoc G μ e e h C hc hi hc hi hh.1 hh.2.1 hid x] at h3
        calc _ ≤ _ := h3
          _ = _ := by ring
    intro C h hh x
    have ht : Tendsto (fun k : ℕ => ((1 / 2 : ℝ) ^ (k + 1)) * C) atTop (𝓝 (0 * C)) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 1)).mul_const C
    exact ge_of_tendsto' ht (fun k => hk k C h hh x)
  obtain ⟨δ, hδ, hnear⟩ := opLe_near G μ N a H e hR hi (1 / 2) (by norm_num)
  have step2 : ∀ s s', |s - s'| < δ → OpLe μ N a e s 0 → OpLe μ N a e s' 0 := by
    intro s s' hss hs
    have := hnear s s' 0 hss hs
    rw [zero_add] at this
    exact step1 s' this
  obtain ⟨s₀, hs₀⟩ := opLe_half G μ N a H e hR hi
  have h0 := step1 s₀ hs₀
  have step3 : ∀ n : ℕ, ∀ s, |s - s₀| ≤ n * (δ / 2) → OpLe μ N a e s 0 := by
    intro n
    induction n with
    | zero =>
      intro s hs
      have : s = s₀ := by
        have : |s - s₀| ≤ 0 := by simpa using hs
        linarith [abs_nonpos_iff.mp this]
      rw [this]; exact h0
    | succ n ih =>
      intro s hs
      have hn : (0 : ℝ) ≤ n * (δ / 2) := by positivity
      push_cast at hs
      rw [abs_le] at hs
      by_cases h1 : |s - s₀| ≤ n * (δ / 2)
      · exact ih s h1
      · rcases le_total s s₀ with h2 | h2
        · refine step2 (s₀ - n * (δ / 2)) s ?_ (ih _ ?_)
          · rw [abs_of_nonpos (by linarith), not_le] at h1
            rw [abs_lt]; constructor <;> nlinarith
          · rw [abs_le]; constructor <;> linarith
        · refine step2 (s₀ + n * (δ / 2)) s ?_ (ih _ ?_)
          · rw [abs_of_nonneg (by linarith), not_le] at h1
            rw [abs_lt]; constructor <;> nlinarith
          · rw [abs_le]; constructor <;> linarith
  intro s C h hh x
  obtain ⟨n, hn⟩ := exists_nat_ge (|s - s₀| / (δ / 2))
  rw [div_le_iff₀ (by positivity)] at hn
  have := step3 n s hn C h hh x
  rw [zero_mul] at this
  exact norm_le_zero_iff.mp this
end

section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.isEig_of_isBand :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (N : Set G) (a : ℝ → G) (H : G → ℝ) (h : G → ℂ),
      IsRay N a H → IsBand N H h → ∀ s : ℝ, ∃ C : ℝ,
        IsEig N a s C (fun g => ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a t)) ∧
          ∀ g, Integrable (fun t : ℝ => h (g * a t)) ∧ ∫ t : ℝ, ‖h (g * a t)‖ ≤ C := by
  intro G _ _ _ _ _ _ N a H h hr hb s
  obtain ⟨hc, ⟨B, hB⟩, hN, ⟨R, hR⟩⟩ := hb
  have ha := hr.cont
  have hH := hr.contH
  have he1 : ∀ x : ℝ, ‖Complex.exp (-((x : ℂ) * Complex.I))‖ = 1 := fun x => by
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have hsupp : ∀ g t, h (g * a t) ≠ 0 → |H g + t| ≤ R := fun g t hne => by
    have := hR _ hne
    rwa [hr.move] at this
  have hint : ∀ g, Integrable (fun t : ℝ => h (g * a t)) := by
    intro g
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := -R - H g) (b := R - H g)) ?_
    intro t ht
    by_contra hne
    apply ht
    have := abs_le.mp (hsupp g t hne)
    constructor <;> linarith [this.1, this.2]
  have hbound : ∀ g, ∫ t : ℝ, ‖h (g * a t)‖ ≤ 2 * |R| * |B| := by
    intro g
    have hle : ∀ t, ‖h (g * a t)‖ ≤ (Set.Icc (-R - H g) (R - H g)).indicator (fun _ => |B|) t := by
      intro t
      by_cases hne : h (g * a t) = 0
      · rw [hne, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
      · have := abs_le.mp (hsupp g t hne)
        rw [Set.indicator_of_mem (by constructor <;> linarith [this.1, this.2])]
        exact (hB _).trans (le_abs_self B)
    refine (integral_mono (hint g).norm
      ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc) hle).trans ?_
    rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, Real.volume_real_Icc]
    have h1 : max (R - H g - (-R - H g)) 0 ≤ 2 * |R| :=
      max_le (by linarith [le_abs_self R]) (by positivity)
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg B)
  have hshift : ∀ g, (∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a t)) =
      Complex.exp (((s * H g : ℝ) : ℂ) * Complex.I) *
        ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g)) := by
    intro g
    rw [← integral_const_mul]
    conv_lhs => rw [← integral_sub_right_eq_self _ (H g)]
    congr 1
    ext t
    rw [← mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  have hΦ : Continuous fun g =>
      ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g)) := by
    refine continuous_of_dominated (bound := (Set.Icc (-R) R).indicator (fun _ => |B|)) ?_ ?_ ?_ ?_
    · intro g
      exact (by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g))).aestronglyMeasurable
    · intro g
      refine Eventually.of_forall fun t => ?_
      rw [norm_mul, he1, one_mul]
      by_cases hne : h (g * a (t - H g)) = 0
      · rw [hne, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
      · have := abs_le.mp (hsupp g _ hne)
        rw [Set.indicator_of_mem (by constructor <;> linarith [this.1, this.2])]
        exact (hB _).trans (le_abs_self B)
    · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
    · exact Eventually.of_forall fun t => by fun_prop
  refine ⟨2 * |R| * |B|, ⟨?_, ?_, ?_, ?_⟩, fun g => ⟨hint g, hbound g⟩⟩
  · rw [show (fun g => ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a t)) =
        fun g => Complex.exp (((s * H g : ℝ) : ℂ) * Complex.I) *
          ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g)) from funext hshift]
    exact (Complex.continuous_exp.comp (by fun_prop)).mul hΦ
  · intro g
    refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_ (hbound g))
    congr 1
    ext t
    rw [norm_mul, he1, one_mul]
  · intro g m hm
    beta_reduce
    congr 1
    ext t
    rw [show g * m * a t = g * a t * ((a t)⁻¹ * m * a t) by group, hN _ _ (hr.norm t m hm)]
  · intro g u
    beta_reduce
    rw [← integral_const_mul]
    conv_rhs => rw [← integral_add_left_eq_self _ u]
    congr 1
    ext t
    rw [mul_assoc g, ← hr.add, ← mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
end

section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

open scoped FourierTransform in
theorem UpperTheory.Lit.Cusp.fourier_zero :
    ∀ u : ℝ → ℂ, Continuous u → Integrable u →
      (∀ s : ℝ, ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * u t = 0) → ∀ t, u t = 0 := by
  intro u hc hi hz t
  have hF : 𝓕 u = 0 := by
    ext w
    rw [Real.fourier_real_eq_integral_exp_smul, Pi.zero_apply, ← hz (2 * Real.pi * w)]
    congr 1
    ext v
    rw [smul_eq_mul]
    congr 1
    congr 1
    push_cast
    ring
  have hinv := hc.fourierInv_fourier_eq hi (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  simp [Real.fourierInv_eq]
end

section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.conv_band :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (f h : G → ℂ),
      IsRay N a H → Continuous f → Integrable f μ → Kills μ N a f → IsBand N H h → ∀ x, conv μ f h x = 0 := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H f h hR hf hfi hK hB x
  have ha := hR.cont
  have hh : Continuous h := hB.1
  obtain ⟨B, hBd⟩ := hB.2.1
  obtain ⟨C, -, hC⟩ := isEig_of_isBand G N a H h hR hB 0
  have a0 : a 0 = 1 := by
    have := hR.add 0 0
    rw [add_zero] at this
    simpa using this
  have hFc : Continuous (fun p : G × ℝ => f p.1 * h (p.1⁻¹ * x * a p.2)) := by fun_prop
  have hF : Integrable (fun p : G × ℝ => f p.1 * h (p.1⁻¹ * x * a p.2)) (μ.prod volume) := by
    rw [integrable_prod_iff hFc.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun g => (hC (g⁻¹ * x)).1.const_mul (f g), ?_⟩
    refine Integrable.mono' (hfi.norm.mul_const C)
      (hFc.norm.aestronglyMeasurable.integral_prod_right') (Eventually.of_forall fun g => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
    simp only [norm_mul]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hC (g⁻¹ * x)).2 (norm_nonneg _)
  have huc : Continuous (fun t : ℝ => ∫ g, f g * h (g⁻¹ * x * a t) ∂μ) := by
    refine continuous_of_dominated (bound := fun g => ‖f g‖ * B) (fun t => ?_) (fun t => ?_)
      (hfi.norm.mul_const B) (Eventually.of_forall fun g => by fun_prop)
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · refine Eventually.of_forall fun g => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hBd _) (norm_nonneg _)
  have hui : Integrable (fun t : ℝ => ∫ g, f g * h (g⁻¹ * x * a t) ∂μ) := hF.integral_prod_right
  have key := fourier_zero _ huc hui (fun s => ?_) 0
  · simpa [a0, conv] using key
  obtain ⟨D, hE, -⟩ := isEig_of_isBand G N a H h hR hB s
  have h0 := hK s D _ hE x
  have hF' : Integrable (fun p : G × ℝ =>
      Complex.exp (-((s * p.2 : ℝ) * Complex.I)) * (f p.1 * h (p.1⁻¹ * x * a p.2))) (μ.prod volume) := by
    refine hF.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun p => ?_)
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have hsw := integral_integral_swap (μ := μ) (ν := (volume : Measure ℝ))
    (f := fun g t => Complex.exp (-((s * t : ℝ) * Complex.I)) * (f g * h (g⁻¹ * x * a t))) hF'
  simp only [← integral_const_mul]
  rw [← hsw, ← h0, conv]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  ring
end

section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.conv_average :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ)
      (ν : Measure G) [IsFiniteMeasureOnCompacts ν], ν Nᶜ = 0 → (∀ m ∈ N, ν.map (fun x => m * x) = ν) →
      IsRay N a H → ∀ f ψ : G → ℂ, Continuous f → Integrable f μ → Continuous ψ → HasCompactSupport ψ → ∀ x,
        conv μ f (fun g => ∫ m, ψ (g * m) ∂ν) x = ∫ y, ψ y⁻¹ * ∫ m, f (x * m * y) ∂ν ∂μ := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H ν _ hN hinv hray f ψ hf hfi hψ hψc x
  haveI : IsLocallyFiniteMeasure ν := inferInstance
  haveI : SigmaFinite ν := inferInstance
  have hn := isBand_of_compact G N a H ν hN hinv hray (fun g => ((‖ψ g‖ : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp hψ.norm)
    (hψc.comp_left (g := fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) (by simp))
  have hb := isBand_of_compact G N a H ν hN hinv hray ψ hψ hψc
  obtain ⟨⟨-, ⟨C, hC⟩, -, -⟩, -⟩ := hn
  have hC' : ∀ g, ∫ m, ‖ψ (g * m)‖ ∂ν ≤ C := by
    intro g
    have h := hC g
    simp only [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hc1 : Continuous (fun p : G × G => f p.1 * ψ (p.1⁻¹ * x * p.2)) := by fun_prop
  have h1 : Integrable (fun p : G × G => f p.1 * ψ (p.1⁻¹ * x * p.2)) (μ.prod ν) := by
    rw [integrable_prod_iff hc1.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun g => (hb.2 (g⁻¹ * x)).const_mul (f g), ?_⟩
    refine Integrable.mono' (hfi.norm.mul_const C)
      (hc1.norm.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable
      (Eventually.of_forall fun g => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [norm_mul]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hC' _) (norm_nonneg _)
  have h2 := (integrable_prod_iff h1.swap.aestronglyMeasurable).1 h1.swap
  have key : ∀ m y : G, (x * m * y)⁻¹ * x * m = y⁻¹ := by
    intro m y; group
  have hc3 : Continuous (fun p : G × G => ψ p.2⁻¹ * f (x * p.1 * p.2)) := by fun_prop
  have h3 : Integrable (fun p : G × G => ψ p.2⁻¹ * f (x * p.1 * p.2)) (ν.prod μ) := by
    rw [integrable_prod_iff hc3.aestronglyMeasurable]
    refine ⟨h2.1.mono fun m hm => ?_, h2.2.congr (Eventually.of_forall fun m => ?_)⟩
    · have := hm.comp_mul_left (x * m)
      simpa only [Function.comp, Prod.swap, key, mul_comm (f _)] using this
    · have := integral_mul_left_eq_self (μ := μ) (fun g => ‖f g * ψ (g⁻¹ * x * m)‖) (x * m)
      simp only [key, mul_comm (f (x * m * _))] at this
      simpa only [Function.comp, Prod.swap] using this.symm
  calc conv μ f (fun g => ∫ m, ψ (g * m) ∂ν) x
      = ∫ g, ∫ m, f g * ψ (g⁻¹ * x * m) ∂ν ∂μ := by
        simp only [conv, integral_const_mul]
    _ = ∫ m, ∫ g, f g * ψ (g⁻¹ * x * m) ∂μ ∂ν := integral_integral_swap h1
    _ = ∫ m, ∫ y, ψ y⁻¹ * f (x * m * y) ∂μ ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun m => ?_)
        have := integral_mul_left_eq_self (μ := μ) (fun g => f g * ψ (g⁻¹ * x * m)) (x * m)
        simp only [key, mul_comm (f (x * m * _))] at this
        exact this.symm
    _ = ∫ y, ∫ m, ψ y⁻¹ * f (x * m * y) ∂ν ∂μ := integral_integral_swap h3
    _ = ∫ y, ψ y⁻¹ * ∫ m, f (x * m * y) ∂ν ∂μ := by
        simp only [integral_const_mul]
end

section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.eq_zero_of_test :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (F : G → ℂ), Continuous F →
      (∀ ψ : G → ℂ, Continuous ψ → HasCompactSupport ψ → ∫ y, ψ y⁻¹ * F y ∂μ = 0) → ∀ y, F y = 0 := by
  intro G _ _ _ _ _ _ _ _ μ _ F hF h y₀
  by_contra hy
  obtain ⟨χ, hχc, hχ0, hχy⟩ := exists_continuous_nonneg_pos y₀
  have hχcont : Continuous (fun y => χ y) := χ.continuous
  have hc1 : Continuous (fun y => (χ y : ℂ) * (starRingEnd ℂ) (F y)) :=
    (Complex.continuous_ofReal.comp hχcont).mul (Complex.continuous_conj.comp hF)
  have hs0 : HasCompactSupport (fun y => (χ y : ℂ)) :=
    hχc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hs1 : HasCompactSupport (fun y => (χ y : ℂ) * (starRingEnd ℂ) (F y)) :=
    hs0.mul_right (f' := fun y => (starRingEnd ℂ) (F y))
  have h1 := h (fun z => (χ z⁻¹ : ℂ) * (starRingEnd ℂ) (F z⁻¹)) (hc1.comp continuous_inv)
    (hs1.comp_homeomorph (Homeomorph.inv G))
  have h2 : ∀ y, (χ y⁻¹⁻¹ : ℂ) * (starRingEnd ℂ) (F y⁻¹⁻¹) * F y
      = ((χ y * ‖F y‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    rw [inv_inv, mul_assoc, Complex.conj_mul']
    push_cast
    rfl
  simp only [h2] at h1
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h1
  have hc2 : Continuous (fun y => χ y * ‖F y‖ ^ 2) := hχcont.mul (hF.norm.pow 2)
  have hs2 : HasCompactSupport (fun y => χ y * ‖F y‖ ^ 2) :=
    hχc.mul_right (f' := fun y => ‖F y‖ ^ 2)
  have hpos := hc2.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := y₀) hs2
    (fun y => mul_nonneg (hχ0 y) (sq_nonneg _))
    (mul_ne_zero hχy (pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)))
  exact hpos.ne' h1
end

section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.average_eq_zero :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ)
      (ν : Measure G) [IsFiniteMeasureOnCompacts ν], ν Nᶜ = 0 → (∀ m ∈ N, ν.map (fun x => m * x) = ν) →
      IsRay N a H → ∀ e f : G → ℂ, Continuous e → Integrable e μ → Continuous f → Integrable f μ →
        (∀ x, conv μ e e x = e x) → (∀ x, conv μ e f x = f x) →
        ∀ x, (Continuous fun y => ∫ m, f (x * m * y) ∂ν) → ∀ y, ∫ m, f (x * m * y) ∂ν = 0 := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H ν _ hν hinv hray e f hec hei hfc hfi hee hef x hcont
  have hKe : Kills μ N a e := kills_of_idem G μ N a H e hray hec hei hee
  have hKf : Kills μ N a f := by
    intro s C h hh z
    rw [conv_assoc G μ e f h C hec hei hfc hfi hh.1 hh.2.1 hef z]
    exact hKe s _ _ (conv_isEig G μ N a f h s C hfi hh) z
  refine eq_zero_of_test G μ (fun y => ∫ m, f (x * m * y) ∂ν) hcont ?_
  intro ψ hψ hψc
  rw [← conv_average G μ N a H ν hν hinv hray f ψ hfc hfi hψ hψc x]
  exact conv_band G μ N a H f _ hray hfc hfi hKf
    (isBand_of_compact G N a H ν hν hinv hray ψ hψ hψc).1 x
end
