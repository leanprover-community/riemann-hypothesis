import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLoc
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatNull

section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem hyq_nsq_chart (A : WeightedAtlas n Y ι La) (la : La) (s : ι → Y → ℂ) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source)
    (hs : s i y = A.g la i (A.pick y) y * s (A.pick y) y) :
    A.nsq la s y = ‖s i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  unfold WeightedAtlas.nsq
  have hp := A.mem_pick y
  have hg := A.g_ne la i (A.pick y) y hi hp
  have hpos : 0 < ‖A.g la i (A.pick y) y‖ ^ 2 := pow_pos (norm_pos_iff.2 hg) 2
  rw [A.ph_trans la i (A.pick y) y hi hp, hs, norm_mul, mul_pow]
  rw [show -(A.ph la i y - Real.log (‖A.g la i (A.pick y) y‖ ^ 2)) =
      -A.ph la i y + Real.log (‖A.g la i (A.pick y) y‖ ^ 2) by ring, Real.exp_add,
    Real.exp_log hpos]
  ring

theorem hyq_bdd {f : V n → ℝ} {c : V n} {r : ℝ} (hf : ContinuousOn f (closedBall c r)) :
    ∃ C : ℝ, ∀ v ∈ closedBall c r, f v ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall c r).bddAbove_image hf
  exact ⟨C, fun v hv => hC (Set.mem_image_of_mem f hv)⟩

theorem hyq_smoothFn_cont (A : WeightedAtlas n Y ι La) {f : Y → ℝ} (hf : A.SmoothFn f) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro y
  have hy := A.mem_pick y
  have h1 : ContinuousOn (f ∘ (A.chart (A.pick y)).symm) (A.chart (A.pick y)).target :=
    (hf (A.pick y)).continuousOn
  have h2 : ContinuousAt (f ∘ (A.chart (A.pick y)).symm) (A.chart (A.pick y) y) :=
    h1.continuousAt ((A.chart (A.pick y)).open_target.mem_nhds ((A.chart (A.pick y)).map_source hy))
  refine (h2.comp ((A.chart (A.pick y)).continuousAt hy)).congr ?_
  filter_upwards [(A.chart (A.pick y)).open_source.mem_nhds hy] with x hx
  simp [(A.chart (A.pick y)).left_inv hx]

theorem hyq_contDiffAt_of_holo {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) {c : V n} (hc : c ∈ U) : ContDiffAt ℝ ∞ g c :=
  (((contDiffOn_of_differentiableOn n g U hU hg).contDiffAt (hU.mem_nhds hc))).restrict_scalars ℝ

theorem hyq_contDiffAt_of_ev {g : V n → ℂ} {c : V n}
    (hg : ∀ᶠ v in 𝓝 c, DifferentiableAt ℂ g v) : ContDiffAt ℝ ∞ g c := by
  obtain ⟨U, hU, hUo, hcU⟩ := _root_.eventually_nhds_iff.1 hg
  exact hyq_contDiffAt_of_holo hUo (fun v hv => (hU v hv).differentiableWithinAt) hcU

def hyPhi (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ)
    (σ : ι → Y → ℂ) (la : La) (ps : Y → ℝ) (y : Y) : ℝ :=
  Real.log (A.nsq A.kap (fun i y => (jz A w0 s i y).det) y) - Real.log (A.nsq (A.kap + la) σ y) +
    ps y

def sectionFrameQuotient (A : WeightedAtlas n Y ι La) (F0 σ : ι → Y → ℂ) (y : Y) : ℂ :=
  F0 (A.pick y) y / σ (A.pick y) y

variable   (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {la : La} {σ : ι → Y → ℂ}

theorem hyq_sigma_ne (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ) {y : Y}
    (hy : y ∈ A.Mset w0 s De) (i : ι) (hi : y ∈ (A.chart i).source) : σ i y ≠ 0 := by
  obtain ⟨⟨_, htr⟩, hne⟩ := hσ
  rw [htr i (A.pick y) y hy hi (A.mem_pick y)]
  exact mul_ne_zero (A.g_ne _ i (A.pick y) y hi (A.mem_pick y)) (hne y hy)

theorem hyq_nsig_pos (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ) {y : Y}
    (hy : y ∈ A.Mset w0 s De) : 0 < A.nsq (A.kap + la) σ y := by
  obtain ⟨_, hne⟩ := hσ
  unfold WeightedAtlas.nsq
  exact mul_pos (pow_pos (norm_pos_iff.2 (hne y hy)) 2) (Real.exp_pos _)

theorem hyq_nJ_pos (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) {y : Y}
    (hy : y ∈ A.Mset w0 s De) : 0 < A.nsq A.kap (fun i y => (jz A w0 s i y).det) y := by
  unfold WeightedAtlas.nsq
  have h := hF.deriv_ne y hy
  exact mul_pos (pow_pos (norm_pos_iff.2 h) 2) (Real.exp_pos _)

theorem isOpen_chart_image_mem (hD : A.D0 L w w0 s) {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι)
    (hi : x ∈ (A.chart i).source) :
    IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De) ∧
      A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De := by
  obtain ⟨hw0d, hw0t⟩ := hD.isSection_denom
  have hsd : ∀ k, DifferentiableOn ℂ (s k i ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ) := fun k => by
    obtain ⟨h1, _⟩ := hD.sec_s k
    exact h1 i
  have hst : ∀ k, ∀ i j y, y ∈ (Set.univ : Set Y) → y ∈ (A.chart i).source →
      y ∈ (A.chart j).source → s k i y = A.g L i j y * s k j y := fun k => by
    obtain ⟨_, h2⟩ := hD.sec_s k
    exact h2
  have hT : (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ = (A.chart i).target := by simp
  have hw0c : ContinuousOn (w0 i ∘ (A.chart i).symm) (A.chart i).target := by
    have h := (hw0d i).continuousOn
    rwa [hT] at h
  have hsc : ∀ k, ContinuousOn (s k i ∘ (A.chart i).symm) (A.chart i).target := fun k => by
    have h := (hsd k).continuousOn
    rwa [hT] at h
  have hU1 : IsOpen ((A.chart i).target ∩ (w0 i ∘ (A.chart i).symm) ⁻¹' {0}ᶜ) :=
    hw0c.isOpen_inter_preimage (A.chart i).open_target isOpen_compl_singleton
  have hF2 : ContinuousOn (fun v => MvPolynomial.eval
      (fun k => s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v)) De)
      ((A.chart i).target ∩ (w0 i ∘ (A.chart i).symm) ⁻¹' {0}ᶜ) :=
    (MvPolynomial.continuous_eval De).comp_continuousOn (continuousOn_pi.2 fun k =>
      ((hsc k).mono Set.inter_subset_left).div (hw0c.mono Set.inter_subset_left)
        (fun v hv => hv.2))
  have hU2 := hF2.isOpen_inter_preimage hU1 (isOpen_compl_singleton (x := (0 : ℂ)))
  have key : ∀ v ∈ (A.chart i).target, ((A.chart i).symm v ∈ A.Mset w0 s De ↔
      (w0 i ((A.chart i).symm v) ≠ 0 ∧ MvPolynomial.eval
        (fun k => s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v)) De ≠ 0)) := by
    intro v hv
    have hy : (A.chart i).symm v ∈ (A.chart i).source := (A.chart i).map_target hv
    have hp := A.mem_pick ((A.chart i).symm v)
    have hg := A.g_ne L i (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) hy hp
    have e0 := hw0t i (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) (Set.mem_univ _) hy hp
    have ek : ∀ k, s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v) =
        s k (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) /
          w0 (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) := fun k => by
      rw [hst k i (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) (Set.mem_univ _) hy hp, e0,
        mul_div_mul_left _ _ hg]
    simp only [ek]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [e0]
        exact mul_ne_zero hg h1
      · simpa [WeightedAtlas.zmap] using h2
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · intro h0
        apply h1
        rw [e0, h0, mul_zero]
      · simpa [WeightedAtlas.zmap] using h2
  have hW : (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De =
      ((A.chart i).target ∩ (w0 i ∘ (A.chart i).symm) ⁻¹' {0}ᶜ) ∩ (fun v => MvPolynomial.eval
        (fun k => s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v)) De) ⁻¹' {0}ᶜ := by
    ext v
    constructor
    · rintro ⟨hv, hm⟩
      exact ⟨⟨hv, ((key v hv).1 hm).1⟩, ((key v hv).1 hm).2⟩
    · rintro ⟨⟨hv, h1⟩, h2⟩
      exact ⟨hv, (key v hv).2 ⟨h1, h2⟩⟩
  refine ⟨by rw [hW]; exact hU2, (A.chart i).map_source hi, ?_⟩
  rw [Set.mem_preimage, (A.chart i).left_inv hi]
  exact hx

theorem hyq_sig_cd (hD : A.D0 L w w0 s) (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (σ i ∘ (A.chart i).symm) (A.chart i x) := by
  obtain ⟨⟨hd, _⟩, _⟩ := hσ
  obtain ⟨ho, hm⟩ := isOpen_chart_image_mem A hD hx i hi
  exact hyq_contDiffAt_of_ev (Filter.eventually_of_mem (ho.mem_nhds hm) fun v hv =>
    (hd i v hv).differentiableAt (ho.mem_nhds hv))

theorem hyq_sig_holo (hD : A.D0 L w w0 s) (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    ∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ (σ i ∘ (A.chart i).symm) v := by
  obtain ⟨⟨hd, _⟩, _⟩ := hσ
  obtain ⟨ho, hm⟩ := isOpen_chart_image_mem A hD hx i hi
  filter_upwards [ho.mem_nhds hm] with v hv
  exact (hd i v hv).differentiableAt (ho.mem_nhds hv)

theorem hyq_evM (hD : A.D0 L w w0 s) {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι)
    (hi : x ∈ (A.chart i).source) :
    ∀ᶠ v in 𝓝 (A.chart i x), v ∈ (A.chart i).target ∧ (A.chart i).symm v ∈ A.Mset w0 s De := by
  obtain ⟨ho, hm⟩ := isOpen_chart_image_mem A hD hx i hi
  filter_upwards [ho.mem_nhds hm] with v hv
  exact ⟨hv.1, hv.2⟩

theorem hyq_phi_loc (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ) (ps : Y → ℝ)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    hyPhi A w0 s σ la ps =ᶠ[𝓝 x] fun y => (A.ph la i y + ps y) +
      Real.log (‖(jz A w0 s i y).det * (σ i y)⁻¹‖ ^ 2) := by
  filter_upwards [(A.chart i).open_source.mem_nhds hi, (isOpen_Mset A hD).mem_nhds hx]
    with y hyi hyM
  have hp := A.mem_pick y
  have hσne := hyq_sigma_ne A hσ hyM i hyi
  have hJne := jz_det_ne A hD hF y hyM i hyi
  have e1 := hyq_nsq_chart A _ σ i y hyi (hσ.1.2 i _ y hyM hyi hp)
  have e2 := hyq_nsq_chart A A.kap (fun i y => (jz A w0 s i y).det) i y hyi (by
    show (jz A w0 s i y).det = A.g A.kap i (A.pick y) y * (jz A w0 s (A.pick y) y).det
    rw [jz_det_trans A hD hF y hyM i (A.pick y) hyi hp, mul_comm])
  unfold hyPhi
  rw [e1, e2, A.ph_add A.kap la i y hyi, norm_mul, norm_inv, mul_pow, inv_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_exp, Real.log_exp]
  ring

theorem hyq_q_cd (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    (∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ
      (fun v => (fderiv ℂ (A.zLoc w0 s i) v).det * (σ i ((A.chart i).symm v))⁻¹) v) ∧
    ((fun y => (jz A w0 s i y).det * (σ i y)⁻¹) ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i x)]
      fun v => (fderiv ℂ (A.zLoc w0 s i) v).det * (σ i ((A.chart i).symm v))⁻¹) ∧
    (fun v => (fderiv ℂ (A.zLoc w0 s i) v).det * (σ i ((A.chart i).symm v))⁻¹) (A.chart i x) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [differentiableAt_det_jz A hD hF x hx i hi, hyq_sig_holo A hD hσ hx i hi,
      hyq_evM A hD hx i hi] with v h1 h2 h3
    exact h1.mul (h2.inv (hyq_sigma_ne A hσ h3.2 i ((A.chart i).map_target h3.1)))
  · filter_upwards [(A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)] with v hv
    simp only [Function.comp, jz, (A.chart i).right_inv hv]
  · simp only [(A.chart i).left_inv hi]
    exact mul_ne_zero (by simpa [jz] using jz_det_ne A hD hF x hx i hi)
      (inv_ne_zero (hyq_sigma_ne A hσ hx i hi))

theorem hyq_phi_smooth (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ) {ps : Y → ℝ} (hps : A.SmoothFn ps)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (hyPhi A w0 s σ la ps ∘ (A.chart i).symm) (A.chart i x) := by
  have hloc := hyq_phi_loc A hD hF hσ ps hx i hi
  obtain ⟨hQd, hQeq, hQne⟩ := hyq_q_cd A hD hF hσ hx i hi
  have hc := (A.chart i).map_source hi
  have ht : Filter.Tendsto (A.chart i).symm (𝓝 (A.chart i x)) (𝓝 x) := by
    have h0 := (A.chart i).continuousAt_symm hc
    rwa [ContinuousAt, (A.chart i).left_inv hi] at h0
  have h1 : hyPhi A w0 s σ la ps ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i x)] fun v =>
      (A.ph la i ((A.chart i).symm v) + ps ((A.chart i).symm v)) +
        Real.log (‖(fderiv ℂ (A.zLoc w0 s i) v).det * (σ i ((A.chart i).symm v))⁻¹‖ ^ 2) := by
    filter_upwards [hloc.comp_tendsto ht, hQeq] with v e1 e2
    simp only [Function.comp_apply] at e1 e2 ⊢
    rw [e1, e2]
  refine ContDiffAt.congr_of_eventuallyEq ?_ h1
  have hph : ContDiffAt ℝ ∞ (A.ph la i ∘ (A.chart i).symm) (A.chart i x) :=
    (A.smooth_ph la i).contDiffAt ((A.chart i).open_target.mem_nhds hc)
  have hps' : ContDiffAt ℝ ∞ (ps ∘ (A.chart i).symm) (A.chart i x) :=
    (hps i).contDiffAt ((A.chart i).open_target.mem_nhds hc)
  have hQs := hyq_contDiffAt_of_ev hQd
  have hlog := (hQs.norm_sq ℝ).log (pow_ne_zero 2 (norm_ne_zero_iff.2 hQne))
  exact (hph.add hps').add hlog

theorem hyq_levi_phi (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ) {ps : Y → ℝ} (hps : A.SmoothFn ps)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    A.leviAt i (hyPhi A w0 s σ la ps) x ξ = A.leviAt i (fun y => A.ph la i y + ps y) x ξ := by
  obtain ⟨hqd, hqe, hqne⟩ := hyq_q_cd A hD hF hσ hx i hi
  have hc : (A.chart i).symm (A.chart i x) = x := (A.chart i).left_inv hi
  have hT := (A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)
  have hq : ContDiffAt ℝ ∞ (fun v => (fderiv ℂ (A.zLoc w0 s i) v).det *
      (σ i ((A.chart i).symm v))⁻¹) (A.chart i x) :=
    ((contDiffAt_det_jz A hD hF x hx i hi).restrict_scalars ℝ).mul
      ((hyq_sig_cd A hD hσ hx i hi).inv (by simp only [Function.comp, hc]; exact hyq_sigma_ne A hσ hx i hi))
  have hf2 : ContDiffAt ℝ 2 ((fun y => A.ph la i y + ps y) ∘ (A.chart i).symm) (A.chart i x) :=
    (((A.smooth_ph la i).contDiffAt hT).add ((hps i).contDiffAt hT)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hg2 : ContDiffAt ℝ 2 ((fun y => Real.log (‖(jz A w0 s i y).det * (σ i y)⁻¹‖ ^ 2)) ∘
      (A.chart i).symm) (A.chart i x) := by
    refine (((hq.norm_sq ℝ).log (by positivity)).of_le (WithTop.coe_le_coe.mpr le_top)).congr_of_eventuallyEq ?_
    filter_upwards [hqe] with v hv
    simp only [Function.comp] at hv ⊢
    rw [hv]
  have hh : ∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ
      ((fun y => (jz A w0 s i y).det * (σ i y)⁻¹) ∘ (A.chart i).symm) v := by
    filter_upwards [hqd, hqe.eventuallyEq_nhds] with v h1 h2
    exact h1.congr_of_eventuallyEq h2
  rw [leviAt_congr A i _ _ x hi (hyq_phi_loc A hD hF hσ ps hx i hi) ξ,
    leviAt_add A i (fun y => A.ph la i y + ps y)
      (fun y => Real.log (‖(jz A w0 s i y).det * (σ i y)⁻¹‖ ^ 2)) x hf2 hg2 ξ,
    leviAt_log_normSq A i (fun y => (jz A w0 s i y).det * (σ i y)⁻¹) x hi hh
      (mul_ne_zero (jz_det_ne A hD hF x hx i hi) (inv_ne_zero (hyq_sigma_ne A hσ hx i hi))) ξ,
    add_zero]

theorem hyq_nsig_smooth (hD : A.D0 L w w0 s) (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (A.nsq (A.kap + la) σ ∘ (A.chart i).symm) (A.chart i x) := by
  have hsg := hyq_sig_cd A hD hσ hx i hi
  obtain ⟨⟨_, htr⟩, _⟩ := hσ
  obtain ⟨ho, hm⟩ := isOpen_chart_image_mem A hD hx i hi
  have hev : A.nsq (A.kap + la) σ ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i x)] fun v =>
      ‖σ i ((A.chart i).symm v)‖ ^ 2 * Real.exp (-A.ph (A.kap + la) i ((A.chart i).symm v)) := by
    filter_upwards [ho.mem_nhds hm] with v hv
    have hs' := (A.chart i).map_target hv.1
    exact hyq_nsq_chart A (A.kap + la) σ i ((A.chart i).symm v) hs'
      (htr i (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) hv.2 hs' (A.mem_pick _))
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have hph : ContDiffAt ℝ ∞ (A.ph (A.kap + la) i ∘ (A.chart i).symm) (A.chart i x) :=
    (A.smooth_ph (A.kap + la) i).contDiffAt
      ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hi))
  exact (hsg.norm_sq ℝ).mul hph.neg.exp

theorem contDiffAt_sectionFrameQuotient (hD : A.D0 L w w0 s) (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ)
    {F0 : ι → Y → ℂ} (hF0 : A.IsSSec (A.kap + la) F0)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (sectionFrameQuotient A F0 σ ∘ (A.chart i).symm) (A.chart i x) := by
  have h2 := hyq_sig_cd A hD hσ hx i hi
  have hne := hyq_sigma_ne A hσ hx i hi
  obtain ⟨⟨_, htr⟩, _⟩ := hσ
  obtain ⟨hF0s, hF0t⟩ := hF0
  obtain ⟨ho, hm⟩ := isOpen_chart_image_mem A hD hx i hi
  have hev : sectionFrameQuotient A F0 σ ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i x)] fun v =>
      F0 i ((A.chart i).symm v) / σ i ((A.chart i).symm v) := by
    filter_upwards [ho.mem_nhds hm] with v hv
    have hs' := (A.chart i).map_target hv.1
    have hp := A.mem_pick ((A.chart i).symm v)
    simp only [Function.comp_apply, sectionFrameQuotient]
    rw [hF0t i _ _ hs' hp, htr i _ _ hv.2 hs' hp,
      mul_div_mul_left _ _ (A.g_ne _ i _ _ hs' hp)]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have h1 : ContDiffAt ℝ ∞ (F0 i ∘ (A.chart i).symm) (A.chart i x) :=
    (hF0s i).contDiffAt ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hi))
  have hne' : (σ i ∘ (A.chart i).symm) (A.chart i x) ≠ 0 := by
    simpa [(A.chart i).left_inv hi] using hne
  have h3 := h1.mul (h2.inv hne')
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
  simp [div_eq_mul_inv]

theorem dbar_sectionFrameQuotient (hD : A.D0 L w w0 s) (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ)
    {F0 : ι → Y → ℂ} (hF0 : A.IsSSec (A.kap + la) F0)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    A.dbarAt i (fun _ => sectionFrameQuotient A F0 σ) x ξ = A.dbarAt i F0 x ξ / σ i x := by
  have hsh := hyq_sig_holo A hD hσ hx i hi
  have hne := hyq_sigma_ne A hσ hx i hi
  obtain ⟨⟨_, htr⟩, _⟩ := hσ
  obtain ⟨hF0s, hF0t⟩ := hF0
  obtain ⟨ho, hm⟩ := isOpen_chart_image_mem A hD hx i hi
  have hc := (A.chart i).map_source hi
  have hev : sectionFrameQuotient A F0 σ ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i x)] fun v =>
      (F0 i ∘ (A.chart i).symm) v * ((σ i ∘ (A.chart i).symm) v)⁻¹ := by
    filter_upwards [ho.mem_nhds hm] with v hv
    have hs' := (A.chart i).map_target hv.1
    have hp := A.mem_pick ((A.chart i).symm v)
    simp only [Function.comp_apply, sectionFrameQuotient]
    rw [hF0t i _ _ hs' hp, htr i _ _ hv.2 hs' hp, ← div_eq_mul_inv,
      mul_div_mul_left _ _ (A.g_ne _ i _ _ hs' hp)]
  have hne' : (σ i ∘ (A.chart i).symm) (A.chart i x) ≠ 0 := by
    simpa [(A.chart i).left_inv hi] using hne
  have hFd : DifferentiableAt ℝ (F0 i ∘ (A.chart i).symm) (A.chart i x) :=
    ((hF0s i).contDiffAt ((A.chart i).open_target.mem_nhds hc)).differentiableAt (by simp)
  have hGd : DifferentiableAt ℂ (fun v => ((σ i ∘ (A.chart i).symm) v)⁻¹) (A.chart i x) :=
    hsh.self_of_nhds.inv hne'
  have key : ∀ (j : Fin n) (F G : V n → ℂ) (c : V n), DifferentiableAt ℝ F c →
      DifferentiableAt ℂ G c → wdb n j (fun v => F v * G v) c = wdb n j F c * G c := by
    intro j F G c hF hG
    unfold wdb
    rw [fderiv_fun_mul hF (hG.restrictScalars ℝ), hG.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.coe_restrictScalars', map_smul]
    linear_combination (F c * fderiv ℂ G c (bas n j) / 2) * Complex.I_mul_I
  unfold WeightedAtlas.dbarAt
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  show wdb n j (sectionFrameQuotient A F0 σ ∘ (A.chart i).symm) (A.chart i x) * (starRingEnd ℂ) (ξ j) =
    wdb n j (F0 i ∘ (A.chart i).symm) (A.chart i x) * (starRingEnd ℂ) (ξ j) / σ i x
  have hw1 : wdb n j (sectionFrameQuotient A F0 σ ∘ (A.chart i).symm) (A.chart i x) =
      wdb n j (fun v => (F0 i ∘ (A.chart i).symm) v * ((σ i ∘ (A.chart i).symm) v)⁻¹)
        (A.chart i x) := by
    unfold wdb
    rw [hev.fderiv_eq (𝕜 := ℝ)]
  rw [hw1, key j _ _ _ hFd hGd]
  simp only [Function.comp_apply, (A.chart i).left_inv hi]
  ring

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem hy (n : ℕ) (Y : Type u) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] (hH : HAll.{u} n) (hE : EXTStatement n) (hN : EXTNullStatement n) :
    HYStatement n Y ι La := by
  intro A L la N w w0 s De σ ps F0 h hD hF hσ hps hPos hF0 hh hdb
  classical
  by_cases hfin : ∫⁻ y, h y * ENNReal.ofReal (Real.exp (-ps y)) ∂A.mu = ⊤
  · refine ⟨fun _ _ => 0, ⟨fun i => differentiableOn_const 0, fun i j y _ _ _ => by simp⟩, ?_⟩
    rw [hfin]; exact le_top
  set M := A.Mset w0 s De with hMdef
  set X := flatStein A hD hF with hX
  have hMo : IsOpen M := isOpen_Mset A hD
  set Φ := hyPhi A w0 s σ la ps with hΦdef
  set u0 := sectionFrameQuotient A F0 σ with hu0def
  set nσ := A.nsq (A.kap + la) σ with hnσdef
  have hpsc : Continuous ps := hyq_smoothFn_cont A hps
  have hΦs : SmoothR n X.z (fun y : M => Φ y) := smoothR_flat A hD hF Φ (fun x hx =>
    ⟨A.pick x, A.mem_pick x, hyq_phi_smooth A hD hF hσ hps hx _ (A.mem_pick x)⟩)
  have hΦl : LeviNonneg n X.z (fun y : M => Φ y) := leviNonneg_flat A hD hF Φ (fun x hx =>
    ⟨A.pick x, A.mem_pick x, hyq_phi_smooth A hD hF hσ hps hx _ (A.mem_pick x), fun ξ => by
      rw [hyq_levi_phi A hD hF hσ hps hx _ (A.mem_pick x)]
      exact hPos _ _ (A.mem_pick x) ξ⟩)
  have hu0s : Smooth n X.z (fun y : M => u0 y) := smooth_flat A hD hF u0 (fun x hx =>
    ⟨A.pick x, A.mem_pick x, contDiffAt_sectionFrameQuotient A hD hσ hF0 hx _ (A.mem_pick x)⟩)
  have hnσs : SmoothR n X.z (fun y : M => nσ y) := smoothR_flat A hD hF nσ (fun x hx =>
    ⟨A.pick x, A.mem_pick x, hyq_nsig_smooth A hD hσ hx _ (A.mem_pick x)⟩)
  have hnσc : Continuous (fun y : M => nσ y) := by
    have := Complex.continuous_re.comp (Smooth.continuous n X.z X.isLocalHomeomorph _ hnσs)
    exact this
  have hu0c : Continuous (fun y : M => u0 y) := Smooth.continuous n X.z X.isLocalHomeomorph _ hu0s

  set hHf : M → ℝ≥0∞ := fun x => h x * ENNReal.ofReal (nσ x)⁻¹ with hHfdef
  have hHm : Measurable hHf :=
    (hh.comp measurable_subtype_coe).mul (ENNReal.measurable_ofReal.comp hnσc.measurable.inv)
  have hdbM : ∀ (x : M) (η : Fin n → ℂ), ENNReal.ofReal (‖dbarDot n X.z (fun y : M => u0 y) x η‖ ^ 2) ≤
      hHf x * ENNReal.ofReal (Levi n X.z (fun y : M => Φ y) x η).re := by
    intro x η
    have hi := A.mem_pick (x : Y)
    have hdet := jz_det_ne A hD hF x x.2 (A.pick x) hi
    set J' := (jz A w0 s (A.pick x) x).toContinuousLinearEquivOfDetNeZero hdet
    set ξ : Fin n → ℂ := WithLp.ofLp (J'.symm (WithLp.toLp 2 η)) with hξ
    have hη : (fun k => jz A w0 s (A.pick x) x (WithLp.toLp 2 ξ) k) = η := by
      have h1 : jz A w0 s (A.pick x) x (WithLp.toLp 2 ξ) = WithLp.toLp 2 η := by
        have h2 := ((jz A w0 s (A.pick x) x).toContinuousLinearEquivOfDetNeZero hdet).apply_symm_apply
          (WithLp.toLp 2 η)
        rw [ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply] at h2
        simpa [J', ξ] using h2
      rw [h1]
    rw [← hη, ← dbar_flat_loc A hD hF u0 (A.pick x) x hi (contDiffAt_sectionFrameQuotient A hD hσ hF0 x.2 _ hi) ξ,
      ← levi_flat_loc A hD hF Φ (A.pick x) x hi (hyq_phi_smooth A hD hF hσ hps x.2 _ hi) ξ,
      hyq_levi_phi A hD hF hσ hps x.2 _ hi, dbar_sectionFrameQuotient A hD hσ hF0 x.2 _ hi]
    have key := hdb (A.pick x) x hi ξ
    have hσne := hyq_sigma_ne A hσ x.2 (A.pick x) hi
    have e1 : ‖A.dbarAt (A.pick x) F0 x ξ / σ (A.pick x) x‖ ^ 2 =
        (‖A.dbarAt (A.pick x) F0 x ξ‖ ^ 2 * Real.exp (-A.ph (A.kap + la) (A.pick x) x)) * (nσ x)⁻¹ := by
      simp only [hnσdef, nsq]
      rw [norm_div, div_pow, mul_inv, Real.exp_neg, inv_inv]
      field_simp
    rw [e1, ENNReal.ofReal_mul (by positivity)]
    calc _ ≤ h x * ENNReal.ofReal (A.leviAt (A.pick x) (fun y => A.ph la (A.pick x) y + ps y) x ξ) *
          ENNReal.ofReal (nσ x)⁻¹ := by gcongr
      _ = _ := by simp only [hHfdef]; ring
  obtain ⟨Fu, hFu, hFbd⟩ := hH M X (fun y => Φ y) (fun y => u0 y) hHf hΦs hΦl hu0s hHm hdbM

  set ut : Y → ℂ := fun y => if hy : y ∈ M then Fu ⟨y, hy⟩ else 0 with hutdef
  have hut : (fun y : M => ut y) = Fu := funext fun y => dif_pos y.2
  have hutc : Continuous (fun y : M => ut y) := by
    rw [hut]; exact Smooth.continuous n X.z X.isLocalHomeomorph _ (Holo.smooth n X.z _ hFu)
  set Fs : ι → Y → ℂ := fun i y => σ i y * ut y with hFsdef
  have hFs : A.IsSecOn (A.kap + la) M Fs := by
    refine ⟨fun i => ?_, fun i j y hy hi hj => ?_⟩
    · have h1 := (holo_flat_iff A hD hF ut).1 (by rw [hut]; exact hFu) i
      exact (hσ.1.1 i).mul h1
    · simp only [hFsdef]; rw [hσ.1.2 i j y hy hi hj]; ring

  set ψ0 : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (nσ y * ‖u0 y - ut y‖ ^ 2 * Real.exp (-ps y))
    with hψ0def
  set ψ : Y → ℝ≥0∞ := M.indicator ψ0 with hψdef
  have hψm : Measurable ψ := by
    refine measurable_of_restrict_of_restrict_compl hMo.measurableSet ?_ ?_
    · have hc : Continuous (fun y : M => ψ0 y) :=
        ENNReal.continuous_ofReal.comp ((hnσc.mul ((hu0c.sub hutc).norm.pow 2)).mul
          (Real.continuous_exp.comp (hpsc.comp continuous_subtype_val).neg))
      have : M.domRestrict ψ = fun y : M => ψ0 y := funext fun y => by
        show M.indicator ψ0 y = ψ0 y; exact Set.indicator_of_mem y.2 _
      rw [this]; exact hc.measurable
    · have : Mᶜ.domRestrict ψ = fun _ => 0 := funext fun y => by
        show M.indicator ψ0 y = 0; exact Set.indicator_of_notMem y.2 _
      rw [this]; exact measurable_const
  have hae : ∀ᵐ y ∂A.mu, y ∈ M := by
    rw [ae_iff]; simpa [Set.compl_def] using mu_compl_Mset A hN hD hF
  have hre : ∀ f : Y → ℝ≥0∞, ∫⁻ y, f y ∂A.mu = ∫⁻ y in M, f y ∂A.mu := fun f => by
    rw [Measure.restrict_eq_self_of_ae_mem hae]
  set nJ := A.nsq A.kap (fun i y => (jz A w0 s i y).det) with hnJdef
  have hdens : ∀ x : M, Real.exp (A.ph A.kap (A.pick x) x) / ‖(jz A w0 s (A.pick x) x).det‖ ^ 2 =
      (nJ x)⁻¹ := by
    intro x
    have hJp := hyq_nJ_pos A hD hF x.2
    simp only [hnJdef, nsq] at hJp ⊢
    rw [Real.exp_neg, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  have hexp : ∀ x : M, Real.exp (-Φ x) = nσ x * Real.exp (-ps x) * (nJ x)⁻¹ := by
    intro x
    have hσp := hyq_nsig_pos A hσ x.2
    have hJp := hyq_nJ_pos A hD hF x.2
    have e : -Φ x = Real.log (nσ x) - Real.log (nJ x) + -ps x := by
      simp only [hΦdef, hyPhi, hnσdef, hnJdef]; ring
    rw [e, Real.exp_add, Real.exp_sub, Real.exp_log hσp, Real.exp_log hJp]; ring
  have hI1 : ∫⁻ y, ψ y ∂A.mu = wint n X.z (fun x => u0 x - Fu x) (fun y => Φ y) := by
    rw [hre, lintegral_flat A hD hF ψ hψm, wint]
    refine lintegral_congr fun x => ?_
    have hσp := hyq_nsig_pos A hσ x.2
    rw [hψdef, Set.indicator_of_mem x.2]
    show ENNReal.ofReal (nσ x * ‖u0 x - ut x‖ ^ 2 * Real.exp (-ps x)) * _ = _
    rw [show ut x = Fu x from congrFun hut x, ← ENNReal.ofReal_mul (by positivity), hdens x, hexp x]
    congr 1; ring
  have hI2 : ∫⁻ x, hHf x * ENNReal.ofReal (Real.exp (-(fun y : M => Φ y) x)) ∂vol n X.z =
      ∫⁻ y in M, h y * ENNReal.ofReal (Real.exp (-ps y)) ∂A.mu := by
    rw [lintegral_flat A hD hF (fun y => h y * ENNReal.ofReal (Real.exp (-ps y))) (hh.mul
      (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hpsc.neg).measurable))]
    refine lintegral_congr fun x => ?_
    have hσp := hyq_nsig_pos A hσ x.2
    have hJp := hyq_nJ_pos A hD hF x.2
    rw [hHfdef, mul_assoc, mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), hdens x]
    show h x * ENNReal.ofReal ((nσ x)⁻¹ * Real.exp (-Φ x)) = _
    rw [hexp x]
    congr 2
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (show nσ x ≠ 0 from hσp.ne'), one_mul]
  have hint : ∫⁻ y, ψ y ∂A.mu ≤ ∫⁻ y, h y * ENNReal.ofReal (Real.exp (-ps y)) ∂A.mu := by
    rw [hI1]
    exact hFbd.trans (hI2.le.trans (setLIntegral_le_lintegral _ _))
  have hψfin : ∫⁻ y, ψ y ∂A.mu < ⊤ := hint.trans_lt (lt_top_iff_ne_top.2 hfin)

  have hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ M, ENNReal.ofReal (A.nsq (A.kap + la) Fs x) ∂A.mu < ⊤ := by
    intro y0
    have hi := A.mem_pick y0
    set e := A.chart (A.pick y0) with he
    obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.1 e.open_target (e y0) (e.map_source hi)
    have hcb : closedBall (e y0) (r / 2) ⊆ e.target :=
      (closedBall_subset_ball (by linarith)).trans hrt
    have hS : ContinuousOn e.symm (closedBall (e y0) (r / 2)) := e.continuousOn_symm.mono hcb
    obtain ⟨C1, hC1⟩ := hyq_bdd (f := fun v => ‖F0 (A.pick y0) (e.symm v)‖ ^ 2 *
      Real.exp (-A.ph (A.kap + la) (A.pick y0) (e.symm v))) (c := e y0) (r := r / 2) (by
        have h1 := (hF0.1 (A.pick y0)).continuousOn.mono hcb
        have h2 := (A.smooth_ph (A.kap + la) (A.pick y0)).continuousOn.mono hcb
        exact (h1.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn h2.neg))
    obtain ⟨C2, hC2⟩ := hyq_bdd (f := fun v => ps (e.symm v)) (c := e y0) (r := r / 2)
      (hpsc.comp_continuousOn hS)
    obtain ⟨C3, hC3⟩ := hyq_bdd (f := fun v => Real.exp (A.ph A.kap (A.pick y0) (e.symm v)))
      (c := e y0) (r := r / 2) (Real.continuous_exp.comp_continuousOn
        ((A.smooth_ph A.kap (A.pick y0)).continuousOn.mono hcb))
    set U := e.source ∩ e ⁻¹' ball (e y0) (r / 2) with hU
    have hUo : IsOpen U := e.isOpen_inter_preimage isOpen_ball
    have hyU : y0 ∈ U := ⟨hi, mem_ball_self (by linarith)⟩
    have hUM : MeasurableSet (U ∩ M) := (hUo.inter hMo).measurableSet
    refine ⟨U, hUo.mem_nhds hyU, ?_⟩
    have hC1n : 0 ≤ C1 := le_trans (by positivity) (hC1 (e y0) (mem_closedBall_self (by linarith)))
    have hpt : ∀ x ∈ U ∩ M, ENNReal.ofReal (A.nsq (A.kap + la) Fs x) ≤
        ENNReal.ofReal (2 * C1) + ENNReal.ofReal (2 * Real.exp C2) * ψ x := by
      rintro x ⟨⟨hxs, hxb⟩, hxM⟩
      have hv : e x ∈ closedBall (e y0) (r / 2) := ball_subset_closedBall hxb
      have hSx : e.symm (e x) = x := e.left_inv hxs
      have h1 := hC1 _ hv
      have h2 := hC2 _ hv
      simp only [hSx] at h1 h2
      have hF0x : A.nsq (A.kap + la) F0 x =
          ‖F0 (A.pick y0) x‖ ^ 2 * Real.exp (-A.ph (A.kap + la) (A.pick y0) x) :=
        hyq_nsq_chart A _ F0 _ x hxs (hF0.2 _ _ x hxs (A.mem_pick x))
      have hσne := hyq_sigma_ne A hσ hxM (A.pick x) (A.mem_pick x)
      have hFsx : A.nsq (A.kap + la) Fs x = nσ x * ‖ut x‖ ^ 2 := by
        simp only [nsq, hFsdef, hnσdef, norm_mul, mul_pow]; ring
      have hF0x' : A.nsq (A.kap + la) F0 x = nσ x * ‖u0 x‖ ^ 2 := by
        simp only [nsq, hnσdef, hu0def, sectionFrameQuotient, norm_div, div_pow]; field_simp
      have hσp := hyq_nsig_pos A hσ hxM
      set t := nσ x * ‖u0 x - ut x‖ ^ 2 * Real.exp (-ps x) with ht
      have hψx : ψ x = ENNReal.ofReal t := by rw [hψdef, Set.indicator_of_mem hxM]
      have ht0 : 0 ≤ t := by positivity
      have hpar : ‖ut x‖ ^ 2 ≤ 2 * ‖u0 x‖ ^ 2 + 2 * ‖u0 x - ut x‖ ^ 2 := by
        have h0 : ‖ut x‖ ≤ ‖u0 x‖ + ‖u0 x - ut x‖ := by
          calc ‖ut x‖ = ‖u0 x - (u0 x - ut x)‖ := by rw [sub_sub_cancel]
            _ ≤ _ := norm_sub_le _ _
        have h3 : ‖ut x‖ ^ 2 ≤ (‖u0 x‖ + ‖u0 x - ut x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h0 2
        nlinarith [sq_nonneg (‖u0 x‖ - ‖u0 x - ut x‖)]
      have hte : nσ x * ‖u0 x - ut x‖ ^ 2 = Real.exp (ps x) * t := by
        rw [ht, Real.exp_neg]; field_simp
      have hkey : A.nsq (A.kap + la) Fs x ≤ 2 * C1 + 2 * Real.exp C2 * t := by
        have he2 : Real.exp (ps x) ≤ Real.exp C2 := Real.exp_le_exp.2 h2
        calc A.nsq (A.kap + la) Fs x = nσ x * ‖ut x‖ ^ 2 := hFsx
          _ ≤ nσ x * (2 * ‖u0 x‖ ^ 2 + 2 * ‖u0 x - ut x‖ ^ 2) := by gcongr
          _ = 2 * A.nsq (A.kap + la) F0 x + 2 * (Real.exp (ps x) * t) := by rw [hF0x', ← hte]; ring
          _ ≤ 2 * C1 + 2 * (Real.exp C2 * t) := by
            rw [hF0x]; gcongr
          _ = 2 * C1 + 2 * Real.exp C2 * t := by ring
      rw [hψx, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
      exact ENNReal.ofReal_le_ofReal hkey
    calc ∫⁻ x in U ∩ M, ENNReal.ofReal (A.nsq (A.kap + la) Fs x) ∂A.mu
        ≤ ∫⁻ x in U ∩ M, (ENNReal.ofReal (2 * C1) + ENNReal.ofReal (2 * Real.exp C2) * ψ x) ∂A.mu :=
          setLIntegral_mono' hUM hpt
      _ = ENNReal.ofReal (2 * C1) * A.mu (U ∩ M) +
          ENNReal.ofReal (2 * Real.exp C2) * ∫⁻ x in U ∩ M, ψ x ∂A.mu := by
          rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul _ hψm,
            Measure.restrict_apply_univ]
      _ < ⊤ := by
          have hmu : A.mu (U ∩ M) < ⊤ := by
            calc A.mu (U ∩ M) ≤ A.mu U := measure_mono Set.inter_subset_left
              _ = ∫⁻ v in e '' U, ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y0) (e.symm v))) :=
                  A.mu_chart _ U hUo.measurableSet Set.inter_subset_left
              _ ≤ ∫⁻ v in closedBall (e y0) (r / 2),
                  ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y0) (e.symm v))) :=
                  lintegral_mono_set (by
                    rintro _ ⟨y, ⟨_, hyb⟩, rfl⟩; exact ball_subset_closedBall hyb)
              _ ≤ ∫⁻ v in closedBall (e y0) (r / 2), ENNReal.ofReal C3 :=
                  setLIntegral_mono' measurableSet_closedBall
                    (fun v hv => ENNReal.ofReal_le_ofReal (hC3 v hv))
              _ = ENNReal.ofReal C3 * volume (closedBall (e y0) (r / 2)) := setLIntegral_const _ _
              _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
          have hψU : ∫⁻ x in U ∩ M, ψ x ∂A.mu < ⊤ :=
            (setLIntegral_le_lintegral _ _).trans_lt hψfin
          exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmu,
            ENNReal.mul_lt_top ENNReal.ofReal_lt_top hψU⟩

  obtain ⟨G, hG, hGeq⟩ := ext_Mset A hE hD hF (A.kap + la) Fs hFs hloc
  refine ⟨G, hG, ?_⟩
  calc ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + la) (F0 - G) y * Real.exp (-ps y)) ∂A.mu
      = ∫⁻ y, ψ y ∂A.mu := by
        refine lintegral_congr_ae (hae.mono fun y hy => ?_)
        rw [hψdef, Set.indicator_of_mem hy]
        show ENNReal.ofReal (A.nsq (A.kap + la) (F0 - G) y * Real.exp (-ps y)) = ψ0 y
        have hσne := hyq_sigma_ne A hσ hy (A.pick y) (A.mem_pick y)
        have hGy := hGeq (A.pick y) y hy (A.mem_pick y)
        have e : A.nsq (A.kap + la) (F0 - G) y = nσ y * ‖u0 y - ut y‖ ^ 2 := by
          simp only [nsq, Pi.sub_apply, hGy, hFsdef, hnσdef, hu0def, sectionFrameQuotient]
          rw [show F0 (A.pick y) y - σ (A.pick y) y * ut y =
            σ (A.pick y) y * (F0 (A.pick y) y / σ (A.pick y) y - ut y) by field_simp, norm_mul,
            mul_pow]
          ring
        rw [e]
    _ ≤ _ := hint

end

end ReciprocityTheory.L2DbarEstimates.Y
end
