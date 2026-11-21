import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNsqCanonicalAddChartPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableNsqExtendAndPsi
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.VanishAtSStatementPf
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenAtlasSectionNonvanishingSetAndMemIff

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

noncomputable section

theorem vanish_at_simple_zero_of_weighted_sq_integrable :
    ∀ (n : ℕ), 1 ≤ n → ∀ (p : V n) (O : Set (V n)) (Z : V n → V n) (lam : V n → ℝ), IsOpen O → p ∈ O →
      DifferentiableOn ℂ Z O → Z p = 0 → (fderiv ℂ Z p).det ≠ 0 → ContinuousOn lam O →
      ∀ u : V n → ℂ, ContinuousOn u O →
        ∫⁻ v in O, ENNReal.ofReal (‖u v‖ ^ 2 * Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) < ⊤ →
        u p = 0 := by
  intro n hn1 p O Z lam hO hpO hZ hZ0 hdet hlam u hu hint
  have hn : 0 < n := hn1
  by_contra hne
  have hOn : O ∈ 𝓝 p := hO.mem_nhds hpO

  have htr : Tendsto (fun z : V n => z + p) (𝓝 0) (𝓝 p) := by
    have := (continuous_add_right p).tendsto (0 : V n)
    simpa using this
  set a := ‖u p‖ with ha
  have ha0 : 0 < a := norm_pos_iff.mpr hne
  have ev1 : ∀ᶠ z in 𝓝 (0 : V n), a / 2 < ‖u (z + p)‖ := by
    have hc : Tendsto (fun v => ‖u v‖) (𝓝 p) (𝓝 a) := ((hu.continuousAt hOn).norm)
    exact htr.eventually (hc.eventually (Ioi_mem_nhds (by linarith)))
  have ev4 : ∀ᶠ z in 𝓝 (0 : V n), lam p - 1 < lam (z + p) := by
    have hc : Tendsto lam (𝓝 p) (𝓝 (lam p)) := hlam.continuousAt hOn
    exact htr.eventually (hc.eventually (Ioi_mem_nhds (by linarith)))
  have ev5 : ∀ᶠ z in 𝓝 (0 : V n), z + p ∈ O := htr.eventually hOn
  set σ : V n → V n := fun z => Z (z + p) with hσ
  have hσ0 : σ 0 = 0 := by simp [hσ, hZ0]
  have hσd : fderiv ℂ σ 0 = fderiv ℂ Z p := by
    rw [hσ, fderiv_comp_add_right]; simp
  obtain ⟨c, hc, ev2⟩ := ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.lower_of_det hn hσ0 (hσd ▸ hdet)
  have hdiff : DifferentiableAt ℂ σ 0 := by
    have h1 : DifferentiableAt ℂ Z (0 + p) := by simpa using hZ.differentiableAt hOn
    exact h1.comp (0 : V n) ((differentiableAt_id).add_const p)
  obtain ⟨C, ev3⟩ : ∃ C : ℝ, ∀ᶠ z in 𝓝 (0 : V n), ‖σ z‖ ≤ C * ‖z‖ := by
    have h := hdiff.hasFDerivAt.isBigO_sub
    simp only [hσ0, sub_zero] at h
    obtain ⟨C, hC⟩ := h.bound
    exact ⟨C, hC⟩
  obtain ⟨δ0, hδ0, hall⟩ := Metric.eventually_nhds_iff.mp
    (ev1.and (ev2.and (ev3.and (ev4.and ev5))))
  set Eb : ℝ := Real.exp (1 - lam p) with hEb
  set B : ℝ := C ^ 2 * Eb + 1 with hB
  have hB0 : 0 < B := by positivity
  set K : ℝ := (a / 2) ^ 2 * B ^ (-(n : ℝ)) with hK
  have hK0 : 0 < K := by positivity
  have hp : -(n : ℝ) ≤ 0 := by have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _; linarith
  set F : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (‖u v‖ ^ 2 *
    Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) with hF
  have hpt : ∀ z ∈ ball (0 : V n) δ0, z ≠ 0 →
      ENNReal.ofReal K * ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤ F (z + p) := by
    intro z hz hz0
    obtain ⟨h1, h2, h3, h4, -⟩ := hall (by simpa using hz)
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    set X := ‖Z (z + p)‖ ^ 2 * Real.exp (-lam (z + p)) with hX
    have hZpos : 0 < ‖Z (z + p)‖ := lt_of_lt_of_le (by positivity) h2
    have hXpos : 0 < X := by positivity
    have hexle : Real.exp (-lam (z + p)) ≤ Eb := Real.exp_le_exp.mpr (by linarith)
    have hXle : X ≤ B * ‖z‖ ^ 2 := by
      have hZle : ‖Z (z + p)‖ ^ 2 ≤ C ^ 2 * ‖z‖ ^ 2 := by
        have h0 : 0 ≤ C * ‖z‖ := le_trans (norm_nonneg _) h3
        calc ‖Z (z + p)‖ ^ 2 ≤ (C * ‖z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
          _ = C ^ 2 * ‖z‖ ^ 2 := by ring
      calc X ≤ (C ^ 2 * ‖z‖ ^ 2) * Eb :=
            mul_le_mul hZle hexle (Real.exp_pos _).le (by positivity)
        _ ≤ B * ‖z‖ ^ 2 := by rw [hB]; nlinarith [sq_nonneg ‖z‖, sq_nonneg C, Real.exp_pos (1 - lam p)]
    have hw : Real.exp (-((n : ℝ) * Real.log X)) = X ^ (-(n : ℝ)) := by
      rw [Real.rpow_def_of_pos hXpos]; ring_nf
    show ENNReal.ofReal K * ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤
      ENNReal.ofReal (‖u (z + p)‖ ^ 2 * Real.exp (-((n : ℝ) * Real.log X)))
    rw [hw, ← ENNReal.ofReal_mul hK0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hSp : (B * ‖z‖ ^ 2) ^ (-(n : ℝ)) ≤ X ^ (-(n : ℝ)) := Real.rpow_le_rpow_of_nonpos hXpos hXle hp
    have hexp : (B * ‖z‖ ^ 2) ^ (-(n : ℝ)) = B ^ (-(n : ℝ)) * ‖z‖ ^ (-2 * (n : ℝ)) := by
      rw [Real.mul_rpow hB0.le (by positivity), ← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
      ring_nf
    have hu2 : (a / 2) ^ 2 ≤ ‖u (z + p)‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1.le 2
    calc K * ‖z‖ ^ (-2 * (n : ℝ)) = (a / 2) ^ 2 * (B * ‖z‖ ^ 2) ^ (-(n : ℝ)) := by rw [hexp, hK]; ring
      _ ≤ ‖u (z + p)‖ ^ 2 * X ^ (-(n : ℝ)) :=
        mul_le_mul hu2 hSp (by positivity) (by positivity)
  have hne0 : ∀ᵐ z ∂(volume : Measure (V n)), z ≠ 0 := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact measure_eq_zero_iff_ae_notMem.mp (measure_singleton 0)

  have hsubO : ∀ z ∈ ball (0 : V n) δ0, z + p ∈ O := fun z hz => (hall (by simpa using hz)).2.2.2.2
  have htrans : ∫⁻ z in ball (0 : V n) δ0, F (z + p) ≤ ∫⁻ v in O, F v := by
    have hind : ∀ z : V n, (ball p δ0).indicator F (z + p) = (ball (0 : V n) δ0).indicator (fun z => F (z + p)) z := by
      intro z
      have hm : z + p ∈ ball p δ0 ↔ z ∈ ball (0 : V n) δ0 := by
        simp [mem_ball, dist_eq_norm]
      by_cases hz : z ∈ ball (0 : V n) δ0
      · rw [Set.indicator_of_mem (hm.mpr hz), Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem (fun h => hz (hm.mp h)), Set.indicator_of_notMem hz]
    have e1 : ∫⁻ z in ball (0 : V n) δ0, F (z + p) = ∫⁻ v in ball p δ0, F v := by
      rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
      simp_rw [← hind]
      exact lintegral_add_right_eq_self (μ := volume) ((ball p δ0).indicator F) p
    have hsb : ball p δ0 ⊆ O := by
      intro v hv
      have h1 : v - p ∈ ball (0 : V n) δ0 := by simpa [mem_ball, dist_eq_norm] using hv
      simpa using hsubO (v - p) h1
    rw [e1]
    exact lintegral_mono_set hsb
  have hlow : ENNReal.ofReal K * ∫⁻ z in ball (0 : V n) δ0, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤
      ∫⁻ v in O, F v := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans ?_ htrans
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne0] with z hz hz0
    exact hpt z hz hz0
  rw [ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.crit_div hn hδ0, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hK0).ne'] at hlow
  exact absurd (lt_of_le_of_lt hlow hint) (lt_irrefl _)

end

end GlobalTheory
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_at_simple_zero_of_weighted_sq_integrable : ∀ (n : ℕ), 1 ≤ n → ∀ (p : V n) (O : Set (V n)) (Z : V n → V n) (lam : V n → ℝ), IsOpen O → p ∈ O → DifferentiableOn ℂ Z O → Z p = 0 → (fderiv ℂ Z p).det ≠ 0 → ContinuousOn lam O → ∀ u : V n → ℂ, ContinuousOn u O → ∫⁻ v in O, ENNReal.ofReal (‖u v‖ ^ 2 * Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) < ⊤ → u p = 0 := by
  atlas_forward_decl GlobalTheory.vanish_at_simple_zero_of_weighted_sq_integrable
end

section
section
namespace GlobalTheory.OTY

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y Set
open scoped ENNReal ContDiff

noncomputable section

section L2ExtNz

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {Λ : La} {τ : ι → Y → ℂ}

theorem nz_coeff_ne_iff (hτ : A.IsSec Λ τ) {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    τ i y ≠ 0 ↔ y ∈ nz A τ := by
  show τ i y ≠ 0 ↔ τ (A.pick y) y ≠ 0
  rw [hτ.2 (A.pick y) i y trivial (A.mem_pick y) hy]
  have hg := A.g_ne Λ (A.pick y) i y (A.mem_pick y) hy
  constructor
  · intro h; exact mul_ne_zero hg h
  · intro h h0; exact h (by rw [h0, mul_zero])

theorem nz_isOpen_of_isSec (hτ : A.IsSec Λ τ) : IsOpen (nz A τ) := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  have hc : ContinuousOn (τ (A.pick y)) (A.chart (A.pick y)).source := by
    simpa using fn_contOn_sec A hτ (A.pick y)
  refine ⟨(A.chart (A.pick y)).source ∩ τ (A.pick y) ⁻¹' {0}ᶜ, ?_,
    hc.isOpen_inter_preimage (A.chart _).open_source isOpen_compl_singleton, ⟨A.mem_pick y, hy⟩⟩
  rintro x ⟨hxs, hx⟩
  exact (nz_coeff_ne_iff A hτ hxs).1 hx

theorem nz_coeff_diff (hτ : A.IsSec Λ τ) (i : ι) :
    DifferentiableOn ℂ (τ i ∘ (A.chart i).symm) (A.chart i).target := by
  simpa using hτ.1 i

theorem nz_coeff_ne_iff' (hτ : A.IsSec Λ τ) {i : ι} {v : V n} (hv : v ∈ (A.chart i).target) :
    (τ i ∘ (A.chart i).symm) v ≠ 0 ↔ (A.chart i).symm v ∈ nz A τ :=
  nz_coeff_ne_iff A hτ ((A.chart i).map_target hv)

theorem nz_loc (hτ : A.IsSec Λ τ) {la : La} {F : ι → Y → ℂ}
    (hFs : A.IsSecOn la (nz A τ) F)
    (hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ nz A τ, ENNReal.ofReal (A.nsq la F x) ∂A.mu < ⊤)
    (i : ι) {v : V n} (hv : v ∈ (A.chart i).target) :
    ∃ r > 0, Metric.ball v r ⊆ (A.chart i).target ∧
      ∫⁻ u in Metric.ball v r \ {u | (τ i ∘ (A.chart i).symm) u = 0},
        ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2) < ⊤ := by
  have hMo : IsOpen (nz A τ) := nz_isOpen_of_isSec A hτ
  obtain ⟨U, hU, hfin⟩ := hloc ((A.chart i).symm v)
  obtain ⟨U', hU'U, hU'o, hyU'⟩ := mem_nhds_iff.1 hU
  have hTo : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U') :=
    (A.chart i).isOpen_inter_preimage_symm hU'o
  obtain ⟨r0, hr0, hB0⟩ := Metric.isOpen_iff.1 hTo v ⟨hv, hyU'⟩
  have hK : Metric.closedBall v (r0 / 2) ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U' :=
    (Metric.closedBall_subset_ball (by linarith)).trans hB0
  have hqc : ContinuousOn (fun u => Real.exp (A.ph la i ((A.chart i).symm u) -
      A.ph A.kap i ((A.chart i).symm u))) (Metric.closedBall v (r0 / 2)) :=
    (Real.continuous_exp.comp_continuousOn
      ((A.smooth_ph la i).continuousOn.sub (A.smooth_ph A.kap i).continuousOn)).mono
      (hK.trans inter_subset_left)
  obtain ⟨C, hC⟩ := (isCompact_closedBall v (r0 / 2)).exists_bound_of_continuousOn hqc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC v (Metric.mem_closedBall_self (by linarith)))
  have hBt : Metric.ball v (r0 / 2) ⊆ (A.chart i).target :=
    (Metric.ball_subset_closedBall.trans hK).trans inter_subset_left
  refine ⟨r0 / 2, by linarith, hBt, ?_⟩
  have hSm : MeasurableSet ((A.chart i).source ∩ nz A τ ∩ U') :=
    (((A.chart i).open_source.inter hMo).inter hU'o).measurableSet
  have hgc : ContinuousOn (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x)))
      ((A.chart i).source ∩ nz A τ ∩ U') :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (((fn_contOn_sec A hFs i).mono inter_subset_left).norm.pow 2 |>.mul
        (Real.continuous_exp.comp_continuousOn
          ((fn_contOn_ph A la i).mono (inter_subset_left.trans inter_subset_left)).neg))
  have hmg : Measurable (((A.chart i).source ∩ nz A τ ∩ U').indicator
      (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x)))) := by
    classical
    rw [← Set.piecewise_eq_indicator]
    exact hgc.measurable_piecewise continuousOn_const hSm
  have hmeas : MeasurableSet (Metric.ball v (r0 / 2) \ {u | (τ i ∘ (A.chart i).symm) u = 0}) := by
    have : IsOpen (Metric.ball v (r0 / 2) ∩ (τ i ∘ (A.chart i).symm) ⁻¹' {0}ᶜ) :=
      ((nz_coeff_diff A hτ i).continuousOn.mono hBt).isOpen_inter_preimage Metric.isOpen_ball
        isOpen_compl_singleton
    exact this.measurableSet
  calc ∫⁻ u in Metric.ball v (r0 / 2) \ {u | (τ i ∘ (A.chart i).symm) u = 0},
        ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2)
      ≤ ∫⁻ u in Metric.ball v (r0 / 2) \ {u | (τ i ∘ (A.chart i).symm) u = 0},
        ENNReal.ofReal C * (fnRho A i u * ((A.chart i).source ∩ nz A τ ∩ U').indicator
          (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x))) ((A.chart i).symm u)) := by
        refine setLIntegral_mono' hmeas fun u hu => ?_
        have hut : u ∈ (A.chart i).target := hBt hu.1
        have hsu : (A.chart i).symm u ∈ (A.chart i).source := (A.chart i).map_target hut
        have hM : (A.chart i).symm u ∈ nz A τ := (nz_coeff_ne_iff' A hτ hut).1 hu.2
        have hU' : (A.chart i).symm u ∈ U' := (hK (Metric.ball_subset_closedBall hu.1)).2
        have hmem : (A.chart i).symm u ∈ (A.chart i).source ∩ nz A τ ∩ U' := ⟨⟨hsu, hM⟩, hU'⟩
        rw [Set.indicator_of_mem (s := (A.chart i).source ∩ nz A τ ∩ U') hmem]
        unfold fnRho
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hC0]
        apply ENNReal.ofReal_le_ofReal
        have hq := hC u (Metric.ball_subset_closedBall hu.1)
        rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hq
        have e0 : Real.exp (A.ph la i ((A.chart i).symm u) - A.ph A.kap i ((A.chart i).symm u)) *
            Real.exp (A.ph A.kap i ((A.chart i).symm u)) *
            Real.exp (-A.ph la i ((A.chart i).symm u)) = 1 := by
          rw [← Real.exp_add, ← Real.exp_add]; simp
        calc ‖F i ((A.chart i).symm u)‖ ^ 2
            = Real.exp (A.ph la i ((A.chart i).symm u) - A.ph A.kap i ((A.chart i).symm u)) *
              (Real.exp (A.ph A.kap i ((A.chart i).symm u)) *
                (‖F i ((A.chart i).symm u)‖ ^ 2 * Real.exp (-A.ph la i ((A.chart i).symm u)))) := by
              linear_combination (-‖F i ((A.chart i).symm u)‖ ^ 2) * e0
          _ ≤ _ := mul_le_mul_of_nonneg_right hq (by positivity)
    _ ≤ ∫⁻ u in (A.chart i).target,
        ENNReal.ofReal C * (fnRho A i u * ((A.chart i).source ∩ nz A τ ∩ U').indicator
          (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x))) ((A.chart i).symm u)) :=
        lintegral_mono_set (sdiff_subset.trans hBt)
    _ = ENNReal.ofReal C * ∫⁻ x in (A.chart i).source, ((A.chart i).source ∩ nz A τ ∩ U').indicator
          (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x))) x ∂A.mu := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, fn_lint A i hmg]
    _ ≤ ENNReal.ofReal C * ∫⁻ x in U ∩ nz A τ, ENNReal.ofReal (A.nsq la F x) ∂A.mu := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        calc _ ≤ ∫⁻ x, ((A.chart i).source ∩ nz A τ ∩ U').indicator
              (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x))) x ∂A.mu :=
              setLIntegral_le_lintegral _ _
          _ = ∫⁻ x in (A.chart i).source ∩ nz A τ ∩ U',
              ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x)) ∂A.mu := lintegral_indicator hSm _
          _ = ∫⁻ x in (A.chart i).source ∩ nz A τ ∩ U',
              ENNReal.ofReal (A.nsq la F x) ∂A.mu :=
              setLIntegral_congr_fun hSm fun x hx => by rw [fn_nsq_eq A hFs hx.1.1 hx.1.2]
          _ ≤ _ := lintegral_mono_set fun x (hx : x ∈ (A.chart i).source ∩ nz A τ ∩ U') =>
              (⟨hU'U hx.2, hx.1.2⟩ : x ∈ U ∩ nz A τ)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem nz_sub_closure (hτ : A.IsSec Λ τ) (hdense : Dense (nz A τ)) (i : ι) {O : Set (V n)}
    (hO : IsOpen O) (hOt : O ⊆ (A.chart i).target) :
    O ⊆ closure (O ∩ {u | (τ i ∘ (A.chart i).symm) u ≠ 0}) := by
  intro p hp
  rw [_root_.mem_closure_iff]
  intro o ho hpo
  have hWo : IsOpen ((A.chart i).source ∩ A.chart i ⁻¹' (o ∩ O)) :=
    (A.chart i).continuousOn.isOpen_inter_preimage (A.chart i).open_source (ho.inter hO)
  have hpt := hOt hp
  have hmem : (A.chart i).symm p ∈ (A.chart i).source ∩ A.chart i ⁻¹' (o ∩ O) := by
    refine ⟨(A.chart i).map_target hpt, ?_⟩
    show A.chart i ((A.chart i).symm p) ∈ o ∩ O
    rw [(A.chart i).right_inv hpt]; exact ⟨hpo, hp⟩
  obtain ⟨x, hxW, hxM⟩ := hdense.inter_open_nonempty _ hWo ⟨_, hmem⟩
  refine ⟨A.chart i x, hxW.2.1, hxW.2.2, ?_⟩
  show (τ i ∘ (A.chart i).symm) (A.chart i x) ≠ 0
  rw [nz_coeff_ne_iff' A hτ ((A.chart i).map_source hxW.1), (A.chart i).left_inv hxW.1]
  exact hxM

theorem l2_extension_nz : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ la : La) (τ F : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → A.IsSecOn la (nz A τ) F → ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq la F y) ∂A.mu < ⊤ → ∃ G : ι → Y → ℂ, A.IsSec la G ∧ ∀ i y, y ∈ nz A τ → y ∈ (A.chart i).source → G i y = F i y := by
  intro n Y _ _ _ _ _ ι La _ A Λ la τ F hτ hdense hFs hfin
  have hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ nz A τ, ENNReal.ofReal (A.nsq la F x) ∂A.mu < ⊤ :=
    fun y => ⟨univ, univ_mem, by simpa using hfin⟩
  have hex : ∀ i, ∀ v ∈ (A.chart i).target, ∃ r > 0, Metric.ball v r ⊆ (A.chart i).target ∧
      ∃ U : V n → ℂ, DifferentiableOn ℂ U (Metric.ball v r) ∧
        EqOn U (F i ∘ (A.chart i).symm)
          (Metric.ball v r \ {u | (τ i ∘ (A.chart i).symm) u = 0}) := by
    intro i v hv
    obtain ⟨r, hr, hBt, hfin'⟩ := nz_loc A hτ hFs hloc i hv
    have hu : DifferentiableOn ℂ (F i ∘ (A.chart i).symm)
        (Metric.ball v r \ {u | (τ i ∘ (A.chart i).symm) u = 0}) :=
      (hFs.1 i).mono fun u (hu : u ∈ Metric.ball v r \ {u | (τ i ∘ (A.chart i).symm) u = 0}) =>
        ⟨hBt hu.1, (nz_coeff_ne_iff' A hτ (hBt hu.1)).1 hu.2⟩
    obtain ⟨U, hU, hUeq⟩ := ReciprocityTheory.L2DbarEstimates.ext n v r (τ i ∘ (A.chart i).symm)
      (F i ∘ (A.chart i).symm) ((nz_coeff_diff A hτ i).mono hBt) hu hfin'
    exact ⟨r, hr, hBt, U, hU, hUeq⟩
  choose! R hR hRt U hU hUeq using hex
  have hagree : ∀ i, ∀ v ∈ (A.chart i).target,
      EqOn (fun u => U i u u) (U i v) (Metric.ball v (R i v)) := by
    intro i v hv u hu
    have hut := hRt i v hv hu
    have hO : IsOpen (Metric.ball v (R i v) ∩ Metric.ball u (R i u)) :=
      Metric.isOpen_ball.inter Metric.isOpen_ball
    have hOt : Metric.ball v (R i v) ∩ Metric.ball u (R i u) ⊆ (A.chart i).target :=
      inter_subset_left.trans (hRt i v hv)
    have key := Set.EqOn.of_subset_closure
      (s := (Metric.ball v (R i v) ∩ Metric.ball u (R i u)) ∩
        {x | (τ i ∘ (A.chart i).symm) x ≠ 0})
      (f := U i v) (g := U i u) ?_ ((hU i v hv).continuousOn.mono inter_subset_left)
      ((hU i u hut).continuousOn.mono inter_subset_right) inter_subset_left
      (nz_sub_closure A hτ hdense i hO hOt)
    · exact (key ⟨hu, Metric.mem_ball_self (hR i u hut)⟩).symm
    · intro x hx
      rw [hUeq i v hv ⟨hx.1.1, hx.2⟩, hUeq i u hut ⟨hx.1.2, hx.2⟩]
  have hGcd : ∀ i, DifferentiableOn ℂ (fun u => U i u u) (A.chart i).target := by
    intro i v hv
    have hev : (fun u => U i u u) =ᶠ[𝓝 v] U i v :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds v (hR i v hv)) (hagree i v hv)
    exact (((hU i v hv).differentiableAt (Metric.ball_mem_nhds v (hR i v hv))).congr_of_eventuallyEq
      hev).differentiableWithinAt
  have hGcF : ∀ i, ∀ v ∈ (A.chart i).target, (A.chart i).symm v ∈ nz A τ →
      U i v v = F i ((A.chart i).symm v) := by
    intro i v hv hM
    exact hUeq i v hv ⟨Metric.mem_ball_self (hR i v hv), (nz_coeff_ne_iff' A hτ hv).2 hM⟩
  have hGF : ∀ i y, y ∈ nz A τ → y ∈ (A.chart i).source →
      U i (A.chart i y) (A.chart i y) = F i y := by
    intro i y hyM hys
    rw [hGcF i _ ((A.chart i).map_source hys) (by rw [(A.chart i).left_inv hys]; exact hyM),
      (A.chart i).left_inv hys]
  refine ⟨fun i y => U i (A.chart i y) (A.chart i y), ⟨fun i => ?_, ?_⟩, hGF⟩
  · refine ((hGcd i).mono inter_subset_left).congr fun u hu => ?_
    simp [(A.chart i).right_inv hu.1]
  · intro i j y _ hyi hyj
    have hcont : ∀ k, ContinuousOn (fun y => U k (A.chart k y) (A.chart k y)) (A.chart k).source :=
      fun k => (hGcd k).continuousOn.comp (A.chart k).continuousOn
        fun x hx => (A.chart k).map_source hx
    have hgc : ContinuousOn (A.g la i j) ((A.chart i).source ∩ (A.chart j).source) := by
      refine ((A.holo_g la i j).continuousOn.comp ((A.chart i).continuousOn.mono inter_subset_left)
        fun x hx => ?_).congr fun x hx => ?_
      · show A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart j).source
        refine ⟨(A.chart i).map_source hx.1, ?_⟩
        show (A.chart i).symm (A.chart i x) ∈ (A.chart j).source
        rw [(A.chart i).left_inv hx.1]; exact hx.2
      · simp [(A.chart i).left_inv hx.1]
    have hO : IsOpen ((A.chart i).source ∩ (A.chart j).source) :=
      (A.chart i).open_source.inter (A.chart j).open_source
    refine Set.EqOn.of_subset_closure
      (s := ((A.chart i).source ∩ (A.chart j).source) ∩ nz A τ)
      (f := fun y => U i (A.chart i y) (A.chart i y))
      (g := fun y => A.g la i j y * U j (A.chart j y) (A.chart j y)) ?_
      ((hcont i).mono inter_subset_left) (hgc.mul ((hcont j).mono inter_subset_right))
      inter_subset_left (hdense.open_subset_closure_inter hO) ⟨hyi, hyj⟩
    intro x hx
    simp only
    rw [hGF i x hx.2 hx.1.1, hGF j x hx.2 hx.1.2]
    exact hFs.2 i j x hx.2 hx.1.1 hx.1.2

end L2ExtNz

end

end GlobalTheory.OTY
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isSec_extension_of_dense_nz_of_l2 : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ la : La) (τ F : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → A.IsSecOn la (nz A τ) F → ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq la F y) ∂A.mu < ⊤ → ∃ G : ι → Y → ℂ, A.IsSec la G ∧ ∀ i y, y ∈ nz A τ → y ∈ (A.chart i).source → G i y = F i y := by
  atlas_forward_decl GlobalTheory.OTY.l2_extension_nz
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem zeroSet_null_of_dense_nz : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → A.mu (nz A τ)ᶜ = 0 := by
  intro n Y _ _ _ _ _ ι La _ A Λ τ hτ hd
  have hN : EXTNullStatement n := extNull n
  have hiff : ∀ i y, y ∈ (A.chart i).source → (τ (A.pick y) y ≠ 0 ↔ τ i y ≠ 0) := by
    intro i y hy
    rw [hτ.2 (A.pick y) i y trivial (A.mem_pick y) hy]
    simp [A.g_ne Λ (A.pick y) i y (A.mem_pick y) hy]
  refine measure_null_of_locally_null _ fun y _ => ?_
  have hys : y ∈ (A.chart (A.pick y)).source := A.mem_pick y
  have hv := (A.chart (A.pick y)).map_source hys
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.1 (A.chart (A.pick y)).open_target _ hv
  have hUo : IsOpen ((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) :=
    (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source Metric.isOpen_ball
  have hyU : y ∈ (A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r := ⟨hys, Metric.mem_ball_self hr⟩
  have hF : DifferentiableOn ℂ (τ (A.pick y) ∘ (A.chart (A.pick y)).symm)
      (A.chart (A.pick y)).target := by
    simpa using hτ.1 (A.pick y)
  have hcont : ContinuousOn (τ (A.pick y)) (A.chart (A.pick y)).source := by
    have := hF.continuousOn.comp (A.chart (A.pick y)).continuousOn
      (fun x hx => (A.chart (A.pick y)).map_source hx)
    refine this.congr fun x hx => ?_
    simp [Function.comp, (A.chart (A.pick y)).left_inv hx]
  have hTo : IsOpen (((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) ∩ τ (A.pick y) ⁻¹' {0}ᶜ) :=
    (hcont.mono Set.inter_subset_left).isOpen_inter_preimage hUo isOpen_compl_singleton
  refine ⟨_, inter_mem_nhdsWithin _ (hUo.mem_nhds hyU), ?_⟩
  refine measure_mono_null (t := ((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) \ (((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) ∩ τ (A.pick y) ⁻¹' {0}ᶜ)) ?_ ?_
  · rintro x ⟨hxn, hxU⟩
    refine ⟨hxU, fun h => hxn ?_⟩
    exact (hiff _ x hxU.1).2 h.2
  rw [A.mu_chart (A.pick y) _ (hUo.measurableSet.diff hTo.measurableSet)
    (Set.diff_subset.trans Set.inter_subset_left)]
  apply setLIntegral_measure_zero
  obtain ⟨y', hy'U, hy'M⟩ := hd.inter_open_nonempty _ hUo ⟨y, hyU⟩
  have hnull := hN (A.chart (A.pick y) y) r (τ (A.pick y) ∘ (A.chart (A.pick y)).symm)
    (hF.mono hB) ⟨A.chart (A.pick y) y', hy'U.2, by
      simp only [Function.comp, (A.chart _).left_inv hy'U.1]
      exact (hiff _ y' hy'U.1).1 hy'M⟩
  refine measure_mono_null ?_ hnull
  rintro _ ⟨x, ⟨hxU, hxn⟩, rfl⟩
  refine ⟨hxU.2, ?_⟩
  simp only [Set.mem_setOf_eq, Function.comp, (A.chart _).left_inv hxU.1]
  by_contra h
  exact hxn ⟨hxU, h⟩

end GlobalTheory
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_compl_nonvanishingSet_eq_zero_of_dense : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → A.mu (nz A τ)ᶜ = 0 := by
  atlas_forward_decl GlobalTheory.zeroSet_null_of_dense_nz
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.extension_values_at_zeros : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ hS : (A.zeroSet s).Finite, (∀ P ∈ A.zeroSet s, jacAt A s P ≠ 0) → (∀ y, A.sqn L s y ≤ 1) → ∀ δ : ℝ, 0 < δ → ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → ∀ (Ω : Set Y) (h : ι → Y → ℂ) (T : ℝ) (θ : ℝ → ℝ), (IsOpen Ω ∧ A.IsSecOn (A.kap + E) Ω h ∧ (∀ i y, y ∉ Ω → h i y = 0)) → A.zeroSet s ⊆ Ω → IsCut T θ → ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu < ⊤ → ∀ F : ι → Y → ℂ, A.IsSecOn (A.kap + E) (nz A τ) F → ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu < ⊤ → ∃ G : ι → Y → ℂ, A.IsSec (A.kap + E) G ∧ (∀ i y, y ∈ nz A τ → y ∈ (A.chart i).source → G i y = F i y) ∧ ∀ P ∈ A.zeroSet s, G (A.pick P) P = h (A.pick P) P := by
  intro n Y _ _ _ _ _ _ ι La _ A hn E L s hs hS hjac hle δ hδ Λ τ hτ hdense Ω h T θ hΩ hSΩ hθ hhint F hF hint
  obtain ⟨hΩo, hhsec, hh0⟩ := hΩ
  have hUo : IsOpen (nz A τ) := (GlobalTheory.T.isOpen_atlasSectionNonvanishingSet_and_mem_iff n Y ι La A Λ τ hτ).1
  have hmeas := GlobalTheory.T.measurable_nsq_and_psi_of_isSecOn n Y ι La A (A.kap + E) Ω h hΩo hhsec hh0
  have hψm : Measurable (psi A L s) := hmeas.2 L s hs
  have hψle : ∀ y, psi A L s y ≤ 0 := fun y => by
    unfold psi
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n)
      (Real.log_nonpos (A.sqn_nonneg L s y) (hle y))
  set c0 : ℝ := 1 / (1 + (T + 1) ^ 2) with hc0def
  have hc0 : 0 < c0 := by positivity
  have hwT : ∀ x, c0 ≤ wT T x := fun x => by
    unfold wT
    apply one_div_le_one_div_of_le (by positivity)
    linarith [min_le_right (x ^ 2) ((T + 1) ^ 2)]
  have hwe : ∀ y, c0 * Real.exp (-psi A L s y) ≤
      wT T (δ * psi A L s y) * Real.exp (-psi A L s y) := fun y =>
    mul_le_mul_of_nonneg_right (hwT _) (Real.exp_pos _).le
  have hexψ : ∀ y, 1 ≤ Real.exp (-psi A L s y) := fun y => Real.one_le_exp (by linarith [hψle y])
  set X : ι → Y → ℂ := fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x with hXdef

  have hpt : ∀ y, A.nsq (A.kap + E) F y ≤ 2 * A.nsq (A.kap + E) h y +
      (2 / c0) * (A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) := by
    intro y
    have hθ01 := hθ.2.2.2.1 (δ * psi A L s y)
    have key : A.nsq (A.kap + E) F y ≤ 2 * A.nsq (A.kap + E) h y + 2 * A.nsq (A.kap + E) X y := by
      simp only [WeightedAtlas.nsq, X]
      set t := θ (δ * psi A L s y)
      set a := F (A.pick y) y
      set b := h (A.pick y) y
      have n1 : ‖(t : ℂ) * b‖ ≤ ‖b‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ01.1]
        exact mul_le_of_le_one_left (norm_nonneg _) hθ01.2
      have ha : ‖a‖ ^ 2 ≤ 2 * ‖b‖ ^ 2 + 2 * ‖(t : ℂ) * b - a‖ ^ 2 := by
        have e1 : a = (t : ℂ) * b - ((t : ℂ) * b - a) := by ring
        have n2 : ‖a‖ ≤ ‖(t : ℂ) * b‖ + ‖(t : ℂ) * b - a‖ := by
          conv_lhs => rw [e1]
          exact norm_sub_le _ _
        have n3 : 0 ≤ ‖(t : ℂ) * b‖ := norm_nonneg _
        have n4 : 0 ≤ ‖(t : ℂ) * b - a‖ := norm_nonneg _
        nlinarith [sq_nonneg (‖(t : ℂ) * b‖ - ‖(t : ℂ) * b - a‖), norm_nonneg a]
      have hex := Real.exp_pos (-A.ph (A.kap + E) (A.pick y) y)
      nlinarith
    have hX0 : 0 ≤ A.nsq (A.kap + E) X y := A.nsq_nonneg _ _ _
    have hq : A.nsq (A.kap + E) X y ≤
        A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)) / c0 := by
      rw [le_div_iff₀ hc0]
      have := (hwe y)
      have h1 : c0 ≤ wT T (δ * psi A L s y) * Real.exp (-psi A L s y) := by
        nlinarith [hexψ y]
      nlinarith
    have : (2 / c0) * (A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)))
        = 2 * (A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)) / c0) := by
      ring
    rw [this]
    linarith
  have hFint : ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E) F y) ∂A.mu < ⊤ := by
    calc ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E) F y) ∂A.mu
        ≤ ∫⁻ y in nz A τ, (ENNReal.ofReal (2 * A.nsq (A.kap + E) h y) + ENNReal.ofReal ((2 / c0) *
            (A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))))) ∂A.mu :=
          lintegral_mono (fun y => (ENNReal.ofReal_le_ofReal (hpt y)).trans ENNReal.ofReal_add_le)
      _ = ∫⁻ y in nz A τ, ENNReal.ofReal (2 * A.nsq (A.kap + E) h y) ∂A.mu +
          ∫⁻ y in nz A τ, ENNReal.ofReal ((2 / c0) *
            (A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)))) ∂A.mu :=
          lintegral_add_left (ENNReal.measurable_ofReal.comp (measurable_const.mul hmeas.1)) _
      _ < ⊤ := by
        apply ENNReal.add_lt_top.2
        constructor
        · have e : ∀ y, ENNReal.ofReal (2 * A.nsq (A.kap + E) h y) =
              ENNReal.ofReal 2 * ENNReal.ofReal (A.nsq (A.kap + E) h y) :=
            fun y => ENNReal.ofReal_mul (by norm_num)
          simp_rw [e]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hhint)
        · have e : ∀ y, ENNReal.ofReal ((2 / c0) *
              (A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)))) =
              ENNReal.ofReal (2 / c0) * ENNReal.ofReal
              (A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) :=
            fun y => ENNReal.ofReal_mul (by positivity)
          simp_rw [e]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
  obtain ⟨G, hG, hGF⟩ := GlobalTheory.T.exists_isSec_extension_of_dense_nz_of_l2 n Y ι La A Λ (A.kap + E) τ F hτ hdense hF hFint
  refine ⟨G, hG, hGF, ?_⟩
  intro P hP

  have hP' : ∀ k, s k (A.pick P) P = 0 := hP
  have hsqP : A.sqn L s P = 0 := by
    simp [WeightedAtlas.sqn, WeightedAtlas.nsq, hP']
  set i := A.pick P with hidef
  set e := A.chart i with hedef
  have hPs : P ∈ e.source := A.mem_pick P
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  set ε : ℝ := Real.exp ((-T - 1) / (δ * n)) with hεdef
  set N : Set Y := (e.source ∩ A.ph E i ⁻¹' Set.Iio (A.ph E i P + 1)) ∩ Ω ∩
    (A.zeroSet s \ {P})ᶜ ∩ {y | A.sqn L s y < ε} with hNdef
  have hNo : IsOpen N := by
    refine ((((A.continuousOn_ph E i).isOpen_inter_preimage e.open_source isOpen_Iio).inter
      hΩo).inter ((hS.subset Set.diff_subset).isClosed.isOpen_compl)).inter
      (isOpen_lt (A.continuous_sqn hs) continuous_const)
  have hPN : P ∈ N := by
    refine ⟨⟨⟨⟨hPs, ?_⟩, hSΩ hP⟩, fun h' => h'.2 rfl⟩, ?_⟩
    · show A.ph E i P < A.ph E i P + 1; linarith
    · show A.sqn L s P < ε; rw [hsqP]; exact Real.exp_pos _
  set O : Set (V n) := e.target ∩ e.symm ⁻¹' N with hOdef
  have hOo : IsOpen O := e.continuousOn_symm.isOpen_inter_preimage e.open_target hNo
  have hpO : e P ∈ O := ⟨e.map_source hPs, by
    show e.symm (e P) ∈ N; rw [e.left_inv hPs]; exact hPN⟩
  set Z : V n → V n := A.zLoc (fun _ _ => 1) s i with hZdef
  set lam : V n → ℝ := fun v => A.ph L i (e.symm v) with hlamdef
  have hdiff : ∀ k, DifferentiableOn ℂ (s k i ∘ e.symm) e.target := fun k => by
    simpa using (hs k).1 i
  have hZd : DifferentiableOn ℂ Z O := by
    intro v hv
    apply DifferentiableAt.differentiableWithinAt
    rw [differentiableAt_euclidean]
    intro k
    simp only [Z, WeightedAtlas.zLoc, PiLp.toLp_apply, div_one]
    exact (hdiff k v hv.1).differentiableAt (e.open_target.mem_nhds hv.1)
  have hZp : Z (e P) = 0 := by
    have h0 : ∀ k, s k i (e.symm (e P)) = 0 := fun k => by rw [e.left_inv hPs]; exact hP' k
    ext k
    simp only [Z, WeightedAtlas.zLoc, PiLp.toLp_apply, div_one]
    first | exact h0 k | simpa using h0 k | (simp; exact h0 k)
  have hdet : (fderiv ℂ Z (e P)).det ≠ 0 := hjac P hP
  have hlam : ContinuousOn lam O :=
    ((A.smooth_ph L i).continuousOn).mono (fun v hv => hv.1)
  set u : V n → ℂ := fun v => h i (e.symm v) - G i (e.symm v) with hudef
  have hu : ContinuousOn u O := by
    have h1 : ContinuousOn (h i ∘ e.symm) O :=
      (hhsec.1 i).continuousOn.mono (fun v hv => ⟨hv.1, hv.2.1.1.2⟩)
    have h2 : ContinuousOn (G i ∘ e.symm) O :=
      (hG.1 i).continuousOn.mono (fun v hv => ⟨hv.1, trivial⟩)
    exact h1.sub h2
  have hZn : ∀ v ∈ e.target, ‖Z v‖ ^ 2 * Real.exp (-lam v) = A.sqn L s (e.symm v) := by
    intro v hv
    have hy : e.symm v ∈ e.source := e.map_target hv
    rw [A.sqn_s_eq (w0 := fun _ _ => 1) hs hy one_ne_zero, e.right_inv hv]
    simp [Z, lam]
    ring
  have hfin : ∫⁻ v in O, ENNReal.ofReal (‖u v‖ ^ 2 *
      Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) < ⊤ := by
    have hNmem : ∀ y ∈ N, y ∈ e.source ∧ A.ph E i y < A.ph E i P + 1 ∧ y ∈ Ω ∧
        y ∉ A.zeroSet s \ {P} ∧ A.sqn L s y < ε :=
      fun y hy => ⟨hy.1.1.1.1, hy.1.1.1.2, hy.1.1.2, hy.1.2, hy.2⟩
    have hUt : IsOpen (e.target ∩ e.symm ⁻¹' nz A τ) :=
      e.continuousOn_symm.isOpen_inter_preimage e.open_target hUo
    set W : Set (V n) := (O ∩ (e.target ∩ e.symm ⁻¹' nz A τ)) \ {e P} with hWdef
    have hWm : MeasurableSet W := (hOo.inter hUt).measurableSet.diff (measurableSet_singleton _)
    have hWO : W ⊆ O := fun v hv => hv.1.1
    have hWt : W ⊆ e.target := fun v hv => hv.1.1.1
    have hnull : volume (e.target ∩ e.symm ⁻¹' (nz A τ)ᶜ) = 0 := by
      have hmu0 : A.mu (e.source ∩ (nz A τ)ᶜ) = 0 :=
        measure_mono_null Set.inter_subset_right (GlobalTheory.T.measure_compl_nonvanishingSet_eq_zero_of_dense n Y ι La A Λ τ hτ hdense)
      rw [A.mu_chart i _ (e.open_source.measurableSet.inter hUo.measurableSet.compl)
        Set.inter_subset_left, e.image_source_inter_eq'] at hmu0
      have hBm : MeasurableSet (e.target ∩ e.symm ⁻¹' (nz A τ)ᶜ) := by
        have : e.target ∩ e.symm ⁻¹' (nz A τ)ᶜ = e.target \ (e.target ∩ e.symm ⁻¹' nz A τ) := by
          ext v; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_diff]
          tauto
        rw [this]; exact e.open_target.measurableSet.diff hUt.measurableSet
      have hco : ContinuousOn (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i (e.symm v))))
          e.target :=
        ENNReal.continuous_ofReal.comp_continuousOn ((A.smooth_ph A.kap i).continuousOn.rexp)
      have hae := (hco.mono Set.inter_subset_left).aemeasurable (μ := volume) hBm
      rw [lintegral_eq_zero_iff' hae] at hmu0
      have h2 : ∀ᵐ v ∂volume, v ∉ e.target ∩ e.symm ⁻¹' (nz A τ)ᶜ := by
        filter_upwards [(ae_restrict_iff' hBm).1 hmu0] with v hv hvB
        have h3 := hv hvB
        simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h3
        exact absurd h3 (not_le.2 (Real.exp_pos _))
      first | exact measure_zero_iff_ae_nmem.2 h2 | exact measure_eq_zero_iff_ae_notMem.2 h2
    have hOW : volume (O \ W) = 0 := by
      apply measure_mono_null (t := {e P} ∪ (e.target ∩ e.symm ⁻¹' (nz A τ)ᶜ))
      · intro v hv
        by_cases hvp : v = e P
        · left; exact hvp
        · right; exact ⟨hv.1.1, fun hU => hv.2 ⟨⟨hv.1, hv.1.1, hU⟩, hvp⟩⟩
      · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
        exact measure_union_null (measure_singleton _) hnull
    have hOWeq : volume.restrict O = volume.restrict W :=
      Measure.restrict_congr_set (ae_eq_set.2 ⟨hOW, by rw [Set.diff_eq_empty.2 hWO]; exact measure_empty⟩)
    rw [hOWeq]
    set c : Y → ℝ := fun y => Real.sqrt (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)) with hcdef
    set D : ι → Y → ℂ := fun j y => (c y : ℂ) * X j y with hDdef
    have hq0 : ∀ y, 0 ≤ wT T (δ * psi A L s y) * Real.exp (-psi A L s y) := fun y =>
      le_trans (mul_nonneg hc0.le (Real.exp_pos _).le) (hwe y)
    have hDsq : ∀ j y, ‖D j y‖ ^ 2 = (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)) * ‖X j y‖ ^ 2 := by
      intro j y
      simp only [D, c, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (hq0 y)]
    have hnsqD : ∀ y, A.nsq (A.kap + E) D y =
        A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)) := by
      intro y
      simp only [WeightedAtlas.nsq]
      rw [hDsq]
      ring
    have hcoc : ∀ y ∈ e.source, e y ∈ W → D (A.pick y) y = A.g (A.kap + E) (A.pick y) i y * D i y := by
      intro y hy hyW
      have hyy : e.symm (e y) = y := e.left_inv hy
      have hyU : y ∈ nz A τ := by
        have := hyW.1.2.2; rwa [Set.mem_preimage, hyy] at this
      have hyΩ : y ∈ Ω := by
        have := (hNmem _ hyW.1.1.2).2.2.1; rwa [hyy] at this
      simp only [D, X]
      rw [hhsec.2 (A.pick y) i y hyΩ (A.mem_pick y) hy, hF.2 (A.pick y) i y hyU (A.mem_pick y) hy]
      ring
    have hsymm : AEMeasurable e.symm (volume.restrict W) :=
      (e.continuousOn_symm.mono hWt).aemeasurable hWm
    have hwTc : Continuous (wT T) := by
      unfold wT
      exact continuous_const.div (by fun_prop) (fun x => by positivity)
    have hcm : Measurable c := by
      have : Measurable (fun x : ℝ => Real.sqrt (wT T (δ * x) * Real.exp (-x))) :=
        (Real.continuous_sqrt.comp ((hwTc.comp (continuous_const.mul continuous_id)).mul
          (Real.continuous_exp.comp continuous_neg))).measurable
      exact this.comp hψm
    have hDm : AEMeasurable (D i ∘ e.symm) (volume.restrict W) := by
      have h1 : AEMeasurable (fun v => (c (e.symm v) : ℂ)) (volume.restrict W) :=
        (Complex.measurable_ofReal.comp hcm).comp_aemeasurable hsymm
      have h2 : AEMeasurable (fun v => (θ (δ * psi A L s (e.symm v)) : ℂ)) (volume.restrict W) :=
        (Complex.measurable_ofReal.comp (hθ.1.continuous.measurable.comp
          (measurable_const.mul hψm))).comp_aemeasurable hsymm
      have h3 : AEMeasurable (h i ∘ e.symm) (volume.restrict W) :=
        ((hhsec.1 i).continuousOn.mono (fun v hv => ⟨hWt hv, (hNmem _ (hWO hv).2).2.2.1⟩)).aemeasurable hWm
      have h4 : AEMeasurable (F i ∘ e.symm) (volume.restrict W) :=
        ((hF.1 i).continuousOn.mono (fun v hv => ⟨hWt hv, hv.1.2.2⟩)).aemeasurable hWm
      exact h1.mul ((h2.mul h3).sub h4)
    have hconv := GlobalTheory.T.lintegral_nsq_canonical_add_chart_part n Y ι La A E i W D hWm hWt hcoc hDm
    have hbound : ∫⁻ v in W, ENNReal.ofReal (‖D i (e.symm v)‖ ^ 2 * Real.exp (-A.ph E i (e.symm v))) < ⊤ := by
      rw [← hconv]
      refine lt_of_le_of_lt (lintegral_mono_set ?_)
        (?_ : ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E) D y) ∂A.mu < ⊤)
      · intro y hy
        have := hy.2.1.2.2
        rwa [Set.mem_preimage, e.left_inv hy.1] at this
      · simp_rw [hnsqD]; exact hint
    set K : ℝ := Real.exp (A.ph E i P + 1) / c0 with hKdef
    have hK : 0 ≤ K := by positivity
    calc ∫⁻ v in W, ENNReal.ofReal (‖u v‖ ^ 2 *
          Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v)))))
        ≤ ∫⁻ v in W, ENNReal.ofReal K *
          ENNReal.ofReal (‖D i (e.symm v)‖ ^ 2 * Real.exp (-A.ph E i (e.symm v))) := by
          refine setLIntegral_mono' hWm (fun v hv => ?_)
          rw [← ENNReal.ofReal_mul hK]
          apply ENNReal.ofReal_le_ofReal
          obtain ⟨⟨⟨hvt, hvN⟩, ⟨-, hvU⟩⟩, hvp⟩ := hv
          obtain ⟨hys, hyph, hyΩ, hyS, hysq⟩ := hNmem _ hvN
          have hvy : e (e.symm v) = v := e.right_inv hvt
          have hyZ : e.symm v ∉ A.zeroSet s := by
            intro hz
            apply hvp
            have : e.symm v = P := by
              by_contra hne
              exact hyS ⟨hz, hne⟩
            show v = e P
            rw [← hvy, this]
          have hpos : 0 < A.sqn L s (e.symm v) :=
            bsA_sqn_pos A (by by_contra hc; push_neg at hc; exact hyZ hc)
          have hψlt : δ * psi A L s (e.symm v) ≤ -T - 1 := by
            have hlog : Real.log (A.sqn L s (e.symm v)) < (-T - 1) / (δ * n) :=
              (Real.log_lt_iff_lt_exp hpos).2 hysq
            have hdn : 0 < δ * n := mul_pos hδ hnpos
            have h5 := mul_lt_mul_of_pos_left hlog hdn
            have e2 : (δ * n) * ((-T - 1) / (δ * n)) = -T - 1 := by field_simp
            unfold psi
            calc δ * ((n : ℝ) * Real.log (A.sqn L s (e.symm v)))
                = (δ * n) * Real.log (A.sqn L s (e.symm v)) := by ring
              _ ≤ -T - 1 := by linarith
          have hθ1 : θ (δ * psi A L s (e.symm v)) = 1 := hθ.2.1 _ hψlt
          have hGy : G i (e.symm v) = F i (e.symm v) := hGF i _ hvU hys
          have huX : u v = X i (e.symm v) := by
            simp only [u, X, hθ1, hGy, Complex.ofReal_one, one_mul]
          rw [hZn v hvt, huX, hDsq]
          have hψdef : (n : ℝ) * Real.log (A.sqn L s (e.symm v)) = psi A L s (e.symm v) := rfl
          rw [hψdef]
          have h1 := hwe (e.symm v)
          have h2 : 1 ≤ Real.exp (A.ph E i P + 1) * Real.exp (-A.ph E i (e.symm v)) := by
            rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
          have hx2 : 0 ≤ ‖X i (e.symm v)‖ ^ 2 := by positivity
          have hq := hq0 (e.symm v)
          rw [hKdef, div_mul_eq_mul_div, le_div_iff₀ hc0]
          nlinarith [mul_le_mul_of_nonneg_left h1 hx2,
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hx2 hq)]
      _ = ENNReal.ofReal K * ∫⁻ v in W,
          ENNReal.ofReal (‖D i (e.symm v)‖ ^ 2 * Real.exp (-A.ph E i (e.symm v))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbound
  have key := GlobalTheory.T.eq_zero_at_simple_zero_of_weighted_sq_integrable n hn (e P) O Z lam hOo hpO hZd hZp hdet hlam u hu hfin
  simp only [u, e.left_inv hPs, sub_eq_zero] at key
  exact key.symm
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_across_hypersurface_values_at_zeros : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ hS : (A.zeroSet s).Finite, (∀ P ∈ A.zeroSet s, jacAt A s P ≠ 0) → (∀ y, A.sqn L s y ≤ 1) → ∀ δ : ℝ, 0 < δ → ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → ∀ (Ω : Set Y) (h : ι → Y → ℂ) (T : ℝ) (θ : ℝ → ℝ), (IsOpen Ω ∧ A.IsSecOn (A.kap + E) Ω h ∧ (∀ i y, y ∉ Ω → h i y = 0)) → A.zeroSet s ⊆ Ω → IsCut T θ → ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu < ⊤ → ∀ F : ι → Y → ℂ, A.IsSecOn (A.kap + E) (nz A τ) F → ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu < ⊤ → ∃ G : ι → Y → ℂ, A.IsSec (A.kap + E) G ∧ (∀ i y, y ∈ nz A τ → y ∈ (A.chart i).source → G i y = F i y) ∧ ∀ P ∈ A.zeroSet s, G (A.pick P) P = h (A.pick P) P := by
  atlas_forward_decl GlobalTheory.OTY.extension_values_at_zeros
end
