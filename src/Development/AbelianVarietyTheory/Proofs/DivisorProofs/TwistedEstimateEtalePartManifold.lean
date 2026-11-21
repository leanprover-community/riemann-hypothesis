import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsLocalHomeomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothEtaleOfSmoothInCharts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLeviNonnegOfChartPlurisubharmonic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenAtlasSectionNonvanishingSetAndMemIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableNsqExtendAndPsi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHolomorphicIffChartHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExtensionEtaleSteinLogGrowthWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDetIsFrameOnCanonicalWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import BuildAid.ForwardExisting

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem nzStein_germ {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    {Λ : La} {τ : ι → Y → ℂ} (hs : A.IsSec Λ τ) (i : ι) {y : Y}
    (hy : y ∈ (A.chart i).source) (hτ : τ i y ≠ 0) :
    -Real.log (A.nsq Λ τ y) = (A.ph Λ i y + 0) + Real.log (‖(τ i y)⁻¹‖ ^ 2) := by
  rw [A.nsq_eq_chart hs hy]
  have h1 : ‖τ i y‖ ^ 2 ≠ 0 := by positivity
  rw [Real.log_mul h1 (Real.exp_pos _).ne', Real.log_exp, norm_inv, inv_pow, Real.log_inv]
  ring

theorem nzStein_smoothLog {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    {Λ : La} {τ : ι → Y → ℂ} (hs : A.IsSec Λ τ) (i : ι) {y : Y}
    (hy : y ∈ (A.chart i).source) (hτ : τ i y ≠ 0) :
    ContDiffAt ℝ ∞ ((fun x => Real.log (‖(τ i x)⁻¹‖ ^ 2)) ∘ (A.chart i).symm) (A.chart i y) := by
  have hT : (A.chart i).target ∈ 𝓝 (A.chart i y) :=
    (A.chart i).open_target.mem_nhds ((A.chart i).map_source hy)
  have hd : DifferentiableOn ℂ (τ i ∘ (A.chart i).symm) (A.chart i).target := by
    simpa [WeightedAtlas.IsSec, WeightedAtlas.IsSecOn] using hs.1 i
  have hτc : ContDiffAt ℝ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y) := by
    have h : ContDiffAt ℂ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y) :=
      (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ (A.chart i).open_target hd).contDiffAt hT
    exact h.restrict_scalars ℝ
  have hne : (τ i ∘ (A.chart i).symm) (A.chart i y) ≠ 0 := by
    simpa [(A.chart i).left_inv hy] using hτ
  have hlog := ((hτc.inv hne).norm_sq ℝ).log (by simpa using hne)
  simpa [Function.comp_def] using hlog

theorem nzStein_smooth {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    {Λ : La} {τ : ι → Y → ℂ} (hs : A.IsSec Λ τ) (i : ι) {y : Y}
    (hy : y ∈ (A.chart i).source) (hτ : τ i y ≠ 0) :
    ContDiffAt ℝ ∞ ((fun x => (A.ph Λ i x + 0) + Real.log (‖(τ i x)⁻¹‖ ^ 2)) ∘ (A.chart i).symm)
      (A.chart i y) := by
  have hT : (A.chart i).target ∈ 𝓝 (A.chart i y) :=
    (A.chart i).open_target.mem_nhds ((A.chart i).map_source hy)
  have hph : ContDiffAt ℝ ∞ (A.ph Λ i ∘ (A.chart i).symm) (A.chart i y) :=
    (A.smooth_ph Λ i).contDiffAt hT
  have hd : DifferentiableOn ℂ (τ i ∘ (A.chart i).symm) (A.chart i).target := by
    simpa [WeightedAtlas.IsSec, WeightedAtlas.IsSecOn] using hs.1 i
  have hτc : ContDiffAt ℝ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y) :=
    by
    have h : ContDiffAt ℂ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y) :=
      (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ (A.chart i).open_target hd).contDiffAt hT
    exact h.restrict_scalars ℝ
  have hne : (τ i ∘ (A.chart i).symm) (A.chart i y) ≠ 0 := by
    simpa [(A.chart i).left_inv hy] using hτ
  have hinv : ContDiffAt ℝ ∞ (fun v => ((τ i ∘ (A.chart i).symm) v)⁻¹) (A.chart i y) :=
    hτc.inv hne
  have hsq : ContDiffAt ℝ ∞ (fun v => ‖((τ i ∘ (A.chart i).symm) v)⁻¹‖ ^ 2) (A.chart i y) :=
    hinv.norm_sq ℝ
  have hlog : ContDiffAt ℝ ∞ (fun v => Real.log (‖((τ i ∘ (A.chart i).symm) v)⁻¹‖ ^ 2))
      (A.chart i y) :=
    hsq.log (by simpa using hne)
  exact (hph.add contDiffAt_const).add (by simpa [Function.comp_def] using hlog)

end GlobalTheory

namespace GlobalTheory

theorem nzEtaleStein : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n), A.IsSec Λ τ → A.Pos Λ (fun _ => 0) → Etale A (nz A τ) z → ∃ X : EtaleStein n (nz A τ), X.z = (fun y : nz A τ => z y) ∧ X.e = fun y : nz A τ => -Real.log (A.nsq Λ τ y) := by
  intro n Y _ _ _ _ _ _ ι La _ A Λ τ z hs hpos hE

  have hW : ∀ x ∈ nz A τ, ∀ᶠ y in 𝓝 x, (fun y => -Real.log (A.nsq Λ τ y)) y =
      (fun y => (A.ph Λ (A.pick x) y + 0) + Real.log (‖(τ (A.pick x) y)⁻¹‖ ^ 2)) y := by
    intro x hx
    have hO : IsOpen ((A.chart (A.pick x)).source ∩ τ (A.pick x) ⁻¹' {0}ᶜ) :=
      (A.continuousOn_sec hs (A.pick x)).isOpen_inter_preimage (A.chart (A.pick x)).open_source
        isOpen_compl_singleton
    filter_upwards [hO.mem_nhds ⟨A.mem_pick x, hx⟩] with y hy
    exact nzStein_germ A hs (A.pick x) hy.1 hy.2
  have hT : ∀ x, Tendsto (A.chart (A.pick x)).symm (𝓝 (A.chart (A.pick x) x)) (𝓝 x) := by
    intro x
    have := (A.chart (A.pick x)).continuousAt_symm ((A.chart (A.pick x)).map_source (A.mem_pick x))
    rwa [ContinuousAt, (A.chart (A.pick x)).left_inv (A.mem_pick x)] at this
  have hsm : ∀ x ∈ nz A τ, ContDiffAt ℝ ∞
      ((fun y => -Real.log (A.nsq Λ τ y)) ∘ (A.chart (A.pick x)).symm) (A.chart (A.pick x) x) := by
    intro x hx
    refine (nzStein_smooth A hs (A.pick x) (A.mem_pick x) hx).congr_of_eventuallyEq ?_
    filter_upwards [(hT x).eventually (hW x hx)] with v hv
    exact hv
  have hlev : ∀ x ∈ nz A τ, ∀ ξ : Fin n → ℂ,
      0 ≤ A.leviAt (A.pick x) (fun y => -Real.log (A.nsq Λ τ y)) x ξ := by
    intro x hx ξ
    have hxi : x ∈ (A.chart (A.pick x)).source := A.mem_pick x
    rw [leviAt_congr A (A.pick x) _ _ x hxi (hW x hx) ξ]
    have hT' : (A.chart (A.pick x)).target ∈ 𝓝 (A.chart (A.pick x) x) :=
      (A.chart (A.pick x)).open_target.mem_nhds ((A.chart (A.pick x)).map_source hxi)
    have hf : ContDiffAt ℝ 2 ((fun y => A.ph Λ (A.pick x) y + 0) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x) x) := by
      have : ContDiffAt ℝ ∞ (A.ph Λ (A.pick x) ∘ (A.chart (A.pick x)).symm) (A.chart (A.pick x) x) :=
        (A.smooth_ph Λ (A.pick x)).contDiffAt hT'
      exact (this.add contDiffAt_const).of_le (WithTop.coe_le_coe.mpr le_top)
    have hg : ContDiffAt ℝ 2
        ((fun y => Real.log (‖(τ (A.pick x) y)⁻¹‖ ^ 2)) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x) x) :=
      (nzStein_smoothLog A hs (A.pick x) hxi hx).of_le (WithTop.coe_le_coe.mpr le_top)
    have hd : DifferentiableOn ℂ (τ (A.pick x) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x)).target := by
      simpa [WeightedAtlas.IsSec, WeightedAtlas.IsSecOn] using hs.1 (A.pick x)
    have hO : IsOpen ((A.chart (A.pick x)).source ∩ τ (A.pick x) ⁻¹' {0}ᶜ) :=
      (A.continuousOn_sec hs (A.pick x)).isOpen_inter_preimage (A.chart (A.pick x)).open_source
        isOpen_compl_singleton
    have hh : ∀ᶠ v in 𝓝 (A.chart (A.pick x) x),
        DifferentiableAt ℂ ((fun y => (τ (A.pick x) y)⁻¹) ∘ (A.chart (A.pick x)).symm) v := by
      filter_upwards [(A.chart (A.pick x)).open_target.mem_nhds ((A.chart (A.pick x)).map_source hxi),
        (hT x).eventually (hO.mem_nhds ⟨hxi, hx⟩)] with v hv1 hv2
      exact (hd.differentiableAt ((A.chart (A.pick x)).open_target.mem_nhds hv1)).inv hv2.2
    have E1 := leviAt_add A (A.pick x) (fun y => A.ph Λ (A.pick x) y + 0)
      (fun y => Real.log (‖(τ (A.pick x) y)⁻¹‖ ^ 2)) x hf hg ξ
    have E2 := leviAt_log_normSq A (A.pick x) (fun y => (τ (A.pick x) y)⁻¹) x hxi hh (inv_ne_zero hx) ξ
    have hp := hpos (A.pick x) x hxi ξ
    simp only at E1 E2 hp
    rw [E1, E2]
    linarith
  have hLH : IsLocalHomeomorph (fun y : nz A τ => z y) := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A _ z hE
  have hSm : SmoothR n (fun y : nz A τ => z y) (fun y : nz A τ => -Real.log (A.nsq Λ τ y)) :=
    (GlobalTheory.T.smooth_and_smoothR_of_contDiffAt_in_charts n Y ι La A _ z hE).2 (fun y => -Real.log (A.nsq Λ τ y))
      (fun x hx => ⟨A.pick x, A.mem_pick x, hsm x hx⟩)
  have hLv : LeviNonneg n (fun y : nz A τ => z y) (fun y : nz A τ => -Real.log (A.nsq Λ τ y)) :=
    GlobalTheory.T.etale_leviNonneg_of_chart_plurisubharmonic n Y ι La A _ z hE (fun y => -Real.log (A.nsq Λ τ y))
      (fun x hx => ⟨A.pick x, A.mem_pick x, hsm x hx, hlev x hx⟩)
  have hC : ∀ a : ℝ, IsCompact {y : nz A τ | -Real.log (A.nsq Λ τ y) ≤ a} := by
    intro a
    have hK : IsCompact {y : Y | Real.exp (-a) ≤ A.nsq Λ τ y} :=
      (isClosed_le continuous_const (A.continuous_nsq hs)).isCompact
    have hsub : {y : Y | Real.exp (-a) ≤ A.nsq Λ τ y} ⊆ nz A τ := by
      intro y hy
      show τ (A.pick y) y ≠ 0
      intro h0
      have h1 : Real.exp (-a) ≤ A.nsq Λ τ y := hy
      have h2 : A.nsq Λ τ y = 0 := by simp [WeightedAtlas.nsq, h0]
      have := Real.exp_pos (-a)
      linarith
    have heq : {y : nz A τ | -Real.log (A.nsq Λ τ y) ≤ a} =
        Subtype.val ⁻¹' {y : Y | Real.exp (-a) ≤ A.nsq Λ τ y} := by
      ext ⟨y, hy⟩
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      have hne : τ (A.pick y) y ≠ 0 := hy
      have hp : 0 < A.nsq Λ τ y := by
        unfold WeightedAtlas.nsq
        positivity
      rw [neg_le, Real.le_log_iff_exp_le hp]
    rw [heq, Subtype.isCompact_iff, Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hsub)]
    exact hK
  exact ⟨⟨fun y => z y, hLH, fun y => -Real.log (A.nsq Λ τ y), hSm, hLv, hC⟩, rfl, rfl⟩

end GlobalTheory
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonvanishingSet_etale_stein : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n), A.IsSec Λ τ → A.Pos Λ (fun _ => 0) → Etale A (nz A τ) z → ∃ X : EtaleStein n (nz A τ), X.z = (fun y : nz A τ => z y) ∧ X.e = fun y : nz A τ => -Real.log (A.nsq Λ τ y) := by
  atlas_forward_decl GlobalTheory.nzEtaleStein
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas

theorem frameWeight_levi : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E : La) (U : Set Y) (β J : ι → Y → ℂ), IsOpen U → A.IsFrameOn (A.kap + E) U β → A.IsFrameOn A.kap U J → ∀ x ∈ U, ∀ i, x ∈ (A.chart i).source → ContDiffAt ℝ ∞ ((fun y => -Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) ∘ (A.chart i).symm) (A.chart i x) ∧ ∀ f : Y → ℝ, ContDiffAt ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i x) → ∀ ξ : Fin n → ℂ, A.leviAt i (fun y => (-Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) + f y) x ξ = A.leviAt i (fun y => A.ph E i y + f y) x ξ := by
  intro n Y _ _ _ _ _ ι La _ A E U β J hU hβ hJ x hx i hi
  have hne : ∀ (la : La) (s : ι → Y → ℂ), A.IsFrameOn la U s → ∀ y ∈ U,
      y ∈ (A.chart i).source → s i y ≠ 0 := by
    intro la s hs y hyU hyi
    rw [hs.1.2 i (A.pick y) y hyU hyi (A.mem_pick y)]
    exact mul_ne_zero (A.g_ne _ _ _ y hyi (A.mem_pick y)) (hs.2 y hyU)
  have hloc : (fun y => (-Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y))) =ᶠ[𝓝 x]
      fun y => A.ph E i y + Real.log (‖J i y * (β i y)⁻¹‖ ^ 2) := by
    filter_upwards [(A.chart i).open_source.mem_nhds hi, hU.mem_nhds hx] with y hyi hyU
    have hp := A.mem_pick y
    have hb := hne _ β hβ y hyU hyi
    have hj := hne _ J hJ y hyU hyi
    have e1 := hyq_nsq_chart A (A.kap + E) β i y hyi (hβ.1.2 i _ y hyU hyi hp)
    have e2 := hyq_nsq_chart A A.kap J i y hyi (hJ.1.2 i _ y hyU hyi hp)
    have hb2 : 0 < ‖β i y‖ ^ 2 := by positivity
    have hj2 : 0 < ‖J i y‖ ^ 2 := by positivity
    rw [e1, e2, A.ph_add A.kap E i y hyi, norm_mul, norm_inv, mul_pow, inv_pow,
      Real.log_mul hb2.ne' (Real.exp_pos _).ne', Real.log_mul hj2.ne' (Real.exp_pos _).ne',
      Real.log_mul hj2.ne' (inv_pos.mpr hb2).ne', Real.log_inv, Real.log_exp, Real.log_exp]
    ring
  have hWo : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (A.chart i).isOpen_inter_preimage_symm hU
  have hxW : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
    ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hx]⟩
  have hc : (A.chart i).symm (A.chart i x) = x := (A.chart i).left_inv hi
  have hT := (A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)
  have hholo : ∀ (la : La) (s : ι → Y → ℂ), A.IsFrameOn la U s →
      ∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ (s i ∘ (A.chart i).symm) v := by
    intro la s hs
    filter_upwards [hWo.mem_nhds hxW] with v hv
    exact (hs.1.1 i v hv).differentiableAt (hWo.mem_nhds hv)
  have hevW : ∀ᶠ v in 𝓝 (A.chart i x), v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
    hWo.mem_nhds hxW
  have hqd : ∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ
      ((fun y => J i y * (β i y)⁻¹) ∘ (A.chart i).symm) v := by
    filter_upwards [hholo _ β hβ, hholo _ J hJ, hevW] with v h1 h2 h3
    have hb := hne _ β hβ _ h3.2 ((A.chart i).map_target h3.1)
    exact h2.mul (h1.inv hb)
  have hq : ContDiffAt ℝ ∞ ((fun y => J i y * (β i y)⁻¹) ∘ (A.chart i).symm) (A.chart i x) :=
    hyq_contDiffAt_of_ev hqd
  have hqne : ((fun y => J i y * (β i y)⁻¹) ∘ (A.chart i).symm) (A.chart i x) ≠ 0 := by
    simp only [Function.comp, hc]
    exact mul_ne_zero (hne _ J hJ x hx hi) (inv_ne_zero (hne _ β hβ x hx hi))
  have hlog : ContDiffAt ℝ ∞ ((fun y => Real.log (‖J i y * (β i y)⁻¹‖ ^ 2)) ∘ (A.chart i).symm)
      (A.chart i x) :=
    (hq.norm_sq ℝ).log (by positivity)
  have hphE : ContDiffAt ℝ ∞ (A.ph E i ∘ (A.chart i).symm) (A.chart i x) :=
    (A.smooth_ph E i).contDiffAt hT
  have ht : Filter.Tendsto (A.chart i).symm (𝓝 (A.chart i x)) (𝓝 x) := by
    have := ((A.chart i).continuousAt_symm ((A.chart i).map_source hi)).tendsto
    rwa [hc] at this
  refine ⟨?_, fun f hf ξ => ?_⟩
  · refine (hphE.add hlog).congr_of_eventuallyEq ?_
    filter_upwards [ht.eventually hloc] with v hv
    simp only [Function.comp] at hv ⊢
    rw [hv]
  · have hloc' : (fun y => (-Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) + f y)
        =ᶠ[𝓝 x] fun y => (A.ph E i y + f y) + Real.log (‖J i y * (β i y)⁻¹‖ ^ 2) := by
      filter_upwards [hloc] with y hy
      rw [hy]; ring
    have hf2 : ContDiffAt ℝ 2 ((fun y => A.ph E i y + f y) ∘ (A.chart i).symm) (A.chart i x) :=
      (hphE.add hf).of_le (WithTop.coe_le_coe.mpr le_top)
    have hg2 : ContDiffAt ℝ 2 ((fun y => Real.log (‖J i y * (β i y)⁻¹‖ ^ 2)) ∘ (A.chart i).symm)
        (A.chart i x) := hlog.of_le (WithTop.coe_le_coe.mpr le_top)
    rw [leviAt_congr A i _ _ x hi hloc' ξ,
      leviAt_add A i (fun y => A.ph E i y + f y)
        (fun y => Real.log (‖J i y * (β i y)⁻¹‖ ^ 2)) x hf2 hg2 ξ,
      leviAt_log_normSq A i (fun y => J i y * (β i y)⁻¹) x hi hqd
        (mul_ne_zero (hne _ J hJ x hx hi) (inv_ne_zero (hne _ β hβ x hx hi))) ξ, add_zero]

end GlobalTheory
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviAt_log_nsq_ratio_eq_leviAt_ph : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E : La) (U : Set Y) (β J : ι → Y → ℂ), IsOpen U → A.IsFrameOn (A.kap + E) U β → A.IsFrameOn A.kap U J → ∀ x ∈ U, ∀ i, x ∈ (A.chart i).source → ContDiffAt ℝ ∞ ((fun y => -Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) ∘ (A.chart i).symm) (A.chart i x) ∧ ∀ f : Y → ℝ, ContDiffAt ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i x) → ∀ ξ : Fin n → ℂ, A.leviAt i (fun y => (-Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) + f y) x ξ = A.leviAt i (fun y => A.ph E i y + f y) x ξ := by
  atlas_forward_decl GlobalTheory.frameWeight_levi
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem contDiffAt_psi_of_notMem_zeroSet : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ y, y ∉ A.zeroSet s → ∀ i, y ∈ (A.chart i).source → ContDiffAt ℝ ∞ (psi A L s ∘ (A.chart i).symm) (A.chart i y) := by
  intro n Y _ _ _ _ _ ι La _ A L s hs y hy i hi
  have hv : A.chart i y ∈ (A.chart i).target := (A.chart i).map_source hi
  have hU : (A.chart i).target ∈ 𝓝 (A.chart i y) := (A.chart i).open_target.mem_nhds hv
  have hsk : ∀ k, ContDiffAt ℝ ∞ (s k i ∘ (A.chart i).symm) (A.chart i y) := fun k =>
    hyq_contDiffAt_of_holo (A.chart i).open_target (by simpa using (hs k).1 i) hv
  have hph : ContDiffAt ℝ ∞ (A.ph L i ∘ (A.chart i).symm) (A.chart i y) :=
    (A.smooth_ph L i).contDiffAt hU
  have h1 : ContDiffAt ℝ ∞ (fun v => ∑ k, ‖(s k i ∘ (A.chart i).symm) v‖ ^ 2 *
      Real.exp (-(A.ph L i ∘ (A.chart i).symm) v)) (A.chart i y) :=
    ContDiffAt.sum fun k _ => ((hsk k).norm_sq ℂ).mul hph.neg.exp
  have h2 : ContDiffAt ℝ ∞ (A.sqn L s ∘ (A.chart i).symm) (A.chart i y) := by
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hU] with v hv'
    simp only [Function.comp, WeightedAtlas.sqn]
    exact Finset.sum_congr rfl fun k _ =>
      WeightedAtlas.nsq_eq_chart A (hs k) ((A.chart i).map_target hv')
  have hpos : 0 < A.sqn L s y := by
    obtain ⟨k, hk⟩ : ∃ k, s k (A.pick y) y ≠ 0 := by
      by_contra h
      exact hy fun k => by_contra fun hk => h ⟨k, hk⟩
    unfold WeightedAtlas.sqn WeightedAtlas.nsq
    refine Finset.sum_pos' (fun _ _ => by positivity) ⟨k, Finset.mem_univ _, ?_⟩
    have := norm_pos_iff.2 hk
    positivity
  have h3 : (A.sqn L s ∘ (A.chart i).symm) (A.chart i y) ≠ 0 := by
    simp only [Function.comp, (A.chart i).left_inv hi]
    exact hpos.ne'
  exact contDiffAt_const.mul (h2.log h3)

end GlobalTheory.OTY
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffAt_psi_chart_of_not_mem_zeroSet : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ y, y ∉ A.zeroSet s → ∀ i, y ∈ (A.chart i).source → ContDiffAt ℝ ∞ (psi A L s ∘ (A.chart i).symm) (A.chart i y) := by
  atlas_forward_decl GlobalTheory.OTY.contDiffAt_psi_of_notMem_zeroSet
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ δ : ℝ, (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → (∀ y ∈ U, y ∉ A.zeroSet s) → SmoothR n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y) ∧ SmoothR n (fun y : U => z y) (fun y : U => psi A L s y) ∧ ∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y + α * psi A L s y) := by
  intro n Y _ _ _ _ _ ι La _ A E L s hs δ hlevi U z β hz hβ hU
  have hJ := GlobalTheory.T.jacobianDet_isFrameOn_canonicalWeight n Y ι La A U z hz
  have hW := GlobalTheory.T.leviAt_log_nsq_ratio_eq_leviAt_ph n Y ι La A E U β (jdet A z) hz.isOpen hβ hJ
  have hP : ∀ x ∈ U, ∀ i, x ∈ (A.chart i).source →
      ContDiffAt ℝ ∞ (psi A L s ∘ (A.chart i).symm) (A.chart i x) :=
    fun x hx i hi => GlobalTheory.T.contDiffAt_psi_chart_of_not_mem_zeroSet n Y ι La A L s hs x (hU x hx) i hi
  have hS := (GlobalTheory.T.smooth_and_smoothR_of_contDiffAt_in_charts n Y ι La A U z hz).2
  refine ⟨hS (GlobalTheory.OTY.TwEst.wt A E β z)
      (fun x hx => ⟨A.pick x, A.mem_pick x, (hW x hx _ (A.mem_pick x)).1⟩),
    hS (psi A L s) (fun x hx => ⟨A.pick x, A.mem_pick x, hP x hx _ (A.mem_pick x)⟩), ?_⟩
  intro α hα
  refine GlobalTheory.T.etale_leviNonneg_of_chart_plurisubharmonic n Y ι La A U z hz (fun y => GlobalTheory.OTY.TwEst.wt A E β z y + α * psi A L s y)
    (fun x hx => ⟨A.pick x, A.mem_pick x, ?_, fun ξ => ?_⟩)
  · exact (hW x hx _ (A.mem_pick x)).1.add (contDiffAt_const.mul (hP x hx _ (A.mem_pick x)))
  · have hc : ContDiffAt ℝ ∞ ((fun y => α * psi A L s y) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x) x) :=
      contDiffAt_const.mul (hP x hx _ (A.mem_pick x))
    exact le_of_le_of_eq (hlevi α hα (A.pick x) x (A.mem_pick x) (hU x hx) ξ)
      ((hW x hx _ (A.mem_pick x)).2 _ hc ξ).symm
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameWeight_singularWeight_smooth_leviNonneg : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ δ : ℝ, (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → (∀ y ∈ U, y ∉ A.zeroSet s) → SmoothR n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y) ∧ SmoothR n (fun y : U => z y) (fun y : U => psi A L s y) ∧ ∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y + α * psi A L s y) := by
  atlas_forward_decl GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
theorem _root_.GlobalTheory.OTY.TwEst.quot_holo_measurable : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La), ∀ (la : La) (U Ω : Set Y) (β h : ι → Y → ℂ), IsOpen U → IsOpen Ω →
    A.IsFrameOn la U β → A.IsSecOn la Ω h → (∀ i y, y ∉ Ω → h i y = 0) →
    (∀ i, DifferentiableOn ℂ (_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω))) ∧
    Measurable (_root_.GlobalTheory.OTY.TwEst.ext0 U (fun y : U => _root_.GlobalTheory.OTY.TwEst.quot A h β y)) ∧
    ∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * _root_.GlobalTheory.OTY.TwEst.quot A h β y := by
  intro n Y _ _ _ _ _ ι La _ A la U Ω β h hU hΩ hβ hh h0
  classical
  obtain ⟨⟨hβhol, hβcoc⟩, hβne⟩ := hβ
  obtain ⟨hhhol, hhcoc⟩ := hh
  have hq : ∀ y, _root_.GlobalTheory.OTY.TwEst.quot A h β y = h (A.pick y) y / β (A.pick y) y := fun y => by
    unfold _root_.GlobalTheory.OTY.TwEst.quot; rfl
  have hβi : ∀ i, ∀ y ∈ (A.chart i).source, y ∈ U → β i y ≠ 0 := by
    intro i y hy hyU hzero
    apply hβne y hyU
    rw [hβcoc (A.pick y) i y hyU (A.mem_pick y) hy, hzero, mul_zero]
  have hqe : ∀ i, ∀ y ∈ (A.chart i).source, y ∈ U →
      _root_.GlobalTheory.OTY.TwEst.quot A h β y = h i y / β i y := by
    intro i y hy hyU
    rw [hq]
    by_cases hyΩ : y ∈ Ω
    · rw [hhcoc (A.pick y) i y hyΩ (A.mem_pick y) hy, hβcoc (A.pick y) i y hyU (A.mem_pick y) hy,
        mul_div_mul_left _ _ (A.g_ne la _ _ y (A.mem_pick y) hy)]
    · rw [h0 _ _ hyΩ, h0 _ _ hyΩ, zero_div, zero_div]
  have hdiff : ∀ i, DifferentiableOn ℂ (_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω)) := by
    intro i
    set S := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω) with hS
    have h1 : DifferentiableOn ℂ (h i ∘ (A.chart i).symm) S :=
      (hhhol i).mono fun v hv => ⟨hv.1, hv.2.2⟩
    have h2 : DifferentiableOn ℂ (β i ∘ (A.chart i).symm) S :=
      (hβhol i).mono fun v hv => ⟨hv.1, hv.2.1⟩
    have h3 : ∀ v ∈ S, (β i ∘ (A.chart i).symm) v ≠ 0 := fun v hv =>
      hβi i _ ((A.chart i).map_target hv.1) hv.2.1
    have hd : DifferentiableOn ℂ
        (fun v => (h i ∘ (A.chart i).symm) v * ((β i ∘ (A.chart i).symm) v)⁻¹) S :=
      h1.mul (h2.inv h3)
    refine hd.congr fun v hv => ?_
    simp only [Function.comp_apply, ← div_eq_mul_inv]
    exact hqe i _ ((A.chart i).map_target hv.1) hv.2.1
  refine ⟨hdiff, ?_, fun y hy => ?_⟩
  · have hopen : IsOpen (U ∩ Ω) := hU.inter hΩ
    have hcont : ContinuousOn (_root_.GlobalTheory.OTY.TwEst.quot A h β) (U ∩ Ω) := by
      intro y hy
      set i := A.pick y
      have hys : y ∈ (A.chart i).source := A.mem_pick y
      have hset : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω)) :=
        (A.chart i).isOpen_inter_preimage_symm hopen
      have hmem : A.chart i y ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω) :=
        ⟨(A.chart i).map_source hys, by
          simp only [Set.mem_preimage, (A.chart i).left_inv hys]; exact hy⟩
      have hca : ContinuousAt (_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm) (A.chart i y) :=
        ((hdiff i).continuousOn).continuousAt (hset.mem_nhds hmem)
      have hcomp : ContinuousAt ((_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm) ∘ A.chart i) y :=
        hca.comp ((A.chart i).continuousAt hys)
      refine (hcomp.congr ?_).continuousWithinAt
      filter_upwards [(A.chart i).open_source.mem_nhds hys] with w hw
      simp [(A.chart i).left_inv hw]
    have heq : _root_.GlobalTheory.OTY.TwEst.ext0 U (fun y : U => _root_.GlobalTheory.OTY.TwEst.quot A h β y) =
        (U ∩ Ω).piecewise (_root_.GlobalTheory.OTY.TwEst.quot A h β) 0 := by
      funext y
      unfold _root_.GlobalTheory.OTY.TwEst.ext0
      by_cases hyU : y ∈ U
      · by_cases hyΩ : y ∈ Ω
        · simp [hyU, hyΩ, Set.piecewise]
        · simp [hyU, hyΩ, Set.piecewise, hq, h0 _ _ hyΩ]
      · simp [hyU, Set.piecewise]
    rw [heq]
    exact hcont.measurable_piecewise continuousOn_const hopen.measurableSet
  · rw [hq, mul_div_cancel₀ _ (hβne y hy)]
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionQuotient_holomorphic_measurable : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (U Ω : Set Y) (β h : ι → Y → ℂ), IsOpen U → IsOpen Ω → A.IsFrameOn la U β → A.IsSecOn la Ω h → (∀ i y, y ∉ Ω → h i y = 0) → (∀ i, DifferentiableOn ℂ (GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω))) ∧ Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) ∧ ∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y := by
  atlas_forward_decl GlobalTheory.OTY.TwEst.quot_holo_measurable
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.holo_etale_iff_charts : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ u : Y → ℂ, (Holo n (fun y : U => z y) (fun y : U => u y) ↔ ∀ i, DifferentiableOn ℂ (u ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)) := by
  intro n Y _ _ _ _ _ ι La _ A U z hz u
  have h := GlobalTheory.T.etale_holomorphic_iff_chart_holomorphic n Y ι La A U z hz Set.univ u isOpen_univ
  simp only [Set.preimage_univ, Set.inter_univ] at h
  exact h
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holo_iff_differentiableOn_charts_of_etale : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ u : Y → ℂ, (Holo n (fun y : U => z y) (fun y : U => u y) ↔ ∀ i, DifferentiableOn ℂ (u ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)) := by
  atlas_forward_decl GlobalTheory.holo_etale_iff_charts
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.isSecOn_frame_mul_ext0_and_measurable : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ) (F0 : U → ℂ), Etale A U z → A.IsFrameOn la U β → Holo n (fun y : U => z y) F0 → A.IsSecOn la U (fun i y => β i y * GlobalTheory.OTY.TwEst.ext0 U F0 y) ∧ Measurable (GlobalTheory.OTY.TwEst.ext0 U F0) := by
  intro n Y _ _ _ _ _ ι La _ A la U z β F0 hE hβ hF
  have hfun : (fun y : U => GlobalTheory.OTY.TwEst.ext0 U F0 y) = F0 :=
    funext fun y => GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U F0 y
  have hd := (GlobalTheory.T.holo_iff_differentiableOn_charts_of_etale n Y ι La A U z hE (GlobalTheory.OTY.TwEst.ext0 U F0)).1 (by rw [hfun]; exact hF)
  refine ⟨⟨fun i => (hβ.1.1 i).mul (hd i), fun i j y hy hi hj => ?_⟩, ?_⟩
  · show β i y * _ = _ * (β j y * _)
    rw [hβ.1.2 i j y hy hi hj, mul_assoc]
  · have hc : ContinuousOn (GlobalTheory.OTY.TwEst.ext0 U F0) U := by
      intro y hy
      have hs := A.mem_pick y
      set e := A.chart (A.pick y) with he
      have hop : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hE.isOpen
      have hm : e y ∈ e.target ∩ e.symm ⁻¹' U :=
        ⟨e.map_source hs, by simpa [e.left_inv hs] using hy⟩
      have h1 : ContinuousAt (GlobalTheory.OTY.TwEst.ext0 U F0 ∘ e.symm) (e y) :=
        (hd (A.pick y)).continuousOn.continuousAt (hop.mem_nhds hm)
      have h2 : ContinuousAt ((GlobalTheory.OTY.TwEst.ext0 U F0 ∘ e.symm) ∘ e) y :=
        h1.comp (e.continuousAt hs)
      refine (h2.congr ?_).continuousWithinAt
      filter_upwards [e.open_source.mem_nhds hs] with x hx
      simp [e.left_inv hx]
    classical
    have hm := hc.measurable_piecewise (continuousOn_const (c := (0 : ℂ)) (s := Uᶜ))
      hE.isOpen.measurableSet
    convert hm using 1
    funext y
    by_cases hy : y ∈ U
    · simp [hy]
    · simp [hy, GlobalTheory.OTY.TwEst.ext0]
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSection_holomorphic_mul_frame_extendByZero : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ) (F0 : U → ℂ), Etale A U z → A.IsFrameOn la U β → Holo n (fun y : U => z y) F0 → A.IsSecOn la U (fun i y => β i y * GlobalTheory.OTY.TwEst.ext0 U F0 y) ∧ Measurable (GlobalTheory.OTY.TwEst.ext0 U F0) := by
  atlas_forward_decl GlobalTheory.OTY.TwEst.isSecOn_frame_mul_ext0_and_measurable
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.EtaleMeasure

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

def rho (A : WeightedAtlas n Y ι La) (U : Set Y) (z : Y → V n) (x : U) : ℝ≥0∞ :=
  ENNReal.ofReal (A.nsq A.kap (jdet A z) x)⁻¹

theorem rho_measurable (A : WeightedAtlas n Y ι La) {U : Set Y} {z : Y → V n}
    (hE : Etale A U z) : Measurable (rho A U z) := by
  have hfr := GlobalTheory.T.jacobianDet_isFrameOn_canonicalWeight n Y ι La A U z hE
  have hc : ContinuousOn (A.nsq A.kap (jdet A z)) U := api_nsq_contOn A hE.isOpen hfr.1
  have hc' : Continuous (fun x : U => A.nsq A.kap (jdet A z) x) := hc.restrict
  exact ENNReal.measurable_ofReal.comp hc'.measurable.inv

theorem mu_piece (A : WeightedAtlas n Y ι La) {U : Set Y} {z : Y → V n}
    (hE : Etale A U z) (e : OpenPartialHomeomorph U (V n))
    (he : IsChart n (fun y : U => z y) e) (i : ι) (B : Set U)
    (hB : MeasurableSet B) (hBs : B ⊆ e.source) (hBi : ∀ m ∈ B, (m : Y) ∈ (A.chart i).source) :
    A.mu.comap Subtype.val B = ∫⁻ m in B, rho A U z m ∂vol n (fun y : U => z y) := by
  have hUm : MeasurableSet U := hE.isOpen.measurableSet
  have hemb := MeasurableEmbedding.subtype_coe hUm
  have hz : IsLocalHomeomorph (fun y : U => z y) := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A U z hE
  have hfr := GlobalTheory.T.jacobianDet_isFrameOn_canonicalWeight n Y ι La A U z hE
  have hρ : Measurable (rho A U z) := rho_measurable A hE
  rw [hemb.comap_apply]
  have hBY : MeasurableSet (Subtype.val '' B : Set Y) := hemb.measurableSet_image.2 hB
  rw [A.mu_chart i _ hBY (by rintro _ ⟨m, hm, rfl⟩; exact hBi m hm)]
  have hBimg : MeasurableSet (e '' B) := by
    have := measurableSet_image_of_chart n (fun y : U => z y) e he B hB hBs
    rwa [Set.image_congr fun m hm => he (hBs hm)] at this
  have hR : ∫⁻ m in B, rho A U z m ∂vol n (fun y : U => z y) =
      ∫⁻ w in e '' B, rho A U z (e.symm w) := by
    rw [← lintegral_indicator hB, lintegral_vol_chart n _ hz e he _ (hρ.indicator hB)
      (fun m hm => Set.indicator_of_notMem (fun h => hm (hBs h)) _)]
    have hsub : e '' B ⊆ e.target := fun _ ⟨m, hm, hmw⟩ => hmw ▸ e.map_source (hBs hm)
    rw [← Set.inter_eq_left.2 hsub, ← Measure.restrict_restrict hBimg, ← lintegral_indicator hBimg]
    refine setLIntegral_congr_fun e.open_target.measurableSet fun w hw => ?_
    by_cases h : e.symm w ∈ B
    · have hw' : w ∈ e '' B := ⟨e.symm w, h, e.right_inv hw⟩
      simp only [Set.indicator_of_mem h, Set.indicator_of_mem hw']
    · have hw' : w ∉ e '' B := by
        rintro ⟨m, hm, rfl⟩
        exact h (by rw [e.left_inv (hBs hm)]; exact hm)
      simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem hw']
  set F : V n → V n := z ∘ (A.chart i).symm with hFdef
  set S := A.chart i '' (Subtype.val '' B)
  have hS : MeasurableSet S :=
    measurableSet_image_of_chart n (A.chart i) (A.chart i) (fun _ _ => rfl) _ hBY
      (by rintro _ ⟨m, hm, rfl⟩; exact hBi m hm)
  have hOo : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (A.chart i).isOpen_inter_preimage_symm hE.isOpen
  have hSO : S ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U := by
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨(A.chart i).map_source (hBi m hm), ?_⟩
    show (A.chart i).symm (A.chart i m) ∈ U
    rw [(A.chart i).left_inv (hBi m hm)]; exact m.2
  have hFm : ∀ m ∈ B, F (A.chart i m) = e m := fun m hm => by
    simp only [hFdef, Function.comp_apply, (A.chart i).left_inv (hBi m hm)]
    exact he (hBs hm)
  have himg : e '' B = F '' S := by
    rw [Set.image_image, Set.image_image]
    exact (Set.image_congr fun m hm => hFm m hm).symm
  have hinj : Set.InjOn F S := by
    rintro _ ⟨_, ⟨m1, hm1, rfl⟩, rfl⟩ _ ⟨_, ⟨m2, hm2, rfl⟩, rfl⟩ h
    rw [hFm m1 hm1, hFm m2 hm2] at h
    rw [e.injOn (hBs hm1) (hBs hm2) h]
  have hder : ∀ v ∈ S, HasFDerivWithinAt F
      ((fderiv ℂ F v).restrictScalars ℝ) S v := fun v hv =>
    ((((hE.holo i).differentiableAt (hOo.mem_nhds (hSO hv))).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt
  rw [hR, himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hder hinj]
  refine setLIntegral_congr_fun hS ?_
  rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
  have hmi := hBi m hm
  have hne : jdet A z i m ≠ 0 := hE.det_ne i m m.2 hmi
  have hns := api_nsq_eq A hfr.1 hmi m.2
  have hjd : (fderiv ℂ F (A.chart i m)).det = jdet A z i m := rfl
  simp only
  rw [hFm m hm, e.left_inv (hBs hm), (A.chart i).left_inv hmi, rho, ← hns,
    ← ENNReal.ofReal_mul (abs_nonneg _), fc_det_real, hjd]
  congr 1
  have h2 : 0 < ‖jdet A z i m‖ ^ 2 := by positivity
  rw [mul_inv, Real.exp_neg, inv_inv]
  field_simp

end

end GlobalTheory.EtaleMeasure

namespace GlobalTheory.EtaleMeasure

theorem lintegral_mu_etale : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ φ : Y → ℝ≥0∞, Measurable φ → ∫⁻ y in U, φ y ∂A.mu = ∫⁻ x : U, φ x * ENNReal.ofReal (A.nsq A.kap (jdet A z) x)⁻¹ ∂vol n (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE φ hφ
  have hUm : MeasurableSet U := hE.isOpen.measurableSet
  have hz : IsLocalHomeomorph (fun y : U => z y) := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A U z hE
  have hρ : Measurable (rho A U z) := rho_measurable A hE
  have hmeas : A.mu.comap Subtype.val = (vol n (fun y : U => z y)).withDensity (rho A U z) := by
    choose e he hxe using fun x : U => exists_chart n _ hz x
    let W : U → Set U := fun x =>
      (e x).source ∩ Subtype.val ⁻¹' (A.chart (A.pick x)).source
    have hWo : ∀ x, IsOpen (W x) := fun x =>
      (e x).open_source.inter ((A.chart _).open_source.preimage continuous_subtype_val)
    obtain ⟨T, hTc, hTW⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
    have huniv : ⋃ t : T, W t = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      have hx : x ∈ ⋃ i ∈ T, W i := hTW ▸ Set.mem_iUnion.2 ⟨x, hxe x, A.mem_pick _⟩
      obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 hx
      exact Set.mem_iUnion.2 ⟨⟨t, ht⟩, hxt⟩
    haveI := hTc.to_subtype
    refine Measure.ext_of_iUnion_eq_univ huniv fun t => ?_
    ext B hB
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
      withDensity_apply _ (hB.inter (hWo t).measurableSet)]
    exact mu_piece A hE (e t) (he t) (A.pick (t : Y)) (B ∩ W t)
      (hB.inter (hWo t).measurableSet) (fun m hm => hm.2.1) (fun m hm => hm.2.2)
  rw [← lintegral_subtype_comap hUm, hmeas]
  exact (lintegral_withDensity_eq_lintegral_mul _ hρ (hφ.comp measurable_subtype_coe)).trans
    (lintegral_congr fun x => mul_comm _ _)

end GlobalTheory.EtaleMeasure
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_atlasMeasure_etale_pullback_lebesgue : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ φ : Y → ℝ≥0∞, Measurable φ → ∫⁻ y in U, φ y ∂A.mu = ∫⁻ x : U, φ x * ENNReal.ofReal (A.nsq A.kap (jdet A z) x)⁻¹ ∂vol n (fun y : U => z y) := by
  atlas_forward_decl GlobalTheory.EtaleMeasure.lintegral_mu_etale
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.lintegral_frame_transfer : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E : La) (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → ∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A E U z β hE hβ a w ha hw hw0
  classical
  have hUm : MeasurableSet U := hE.isOpen.measurableSet
  have hc := api_nsq_contOn A hE.isOpen hβ.1
  have hm := ContinuousOn.measurable_piecewise hc
    (continuousOn_const (c := (0 : ℝ)) (s := Uᶜ)) hUm
  set N : Y → ℝ := U.piecewise (A.nsq (A.kap + E) β) (fun _ => 0) with hN
  have hNU : ∀ y ∈ U, N y = A.nsq (A.kap + E) β y := fun y hy => by simp [hN, hy]
  have hΦ : Measurable fun y => ENNReal.ofReal (N y * ‖a y‖ ^ 2 * w y) :=
    ENNReal.measurable_ofReal.comp ((hm.mul (ha.norm.pow_const 2)).mul hw)
  rw [setLIntegral_congr_fun hUm
    (g := fun y => ENNReal.ofReal (N y * ‖a y‖ ^ 2 * w y)) (fun y hy => by simp only [hNU y hy]),
    GlobalTheory.T.lintegral_atlasMeasure_etale_pullback_lebesgue n Y ι La A U z hE _ hΦ]
  refine lintegral_congr fun x => ?_
  have hJ : 0 < A.nsq A.kap (jdet A z) x := by
    have := hE.det_ne (A.pick (x : Y)) x x.2 (A.mem_pick _)
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr this) 2) (Real.exp_pos _)
  have hB : 0 < A.nsq (A.kap + E) β x := by
    have : β (A.pick (x : Y)) x ≠ 0 := by
      exact hβ.2 _ x.2
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr this) 2) (Real.exp_pos _)
  have hwx := hw0 x x.2
  rw [hNU x x.2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold GlobalTheory.OTY.TwEst.wt
  rw [neg_add, neg_neg, Real.exp_add, Real.exp_neg, Real.exp_log hB, Real.exp_log hJ]
  ring
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_weightedAtlas_frame_etale_transfer : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E : La) (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → ∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y) := by
  atlas_forward_decl GlobalTheory.OTY.TwEst.lintegral_frame_transfer
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.rhs_le_manifold : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ δ T : ℝ, ∫⁻ x in {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1}, ENNReal.ofReal (‖GlobalTheory.OTY.TwEst.quot A h β x‖ ^ 2 * Real.exp (-(GlobalTheory.OTY.TwEst.wt A E β z x + psi A L s x))) ∂vol n (fun y : U => z y) ≤ ∫⁻ y in {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu := by
  intro n Y _ _ _ _ _ ι La _ A E L s U z β h hU htr hq hm hpsi δ T
  set S : Set Y := {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1} with hS
  have hδ : Measurable fun y => δ * psi A L s y := hpsi.const_mul δ
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const hδ).inter (measurableSet_le hδ measurable_const)
  have hw : Measurable (S.indicator fun y => Real.exp (-psi A L s y)) :=
    (Real.measurable_exp.comp hpsi.neg).indicator hSm
  have key := htr _ _ hm hw (fun y _ => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) y)
  have hS' : MeasurableSet {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1} :=
    measurable_subtype_coe hSm
  rw [← lintegral_indicator hS']
  refine le_trans (le_of_eq ?_) (le_trans key.ge ?_)
  · refine lintegral_congr fun x => ?_
    rw [GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe]
    by_cases hx : (x : Y) ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1} from hx), ← Real.exp_add]
      congr 3
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1} from hx)]
      simp
  · rw [← lintegral_indicator hSm, ← lintegral_indicator hU.measurableSet]
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ U
    · rw [Set.indicator_of_mem hy]
      by_cases hx : y ∈ S
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        have h0 := GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) ⟨y, hy⟩
        simp only at h0
        rw [h0]
        apply le_of_eq
        congr 2
        unfold WeightedAtlas.nsq
        rw [hq y hy, norm_mul]
        ring
      · rw [Set.indicator_of_notMem hx]
        simp
    · rw [Set.indicator_of_notMem hy]
      exact zero_le
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedEstimate_rhs_le_manifold : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ δ T : ℝ, ∫⁻ x in {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1}, ENNReal.ofReal (‖GlobalTheory.OTY.TwEst.quot A h β x‖ ^ 2 * Real.exp (-(GlobalTheory.OTY.TwEst.wt A E β z x + psi A L s x))) ∂vol n (fun y : U => z y) ≤ ∫⁻ y in {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu := by
  atlas_forward_decl GlobalTheory.OTY.TwEst.rhs_le_manifold
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.cutoff_quot_wint_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ (δ : ℝ) (θ : ℝ → ℝ), Continuous θ → (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) → wint n (fun y : U => z y) (fun x : U => (θ (δ * psi A L s x) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β x) (fun x : U => GlobalTheory.OTY.TwEst.wt A E β z x) ≤ ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu := by
  intro n Y _ _ _ _ _ ι La _ A E L s U z β h hU htr hq hm hpsi δ θ hθ hθ1
  have hma : Measurable (fun y : Y => (θ (δ * psi A L s y) : ℂ) * GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y) :=
    (Complex.measurable_ofReal.comp (hθ.measurable.comp (hpsi.const_mul δ))).mul hm
  have key := htr _ (fun _ => 1) hma measurable_const (fun _ _ => zero_le_one)
  simp only [GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe, one_mul, mul_one] at key
  unfold wint
  rw [← key]
  refine le_trans (setLIntegral_mono' hU.measurableSet ?_) (setLIntegral_le_lintegral U _)
  intro y hy
  apply ENNReal.ofReal_le_ofReal
  have e : GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y = GlobalTheory.OTY.TwEst.quot A h β y :=
    GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) ⟨y, hy⟩
  rw [e]
  unfold WeightedAtlas.nsq
  rw [hq y hy, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hθ1 _).1]
  obtain ⟨h0, h1⟩ := hθ1 (δ * psi A L s y)
  have h2 : θ (δ * psi A L s y) ^ 2 ≤ 1 := by nlinarith
  set t := θ (δ * psi A L s y)
  set b := ‖β (A.pick y) y‖
  set q := ‖GlobalTheory.OTY.TwEst.quot A h β y‖
  generalize hc : Real.exp _ = c
  have hc0 : 0 ≤ c := hc ▸ (Real.exp_pos _).le
  have h3 : 0 ≤ (b * q) ^ 2 * c := by positivity
  calc b ^ 2 * c * (t * q) ^ 2 = t ^ 2 * ((b * q) ^ 2 * c) := by ring
    _ ≤ 1 * ((b * q) ^ 2 * c) := mul_le_mul_of_nonneg_right h2 h3
    _ = _ := one_mul _
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_l2_estimate_twisted_sections : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ (δ : ℝ) (θ : ℝ → ℝ), Continuous θ → (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) → wint n (fun y : U => z y) (fun x : U => (θ (δ * psi A L s x) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β x) (fun x : U => GlobalTheory.OTY.TwEst.wt A E β z x) ≤ ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu := by
  atlas_forward_decl GlobalTheory.OTY.TwEst.cutoff_quot_wint_le
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.lhs_transfer : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ (δ T : ℝ) (θ : ℝ → ℝ) (F0 : U → ℂ), Continuous θ → Measurable (GlobalTheory.OTY.TwEst.ext0 U F0) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - β i x * GlobalTheory.OTY.TwEst.ext0 U F0 x) y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖(θ (δ * psi A L s x) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β x - F0 x‖ ^ 2 * (wT T (δ * psi A L s x) * Real.exp (-(GlobalTheory.OTY.TwEst.wt A E β z x + psi A L s x)))) ∂vol n (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A E L s U z β h hU htr hq hqm hpsi δ T θ F0 hθ hF0
  have hm : Measurable fun y => δ * psi A L s y := hpsi.const_mul δ
  have hwc : Continuous (wT T) := by
    unfold wT
    refine continuous_const.div (by fun_prop) fun x => ?_
    have : 0 ≤ min (x ^ 2) ((T + 1) ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    linarith
  have hw0 : ∀ x, 0 ≤ wT T x := by
    intro x
    unfold wT
    have : 0 ≤ min (x ^ 2) ((T + 1) ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    positivity
  have key := htr (fun y => (θ (δ * psi A L s y) : ℂ) *
      GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y - GlobalTheory.OTY.TwEst.ext0 U F0 y)
    (fun y => wT T (δ * psi A L s y) * Real.exp (-psi A L s y))
    (((Complex.measurable_ofReal.comp (hθ.measurable.comp hm)).mul hqm).sub hF0)
    ((hwc.measurable.comp hm).mul (Real.measurable_exp.comp hpsi.neg))
    (fun y _ => mul_nonneg (hw0 _) (Real.exp_pos _).le)
  refine Eq.trans ?_ (key.trans ?_)
  · refine setLIntegral_congr_fun hU.measurableSet fun y hy => ?_
    have h1 : GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y
        = GlobalTheory.OTY.TwEst.quot A h β y :=
      GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) ⟨y, hy⟩
    have h2 : (θ (δ * psi A L s y) : ℂ) * h (A.pick y) y
        - β (A.pick y) y * GlobalTheory.OTY.TwEst.ext0 U F0 y
        = β (A.pick y) y * ((θ (δ * psi A L s y) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β y
          - GlobalTheory.OTY.TwEst.ext0 U F0 y) := by
      rw [hq y hy]; ring
    simp only [h1]
    congr 1
    unfold WeightedAtlas.nsq
    simp only [h2, norm_mul, mul_pow]
    ring
  · refine lintegral_congr fun x => ?_
    simp only [GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe]
    congr 2
    rw [neg_add, Real.exp_add]
    ring
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedEstimate_lhs_transfer : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ (δ T : ℝ) (θ : ℝ → ℝ) (F0 : U → ℂ), Continuous θ → Measurable (GlobalTheory.OTY.TwEst.ext0 U F0) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - β i x * GlobalTheory.OTY.TwEst.ext0 U F0 x) y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖(θ (δ * psi A L s x) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β x - F0 x‖ ^ 2 * (wT T (δ * psi A L s x) * Real.exp (-(GlobalTheory.OTY.TwEst.wt A E β z x + psi A L s x)))) ∂vol n (fun y : U => z y) := by
  atlas_forward_decl GlobalTheory.OTY.TwEst.lhs_transfer
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.twisted_estimate_nz : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → (∀ y, A.sqn L s y ≤ 1) → ∀ δ : ℝ, 0 < δ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n) (β : ι → Y → ℂ), (A.IsSec Λ τ ∧ A.Pos Λ (fun _ => 0) ∧ Etale A (nz A τ) z ∧ A.IsFrameOn (A.kap + E) (nz A τ) β ∧ Dense (nz A τ) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y) → ∀ (Ω : Set Y) (h : ι → Y → ℂ) (T : ℝ) (θ : ℝ → ℝ), (IsOpen Ω ∧ A.IsSecOn (A.kap + E) Ω h ∧ (∀ i y, y ∉ Ω → h i y = 0)) → 300 ≤ T → IsCut T θ → (∀ y, y ∉ A.zeroSet s → δ * psi A L s y ≤ -T + 1 → y ∈ Ω) → ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu < ⊤ → ∃ F : ι → Y → ℂ, A.IsSecOn (A.kap + E) (nz A τ) F ∧ ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu ≤ 30 * ∫⁻ y in {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu := by
  intro n Y _ _ _ _ _ _ ι La _ A E L s hs hsq δ hδ hlev Λ τ z β hdat Ω h T θ hhd hT hθ hΩcov hfin
  obtain ⟨hτ, hpos, hz, hβ, _hdense, C, hC0, hC⟩ := hdat
  obtain ⟨hΩ, hh, hh0⟩ := hhd
  obtain ⟨X, hXz, hXe⟩ := GlobalTheory.T.nonvanishingSet_etale_stein n Y ι La A Λ τ z hτ hpos hz
  have hU : IsOpen (nz A τ) := hz.isOpen
  have hpt := GlobalTheory.OTY.TwEst.nz_facts A L Λ s τ C hC0 hsq hC
  obtain ⟨hsmφ, hsmψ, hlevi⟩ := GlobalTheory.T.frameWeight_singularWeight_smooth_leviNonneg n Y ι La A E L s hs δ hlev (nz A τ) z β hz hβ
    (fun y hy => (hpt y hy).1)
  obtain ⟨hqd, hqm, hq⟩ := GlobalTheory.T.sectionQuotient_holomorphic_measurable n Y ι La A (A.kap + E) (nz A τ) Ω β h hU hΩ hβ hh hh0
  have hψm : Measurable (psi A L s) :=
    (GlobalTheory.T.measurable_nsq_and_psi_of_isSecOn n Y ι La A (A.kap + E) Ω h hΩ hh hh0).2 L s hs
  have htr := GlobalTheory.T.lintegral_weightedAtlas_frame_etale_transfer n Y ι La A E (nz A τ) z β hz hβ
  have hGholo : ∀ e : OpenPartialHomeomorph (nz A τ) (V n), IsChart n X.z e →
      DifferentiableOn ℂ ((fun y : nz A τ => GlobalTheory.OTY.TwEst.quot A h β y) ∘ e.symm)
        (e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω)) := by
    rw [hXz]
    exact (GlobalTheory.T.etale_holomorphic_iff_chart_holomorphic n Y ι La A (nz A τ) z hz Ω (GlobalTheory.OTY.TwEst.quot A h β) hΩ).2 hqd
  have hGm : Measurable (fun y : nz A τ => GlobalTheory.OTY.TwEst.quot A h β y) := by
    have h1 := hqm.comp (measurable_subtype_coe : Measurable (Subtype.val : nz A τ → Y))
    convert h1 using 1
    funext y
    simp only [Function.comp, GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe]
  have hθc : Continuous θ := hθ.1.continuous
  have hθb : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1 := hθ.2.2.2.1
  have hwint := GlobalTheory.T.weighted_l2_estimate_twisted_sections n Y ι La A E L s (nz A τ) z β h hU htr hq hqm hψm δ θ hθc hθb
  obtain ⟨F0, hF0, hest⟩ := GlobalTheory.T.twisted_extension_etaleStein_logGrowthWeight n (nz A τ) X
    (fun y => GlobalTheory.OTY.TwEst.wt A E β z y) (fun y => psi A L s y)
    (fun y => GlobalTheory.OTY.TwEst.quot A h β y) (Subtype.val ⁻¹' Ω) δ T θ
    (by rw [hXz]; exact hsmφ) (by rw [hXz]; exact hsmψ) (fun x => (hpt x x.2).2.1) hδ hT hθ
    (by rw [hXz]; exact hlevi) (hΩ.preimage continuous_subtype_val) hGm hGholo
    (fun x hx => hΩcov x (hpt x x.2).1 hx)
    ⟨n, n * Real.log C, fun x => by rw [hXe]; exact (hpt x x.2).2.2⟩
    (by rw [hXz]; exact lt_of_le_of_lt hwint hfin)
  rw [hXz] at hF0 hest
  obtain ⟨hFsec, hFm⟩ := GlobalTheory.T.isSection_holomorphic_mul_frame_extendByZero n Y ι La A (A.kap + E) (nz A τ) z β F0 hz hβ hF0
  refine ⟨fun i y => β i y * GlobalTheory.OTY.TwEst.ext0 (nz A τ) F0 y, hFsec, ?_⟩
  exact (GlobalTheory.T.twistedEstimate_lhs_transfer n Y ι La A E L s (nz A τ) z β h hU htr hq hqm hψm δ T θ F0 hθc hFm).trans_le
    (hest.trans (mul_le_mul_of_nonneg_left
      (GlobalTheory.T.twistedEstimate_rhs_le_manifold n Y ι La A E L s (nz A τ) z β h hU htr hq hqm hψm δ T) (by norm_num)))
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedEstimate_etalePart_manifold : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → (∀ y, A.sqn L s y ≤ 1) → ∀ δ : ℝ, 0 < δ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n) (β : ι → Y → ℂ), (A.IsSec Λ τ ∧ A.Pos Λ (fun _ => 0) ∧ Etale A (nz A τ) z ∧ A.IsFrameOn (A.kap + E) (nz A τ) β ∧ Dense (nz A τ) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y) → ∀ (Ω : Set Y) (h : ι → Y → ℂ) (T : ℝ) (θ : ℝ → ℝ), (IsOpen Ω ∧ A.IsSecOn (A.kap + E) Ω h ∧ (∀ i y, y ∉ Ω → h i y = 0)) → 300 ≤ T → IsCut T θ → (∀ y, y ∉ A.zeroSet s → δ * psi A L s y ≤ -T + 1 → y ∈ Ω) → ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu < ⊤ → ∃ F : ι → Y → ℂ, A.IsSecOn (A.kap + E) (nz A τ) F ∧ ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu ≤ 30 * ∫⁻ y in {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu := by
  atlas_forward_decl GlobalTheory.OTY.TwEst.twisted_estimate_nz
end
