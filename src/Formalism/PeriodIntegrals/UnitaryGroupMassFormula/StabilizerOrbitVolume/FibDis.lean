import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibFour
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensGen

section
noncomputable section

namespace PI.VolStabSW.Glue

open MeasureTheory Topology Set Filter PI.VolStabSW
open scoped CompactlySupported

section Ext

variable {V : Type} [TopologicalSpace V] [T2Space V]

open Classical in

def extZ (U : Set V) (φ : U → ℝ) : V → ℝ := fun v => if h : v ∈ U then φ ⟨v, h⟩ else 0

theorem extZ_val (U : Set V) (φ : U → ℝ) (u : U) : extZ U φ u = φ u := by
  simp only [extZ, dif_pos u.2]

private theorem tsupport_extZ_subset_image (U : Set V) (φ : U → ℝ) (hs : HasCompactSupport φ) :
    tsupport (extZ U φ) ⊆ Subtype.val '' tsupport φ := by
  have hK : IsCompact (Subtype.val '' tsupport φ) := hs.isCompact.image continuous_subtype_val
  refine closure_minimal ?_ hK.isClosed
  intro v hv
  rw [Function.mem_support] at hv
  by_cases h : v ∈ U
  · refine ⟨⟨v, h⟩, subset_tsupport _ ?_, rfl⟩
    rw [Function.mem_support]
    simpa only [extZ, dif_pos h] using hv
  · exact (hv (by simp only [extZ, dif_neg h])).elim

theorem extZ_props {U : Set V} (hU : IsOpen U) (φ : U → ℝ) (hc : Continuous φ)
    (hs : HasCompactSupport φ) : IsCcOn U (extZ U φ) := by
  have hK : IsCompact (Subtype.val '' tsupport φ) := hs.isCompact.image continuous_subtype_val
  have hsub := tsupport_extZ_subset_image U φ hs
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) hsub, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro v
    by_cases h : v ∈ U
    · have hcomp : extZ U φ ∘ Subtype.val = φ := funext (extZ_val U φ)
      have hat : ContinuousAt (extZ U φ ∘ Subtype.val) (⟨v, h⟩ : U) := by
        rw [hcomp]; exact hc.continuousAt
      exact hU.isOpenEmbedding_subtypeVal.continuousAt_iff.1 hat
    · have hv : v ∉ Subtype.val '' tsupport φ := by
        rintro ⟨u, _, hu⟩
        exact h (hu ▸ u.2)
      have hev : extZ U φ =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hv] with w hw
        by_contra hne
        exact hw (hsub (subset_tsupport _ hne))
      exact continuousAt_const.congr hev.symm
  · refine hsub.trans ?_
    rintro _ ⟨u, _, rfl⟩
    exact u.2

theorem extZ_add (U : Set V) (φ ψ : U → ℝ) : extZ U (φ + ψ) = extZ U φ + extZ U ψ := by
  funext v
  by_cases h : v ∈ U
  · simp only [extZ, dif_pos h, Pi.add_apply]
  · simp only [extZ, dif_neg h, Pi.add_apply, add_zero]

theorem extZ_smul (U : Set V) (c : ℝ) (φ : U → ℝ) : extZ U (c • φ) = c • extZ U φ := by
  funext v
  by_cases h : v ∈ U
  · simp only [extZ, dif_pos h, Pi.smul_apply]
  · simp only [extZ, dif_neg h, Pi.smul_apply, smul_zero]

theorem extZ_nonneg (U : Set V) (φ : U → ℝ) (h : 0 ≤ φ) : 0 ≤ extZ U φ := by
  intro v
  by_cases hv : v ∈ U
  · simp only [extZ, dif_pos hv, Pi.zero_apply]
    exact h ⟨v, hv⟩
  · simp only [extZ, dif_neg hv, Pi.zero_apply, le_refl]

end Ext

section Dens

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X] {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V}

open Classical in

def G (hD : DensAll μ f ι ν U) (φ : V → ℝ) : X → ℝ :=
  if h : IsCcOn U φ then Classical.choose (hD φ h.1 h.2.1 h.2.2) else 0

theorem G_spec (hD : DensAll μ f ι ν U) {φ : V → ℝ} (h : IsCcOn U φ) :
    Continuous (G hD φ) ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, G hD φ b ∂ν := by
  have hc := Classical.choose_spec (hD φ h.1 h.2.1 h.2.2)
  simp only [G, dif_pos h]
  exact hc

variable [OpensMeasurableSpace X] [T2Space X] [LocallyCompactSpace X]
  [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]

private theorem nonneg_of_setIntegral_compact_nonneg {g : X → ℝ} (hg : Continuous g)
    (h : ∀ S, IsCompact S → 0 ≤ ∫ b in S, g b ∂ν) (b0 : X) : 0 ≤ g b0 := by
  by_contra hlt
  push_neg at hlt
  have hcneg : g b0 / 2 < 0 := by linarith
  have hW : {b | g b < g b0 / 2} ∈ 𝓝 b0 :=
    (isOpen_lt hg continuous_const).mem_nhds (show g b0 < g b0 / 2 by linarith)
  obtain ⟨K, hKn, hKW, hK⟩ := local_compact_nhds hW
  have hpos : 0 < ν K := ν.measure_pos_of_mem_nhds hKn
  have hfin : ν K < ⊤ := hK.measure_lt_top
  have hmeas : MeasurableSet K := hK.isClosed.measurableSet
  have h1 : ∫ b in K, g b ∂ν ≤ ∫ b in K, g b0 / 2 ∂ν :=
    setIntegral_mono_on (hg.continuousOn.integrableOn_compact hK)
      (continuous_const.continuousOn.integrableOn_compact hK) hmeas (fun b hb => le_of_lt (hKW hb))
  have h2 : ∫ b in K, g b0 / 2 ∂ν < 0 := by
    rw [setIntegral_const, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (ENNReal.toReal_pos hpos.ne' hfin.ne) hcneg
  linarith [h K hK]

theorem dens_unique {g1 g2 : X → ℝ} (h1 : Continuous g1) (h2 : Continuous g2)
    (h : ∀ S, IsCompact S → ∫ b in S, g1 b ∂ν = ∫ b in S, g2 b ∂ν) : g1 = g2 := by
  funext b
  have ha : 0 ≤ g1 b - g2 b := by
    refine nonneg_of_setIntegral_compact_nonneg (ν := ν) (g := fun x => g1 x - g2 x) (h1.sub h2) (fun S hS => ?_) b
    rw [integral_sub (h1.continuousOn.integrableOn_compact hS) (h2.continuousOn.integrableOn_compact hS), h S hS, sub_self]
  have hb : 0 ≤ g2 b - g1 b := by
    refine nonneg_of_setIntegral_compact_nonneg (ν := ν) (g := fun x => g2 x - g1 x) (h2.sub h1) (fun S hS => ?_) b
    rw [integral_sub (h2.continuousOn.integrableOn_compact hS) (h1.continuousOn.integrableOn_compact hS), h S hS, sub_self]
  linarith

theorem dens_nonneg {g : X → ℝ} (hg : Continuous g)
    (h : ∀ S, IsCompact S → 0 ≤ ∫ b in S, g b ∂ν) (b0 : X) : 0 ≤ g b0 := by
  exact nonneg_of_setIntegral_compact_nonneg hg h b0

variable [IsFiniteMeasureOnCompacts μ] [OpensMeasurableSpace V]

theorem isCc_add {φ ψ : V → ℝ} (hφ : IsCcOn U φ) (hψ : IsCcOn U ψ) : IsCcOn U (φ + ψ) := by
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, ?_⟩
  refine (closure_minimal ?_ ((isClosed_tsupport φ).union (isClosed_tsupport ψ))).trans
    (union_subset hφ.2.2 hψ.2.2)
  intro x hx
  by_contra hn
  simp only [mem_union, not_or] at hn
  apply hx
  simp only [Pi.add_apply, image_eq_zero_of_notMem_tsupport hn.1,
    image_eq_zero_of_notMem_tsupport hn.2, add_zero]

theorem isCc_smul (c : ℝ) {φ : V → ℝ} (hφ : IsCcOn U φ) : IsCcOn U (c • φ) := by
  have hs : Function.support (c • φ) ⊆ Function.support φ := by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    simp only [Pi.smul_apply, h0, smul_zero]
  exact ⟨hφ.1.const_smul c, hφ.2.1.mono hs, (closure_mono hs).trans hφ.2.2⟩

theorem G_add (hD : DensAll μ f ι ν U) {φ ψ : V → ℝ} (hφ : IsCcOn U φ) (hψ : IsCcOn U ψ) :
    G hD (φ + ψ) = G hD φ + G hD ψ := by
  have hs := G_spec hD (isCc_add hφ hψ)
  have h1 := G_spec hD hφ
  have h2 := G_spec hD hψ
  refine dens_unique (ν := ν) hs.1 (h1.1.add h2.1) (fun S hS => ?_)
  rw [← hs.2 S hS]
  simp only [Pi.add_apply]
  rw [integral_add (hφ.1.integrable_of_hasCompactSupport hφ.2.1).integrableOn
      (hψ.1.integrable_of_hasCompactSupport hψ.2.1).integrableOn,
    integral_add (h1.1.continuousOn.integrableOn_compact hS) (h2.1.continuousOn.integrableOn_compact hS),
    h1.2 S hS, h2.2 S hS]

theorem G_smul (hD : DensAll μ f ι ν U) (c : ℝ) {φ : V → ℝ} (hφ : IsCcOn U φ) :
    G hD (c • φ) = c • G hD φ := by
  have hs := G_spec hD (isCc_smul c hφ)
  have h1 := G_spec hD hφ
  refine dens_unique (ν := ν) hs.1 (h1.1.const_smul c) (fun S hS => ?_)
  rw [← hs.2 S hS]
  simp only [Pi.smul_apply]
  rw [integral_smul, integral_smul, h1.2 S hS]

theorem G_nonneg (hD : DensAll μ f ι ν U) {φ : V → ℝ} (hφ : IsCcOn U φ) (h0 : 0 ≤ φ) :
    0 ≤ G hD φ := by
  intro b
  have hs := G_spec hD hφ
  refine dens_nonneg (ν := ν) hs.1 (fun S hS => ?_) b
  rw [← hs.2 S hS]
  exact integral_nonneg (fun v => h0 v)

end Dens

section Riesz

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [LocallyCompactSpace V] [T2Space V] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [TopologicalSpace Y] [T2Space Y]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V}
  [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]

theorem tsupport_extZ (U : Set V) (φ : U → ℝ) (hs : HasCompactSupport φ) :
    tsupport (extZ U φ) ⊆ Subtype.val '' tsupport φ := by
  exact tsupport_extZ_subset_image U φ hs

def lam (hD : DensAll μ f ι ν U) (hU : IsOpen U) (b : X) : C_c(U, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun ψ => G hD (extZ U ψ) b
      map_add' := fun ψ1 ψ2 => by
        simp only [CompactlySupportedContinuousMap.coe_add, extZ_add]
        rw [G_add hD (extZ_props hU ψ1 ψ1.continuous ψ1.hasCompactSupport)
          (extZ_props hU ψ2 ψ2.continuous ψ2.hasCompactSupport)]
        rfl
      map_smul' := fun c ψ => by
        simp only [CompactlySupportedContinuousMap.coe_smul, extZ_smul, RingHom.id_apply]
        rw [G_smul hD c (extZ_props hU ψ ψ.continuous ψ.hasCompactSupport)]
        rfl }
    (fun ψ hψ => G_nonneg hD (extZ_props hU ψ ψ.continuous ψ.hasCompactSupport)
      (extZ_nonneg U ψ fun u => (CompactlySupportedContinuousMap.le_def.1 hψ) u) b)

theorem lam_apply (hD : DensAll μ f ι ν U) (hU : IsOpen U) (b : X) (ψ : C_c(U, ℝ)) :
    lam hD hU b ψ = G hD (extZ U ψ) b := rfl

variable [OpensMeasurableSpace V]

def fibG (hD : DensAll μ f ι ν U) (hU : IsOpen U) (b : X) : Measure V :=
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  (RealRMK.rieszMeasure (lam hD hU b)).map Subtype.val

def restr (hU : IsOpen U) (φ : V → ℝ) (h : IsCcOn U φ) : C_c(U, ℝ) where
  toFun := fun u => φ u
  continuous_toFun := h.1.comp continuous_subtype_val
  hasCompactSupport' := by
    have hsub : tsupport φ ⊆ Set.range (Subtype.val : U → V) := by
      rw [Subtype.range_coe]; exact h.2.2
    have hK : IsCompact ((Subtype.val : U → V) ⁻¹' tsupport φ) :=
      (Topology.IsInducing.subtypeVal.isCompact_preimage_iff hsub).2 h.2.1
    exact HasCompactSupport.intro' hK ((isClosed_tsupport φ).preimage continuous_subtype_val)
      fun u hu => image_eq_zero_of_notMem_tsupport hu

theorem extZ_restr (hU : IsOpen U) (φ : V → ℝ) (h : IsCcOn U φ) :
    extZ U (restr hU φ h) = φ := by
  funext v
  by_cases hv : v ∈ U
  · simp only [extZ, dif_pos hv]
    rfl
  · simp only [extZ, dif_neg hv]
    exact (image_eq_zero_of_notMem_tsupport fun ht => hv (h.2.2 ht)).symm

theorem fibG_integral (hD : DensAll μ f ι ν U) (hU : IsOpen U) (b : X) (φ : V → ℝ)
    (h : IsCcOn U φ) :
    Integrable φ (fibG hD hU b) ∧ ∫ v, φ v ∂(fibG hD hU b) = G hD φ b := by
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hme : MeasurableEmbedding (Subtype.val : U → V) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  unfold fibG
  refine ⟨?_, ?_⟩
  · rw [hme.integrable_map_iff]
    exact (restr hU φ h).continuous.integrable_of_hasCompactSupport
      (restr hU φ h).hasCompactSupport
  · rw [hme.integral_map]
    have hR := RealRMK.integral_rieszMeasure (lam hD hU b) (restr hU φ h)
    rw [lam_apply, extZ_restr] at hR
    exact hR

private theorem nonpos_of_setIntegral_compact_nonpos {g : X → ℝ} (hg : Continuous g) {b : X} {N : Set X} (hN : N ∈ 𝓝 b)
    (h : ∀ S, IsCompact S → S ⊆ N → ∫ x in S, g x ∂ν ≤ 0) : g b ≤ 0 := by
  refine not_lt.mp fun hpos => ?_
  have hW : N ∩ {x | g b / 2 < g x} ∈ 𝓝 b :=
    inter_mem hN ((isOpen_lt continuous_const hg).mem_nhds (show g b / 2 < g b by linarith))
  obtain ⟨K, hKn, hKW, hK⟩ := local_compact_nhds hW
  have hlow : ∫ x in K, g b / 2 ∂ν ≤ ∫ x in K, g x ∂ν :=
    setIntegral_mono_on (continuous_const.continuousOn.integrableOn_compact hK)
      (hg.continuousOn.integrableOn_compact hK) hK.isClosed.measurableSet
      (fun x hx => (hKW hx).2.le)
  have hconst : 0 < ∫ x in K, g b / 2 ∂ν := by
    rw [setIntegral_const, smul_eq_mul]
    exact mul_pos (ENNReal.toReal_pos (ν.measure_pos_of_mem_nhds hKn).ne' hK.measure_lt_top.ne)
      (half_pos hpos)
  linarith [h K hK (fun x hx => (hKW hx).1)]

theorem fibG_supp (hD : DensAll μ f ι ν U) (hU : IsOpen U) (hf : Continuous f)
    (hι : Continuous ι) (b : X) : fibG hD hU b (f ⁻¹' {ι b} ∩ U)ᶜ = 0 := by
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hW : IsOpen {u : U | f u ≠ ι b} :=
    isOpen_ne_fun (hf.comp continuous_subtype_val) continuous_const
  have hpre : (Subtype.val : U → V) ⁻¹' (f ⁻¹' {ι b} ∩ U)ᶜ = {u : U | f u ≠ ι b} := by
    ext u
    simp
  have hmeas : MeasurableSet (f ⁻¹' {ι b} ∩ U)ᶜ :=
    ((isClosed_singleton.preimage hf).measurableSet.inter hU.measurableSet).compl
  have hzero : ∀ K : Set U, K ⊆ {u : U | f u ≠ ι b} → IsCompact K →
      RealRMK.rieszMeasure (lam hD hU b) K = 0 := by
    intro K hKW hK
    obtain ⟨g, hg1, hgc, hgW, hg01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hW hKW
    let ψ : C_c(U, ℝ) := ⟨g, hgc⟩
    have hcc := extZ_props hU ψ ψ.continuous ψ.hasCompactSupport
    obtain ⟨hGc, hGi⟩ := G_spec hD hcc
    have hK' : IsCompact (Subtype.val '' tsupport ψ) :=
      ψ.hasCompactSupport.isCompact.image continuous_subtype_val
    have hbK : ι b ∉ f '' (Subtype.val '' tsupport ψ) := by
      rintro ⟨v, ⟨u, hu, rfl⟩, hv⟩
      exact hgW hu hv
    have hN : ι ⁻¹' (f '' (Subtype.val '' tsupport ψ))ᶜ ∈ 𝓝 b :=
      ((hK'.image hf).isClosed.isOpen_compl.preimage hι).mem_nhds hbK
    have hSz : ∀ S, IsCompact S → S ⊆ ι ⁻¹' (f '' (Subtype.val '' tsupport ψ))ᶜ →
        ∫ x in S, G hD (extZ U ψ) x ∂ν = 0 := by
      intro S hS hSN
      rw [← hGi S hS]
      apply setIntegral_eq_zero_of_forall_eq_zero
      rintro v ⟨s, hs, hsv⟩
      apply image_eq_zero_of_notMem_tsupport
      intro hvt
      exact hSN hs ⟨v, tsupport_extZ U ψ ψ.hasCompactSupport hvt, hsv.symm⟩
    have hup := nonpos_of_setIntegral_compact_nonpos (ν := ν) hGc hN fun S hS hSN => (hSz S hS hSN).le
    have hdown := nonpos_of_setIntegral_compact_nonpos (ν := ν) hGc.neg hN fun S hS hSN => by
      simp only [Pi.neg_apply]
      rw [integral_neg, hSz S hS hSN, neg_zero]
    have hΛ : lam hD hU b ψ = 0 := by
      rw [lam_apply]
      exact le_antisymm hup (neg_nonpos.mp hdown)
    have hle := RealRMK.rieszMeasure_le_of_eq_one (lam hD hU b) (f := ψ) (fun x => (hg01 x).1) hK
      (fun x hx => hg1 hx)
    rw [hΛ, ENNReal.ofReal_zero] at hle
    exact le_antisymm hle bot_le
  unfold fibG
  rw [Measure.map_apply continuous_subtype_val.measurable hmeas, hpre,
    hW.measure_eq_iSup_isCompact]
  simp only [ENNReal.iSup_eq_zero]
  exact hzero

end Riesz

def DisintStep : Prop :=
  ∀ (V X Y : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [LocallyCompactSpace V]
    [T2Space V] [SecondCountableTopology V] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] [T2Space Y] (μ : Measure V) (ν : Measure X),
    IsFiniteMeasureOnCompacts μ → IsFiniteMeasureOnCompacts ν → ν.IsOpenPosMeasure →
    ∀ (f : V → Y) (ι : X → Y) (U : Set V), Continuous f → IsClosedEmbedding ι →
      (∀ v, f v ∈ Set.range ι) → IsOpen U → ∀ fib : X → Measure V,
      (∀ b, fib b (f ⁻¹' {ι b} ∩ U)ᶜ = 0) →
      (∀ b K, IsCompact K → K ⊆ U → fib b K < ⊤) →
      (∀ φ : V → ℝ, IsCcOn U φ → (∀ b, Integrable φ (fib b)) ∧
        Continuous (fun b => ∫ v, φ v ∂(fib b)) ∧
        ∀ S : Set X, IsCompact S → ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, ∫ v, φ v ∂(fib b) ∂ν) →
      ∀ φ : V → ENNReal, Measurable φ → ∫⁻ v in U, φ v ∂μ = ∫⁻ b, ∫⁻ v, φ v ∂(fib b) ∂ν

theorem fibOfDens_of (hDis : DisintStep) : FibOfDens := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν hμ hν hνp f ι U hf hι hr hU hD
  haveI := hμ
  haveI := hν
  haveI := hνp
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hfin : ∀ b K, IsCompact K → K ⊆ U → fibG hD hU b K < ⊤ := by
    intro b K hK hKU
    unfold fibG
    rw [Measure.map_apply measurable_subtype_coe hK.isClosed.measurableSet]
    have hsub : K ⊆ Set.range (Subtype.val : U → V) := by
      rw [Subtype.range_coe]
      exact hKU
    exact ((Topology.IsInducing.subtypeVal.isCompact_preimage_iff hsub).2 hK).measure_lt_top
  have hint : ∀ φ : V → ℝ, IsCcOn U φ → (∀ b, Integrable φ (fibG hD hU b)) ∧
      Continuous (fun b => ∫ v, φ v ∂(fibG hD hU b)) ∧
      ∀ S : Set X, IsCompact S →
        ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, ∫ v, φ v ∂(fibG hD hU b) ∂ν := by
    intro φ hφ
    have hG := G_spec hD hφ
    have heq : (fun b => ∫ v, φ v ∂(fibG hD hU b)) = G hD φ :=
      funext fun b => (fibG_integral hD hU b φ hφ).2
    refine ⟨fun b => (fibG_integral hD hU b φ hφ).1, ?_, ?_⟩
    · rw [heq]
      exact hG.1
    · intro S hS
      rw [heq]
      exact hG.2 S hS
  have hsupp := fibG_supp hD hU hf hι.continuous
  have hstep := hDis V X Y μ ν hμ hν hνp f ι U hf hι hr hU (fibG hD hU) hsupp hfin hint
  refine ⟨fibG hD hU, hsupp, hstep, fun φ hc hs hsub => ?_⟩
  have h3 := hint φ ⟨hc, hs, hsub⟩
  exact ⟨fun b _ => h3.1 b, h3.2.1.continuousOn⟩

end PI.VolStabSW.Glue
end
end

section
noncomputable section

namespace PI.VolStabSW.DiscreteGroups

open MeasureTheory Topology Set Filter PI.VolStabSW PI.VolStabSW.Glue
open scoped ENNReal

section

variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V]

theorem cover (U : Set V) (hU : IsOpen U) : ∃ W : ℕ → Set V,
    (∀ n, IsOpen (W n) ∧ IsCompact (closure (W n)) ∧ closure (W n) ⊆ U) ∧ ⋃ n, W n = U := by
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let E := CompactExhaustion.choice U
  have h : ∀ n, ∃ W, IsOpen W ∧ Subtype.val '' E n ⊆ W ∧ closure W ⊆ U ∧ IsCompact (closure W) :=
    fun n => exists_open_between_and_isCompact_closure ((E.isCompact n).image continuous_subtype_val)
      hU (by rintro _ ⟨u, -, rfl⟩; exact u.2)
  choose W hW1 hW2 hW3 hW4 using h
  refine ⟨W, fun n => ⟨hW1 n, hW4 n, hW3 n⟩,
    subset_antisymm (iUnion_subset fun n => subset_closure.trans (hW3 n)) ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := E.exists_mem ⟨x, hx⟩
  exact mem_iUnion.2 ⟨n, hW2 n ⟨_, hn, rfl⟩⟩

theorem approx (O : Set V) (hO : IsOpen O) : ∃ φ : ℕ → V → ℝ,
    (∀ k, Continuous (φ k) ∧ HasCompactSupport (φ k) ∧ tsupport (φ k) ⊆ O) ∧
    (∀ k x, 0 ≤ φ k x ∧ φ k x ≤ 1) ∧ (∀ x, Monotone fun k => φ k x) ∧
    ∀ x, ⨆ k, ENNReal.ofReal (φ k x) = O.indicator 1 x := by
  haveI : LocallyCompactSpace O := hO.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let E := CompactExhaustion.choice O
  have h : ∀ k, ∃ g : C(V, ℝ), EqOn g 1 (Subtype.val '' E k) ∧ IsCompact (tsupport g) ∧
      tsupport g ⊆ Subtype.val '' interior (E (k + 1)) ∧ ∀ x, g x ∈ Icc (0 : ℝ) 1 := fun k =>
    exists_continuousMap_one_of_isCompact_subset_isOpen ((E.isCompact k).image continuous_subtype_val)
      (hO.isOpenMap_subtype_val _ isOpen_interior) (image_mono (E.subset_interior_succ k))
  choose g hg1 hgc hgs hg01 using h
  have hsubO : ∀ k, tsupport (g k) ⊆ O :=
    fun k => (hgs k).trans (by rintro _ ⟨u, -, rfl⟩; exact u.2)
  have hmono : ∀ x, Monotone fun k => g k x := by
    intro x
    refine monotone_nat_of_le_succ fun k => ?_
    by_cases hx : x ∈ tsupport (g k)
    · obtain ⟨u, hu, rfl⟩ := hgs k hx
      rw [hg1 (k + 1) ⟨u, interior_subset hu, rfl⟩]
      exact (hg01 k _).2
    · rw [image_eq_zero_of_notMem_tsupport hx]
      exact (hg01 (k + 1) x).1
  refine ⟨fun k => g k, fun k => ⟨(g k).continuous, hgc k, hsubO k⟩, fun k x => hg01 k x, hmono,
    fun x => ?_⟩
  by_cases hx : x ∈ O
  · obtain ⟨n, hn⟩ := E.exists_mem ⟨x, hx⟩
    rw [indicator_of_mem hx]
    apply le_antisymm
    · refine iSup_le fun k => ?_
      have := ENNReal.ofReal_le_ofReal (hg01 k x).2
      simpa using this
    · refine le_iSup_of_le n ?_
      have h1 : g n x = 1 := hg1 n ⟨⟨x, hx⟩, hn, rfl⟩
      show (1 : V → ℝ≥0∞) x ≤ ENNReal.ofReal (g n x)
      rw [h1]
      simp
  · rw [indicator_of_notMem hx]
    simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hsubO _ h))]

variable {X Y : Type} [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}
  (hf : Continuous f) (hι : IsClosedEmbedding ι) (hr : ∀ v, f v ∈ Set.range ι) (hU : IsOpen U)
  (h0 : ∀ b, fib b (f ⁻¹' {ι b} ∩ U)ᶜ = 0) (h2 : ∀ b K, IsCompact K → K ⊆ U → fib b K < ⊤)
  (h3 : ∀ φ : V → ℝ, IsCcOn U φ → (∀ b, Integrable φ (fib b)) ∧
        Continuous (fun b => ∫ v, φ v ∂(fib b)) ∧
        ∀ S : Set X, IsCompact S → ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, ∫ v, φ v ∂(fib b) ∂ν)

include hf hι hr hU h0 h2 h3

theorem cc_case (ψ : V → ℝ) (hψ : IsCcOn U ψ) (h0ψ : ∀ v, 0 ≤ ψ v) :
    ∫⁻ v, ENNReal.ofReal (ψ v) ∂μ = ∫⁻ b, ∫⁻ v, ENNReal.ofReal (ψ v) ∂(fib b) ∂ν := by
  obtain ⟨hint, hcont, hS⟩ := h3 ψ hψ
  set S : Set X := ι ⁻¹' (f '' tsupport ψ) with hSdef
  have hSc : IsCompact S := hι.isCompact_preimage (hψ.2.1.image hf)
  have hsub : tsupport ψ ⊆ f ⁻¹' (ι '' S) := by
    intro v hv
    obtain ⟨s, hs⟩ := hr v
    exact ⟨s, ⟨v, hv, hs.symm⟩, hs⟩
  have hzero : ∀ b ∉ S, ∫ v, ψ v ∂(fib b) = 0 := by
    intro b hb
    apply integral_eq_zero_of_ae
    have hae : ∀ᵐ v ∂(fib b), v ∉ (f ⁻¹' {ι b} ∩ U)ᶜ := measure_eq_zero_iff_ae_notMem.1 (h0 b)
    filter_upwards [hae] with v hv
    simp only [mem_compl_iff, not_not] at hv
    exact (eq_or_ne (ψ v) 0).resolve_right fun hne => hb ⟨v, subset_tsupport _ hne, hv.1⟩
  have e1 : ∫ v in f ⁻¹' (ι '' S), ψ v ∂μ = ∫ v, ψ v ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv =>
      image_eq_zero_of_notMem_tsupport fun h => hv (hsub h)
  have e2 : ∫ b in S, (∫ v, ψ v ∂(fib b)) ∂ν = ∫ b, (∫ v, ψ v ∂(fib b)) ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun b hb => hzero b hb
  have hG : Integrable (fun b => ∫ v, ψ v ∂(fib b)) ν :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro' hSc hSc.isClosed hzero)
  have hi : Integrable ψ μ := hψ.1.integrable_of_hasCompactSupport hψ.2.1
  calc ∫⁻ v, ENNReal.ofReal (ψ v) ∂μ = ENNReal.ofReal (∫ v, ψ v ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ h0ψ)).symm
    _ = ENNReal.ofReal (∫ b, (∫ v, ψ v ∂(fib b)) ∂ν) := by rw [← e1, hS S hSc, e2]
    _ = ∫⁻ b, ENNReal.ofReal (∫ v, ψ v ∂(fib b)) ∂ν :=
        ofReal_integral_eq_lintegral_ofReal hG
          (ae_of_all _ fun b => integral_nonneg fun v => h0ψ v)
    _ = ∫⁻ b, ∫⁻ v, ENNReal.ofReal (ψ v) ∂(fib b) ∂ν :=
        lintegral_congr fun b => ofReal_integral_eq_lintegral_ofReal (hint b) (ae_of_all _ h0ψ)

theorem open_case (O : Set V) (hO : IsOpen O) (hOU : O ⊆ U) :
    Measurable (fun b => fib b O) ∧ μ O = ∫⁻ b, fib b O ∂ν := by
  obtain ⟨φ, hφ, h01, hmono, hlim⟩ := approx O hO
  have hcc : ∀ k, IsCcOn U (φ k) := fun k => ⟨(hφ k).1, (hφ k).2.1, (hφ k).2.2.trans hOU⟩
  have hmeas : ∀ k, Measurable fun v => ENNReal.ofReal (φ k v) :=
    fun k => ENNReal.measurable_ofReal.comp (hφ k).1.measurable
  have hmon : Monotone fun k v => ENNReal.ofReal (φ k v) :=
    fun i j hij v => ENNReal.ofReal_le_ofReal (hmono v hij)
  have hfibO : ∀ b, fib b O = ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) := by
    intro b
    rw [← lintegral_iSup hmeas hmon]
    simp_rw [hlim]
    rw [lintegral_indicator_one hO.measurableSet]
  have hk : ∀ k, Measurable fun b => ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) := by
    intro k
    have : (fun b => ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b)) =
        fun b => ENNReal.ofReal (∫ v, φ k v ∂(fib b)) :=
      funext fun b => (ofReal_integral_eq_lintegral_ofReal ((h3 _ (hcc k)).1 b)
        (ae_of_all _ fun v => (h01 k v).1)).symm
    rw [this]
    exact ENNReal.measurable_ofReal.comp (h3 _ (hcc k)).2.1.measurable
  have hmonb : Monotone fun k b => ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) :=
    fun i j hij b => lintegral_mono fun v => ENNReal.ofReal_le_ofReal (hmono v hij)
  refine ⟨?_, ?_⟩
  · simp_rw [hfibO]
    exact Measurable.iSup hk
  · calc μ O = ∫⁻ v, O.indicator 1 v ∂μ := (lintegral_indicator_one hO.measurableSet).symm
      _ = ∫⁻ v, ⨆ k, ENNReal.ofReal (φ k v) ∂μ := by simp_rw [hlim]
      _ = ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂μ := lintegral_iSup hmeas hmon
      _ = ⨆ k, ∫⁻ b, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) ∂ν := by
          congr 1; funext k
          exact cc_case hf hι hr hU h0 h2 h3 (φ k) (hcc k) fun v => (h01 k v).1
      _ = ∫⁻ b, ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) ∂ν := (lintegral_iSup hk hmonb).symm
      _ = ∫⁻ b, fib b O ∂ν := by simp_rw [hfibO]

theorem null_compl (b : X) : fib b Uᶜ = 0 :=
  measure_mono_null (compl_subset_compl.2 inter_subset_right) (h0 b)

theorem meas_fib : ∀ A, MeasurableSet A → Measurable fun b => fib b A := by
  obtain ⟨W, hW, hWU⟩ := cover U hU
  have hWsub : ∀ n, W n ⊆ U := fun n => subset_closure.trans (hW n).2.2
  have hfin : ∀ b n, fib b (W n) ≠ ⊤ := fun b n =>
    (lt_of_le_of_lt (measure_mono subset_closure) (h2 b _ (hW n).2.1 (hW n).2.2)).ne
  have hP : ∀ n, ∀ A, MeasurableSet A → Measurable fun b => fib b (A ∩ W n) := by
    intro n
    refine MeasurableSpace.induction_on_inter
      (C := fun A _ => Measurable fun b => fib b (A ∩ W n)) (s := {s : Set V | IsOpen s})
      BorelSpace.measurable_eq isPiSystem_isOpen ?_ ?_ ?_ ?_
    · simp only [empty_inter, measure_empty]; exact measurable_const
    · intro t ht
      exact (open_case hf hι hr hU h0 h2 h3 (t ∩ W n) ((ht : IsOpen t).inter (hW n).1)
        (inter_subset_right.trans (hWsub n))).1
    · intro t htm IH
      have e : ∀ b, fib b (tᶜ ∩ W n) = fib b (W n) - fib b (t ∩ W n) := by
        intro b
        rw [← measure_diff inter_subset_right (htm.inter (hW n).1.measurableSet).nullMeasurableSet
          ((measure_mono inter_subset_right).trans_lt (lt_top_iff_ne_top.2 (hfin b n))).ne]
        congr 1
        ext x
        simp only [mem_inter_iff, mem_compl_iff, mem_diff]
        tauto
      simp_rw [e]
      exact (open_case hf hι hr hU h0 h2 h3 (W n) (hW n).1 (hWsub n)).1.sub IH
    · intro g hd hgm IH
      have e : ∀ b, fib b ((⋃ i, g i) ∩ W n) = ∑' i, fib b (g i ∩ W n) := by
        intro b
        rw [iUnion_inter, measure_iUnion (fun i j hij => (hd hij).mono inter_subset_left
          inter_subset_left) (fun i => (hgm i).inter (hW n).1.measurableSet)]
      simp_rw [e]
      exact Measurable.ennreal_tsum IH
  intro A hA
  have hD : ∀ n, MeasurableSet (disjointed W n) :=
    MeasurableSet.disjointed fun n => (hW n).1.measurableSet
  have e : ∀ b, fib b A = ∑' n, fib b (A ∩ disjointed W n) := by
    intro b
    rw [← measure_inter_add_diff A hU.measurableSet,
      measure_mono_null (show A \ U ⊆ Uᶜ from fun x hx => hx.2) (null_compl hf hι hr hU h0 h2 h3 b),
      add_zero,
      ← hWU, ← iUnion_disjointed, inter_iUnion,
      measure_iUnion (fun i j hij => ((disjoint_disjointed W) hij).mono inter_subset_right
        inter_subset_right) (fun n => hA.inter (hD n))]
  simp_rw [e]
  refine Measurable.ennreal_tsum fun n => ?_
  have := hP n (A ∩ disjointed W n) (hA.inter (hD n))
  simpa only [inter_eq_left.2 (inter_subset_right.trans (disjointed_subset W n))] using this

end

theorem disintStep_holds : DisintStep := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν hμ hν hpos f ι U hf hι hr hU fib h0 h2 h3 φ hφ
  have hmf : Measurable fib :=
    Measure.measurable_of_measurable_coe fib (meas_fib hf hι hr hU h0 h2 h3)
  have hρ : μ.restrict U = ν.bind fib := by
    obtain ⟨B, hB, hBU⟩ := cover (univ : Set V) isOpen_univ
    refine Measure.ext_of_generateFrom_of_iUnion {s : Set V | IsOpen s} B BorelSpace.measurable_eq
      isPiSystem_isOpen hBU (fun i => (hB i).1) (fun i => ?_) ?_
    · exact ((Measure.restrict_apply_le _ _).trans_lt
        ((measure_mono subset_closure).trans_lt (hB i).2.1.measure_lt_top)).ne
    · intro s hs
      rw [Measure.restrict_apply (hs : IsOpen s).measurableSet,
        Measure.bind_apply hs.measurableSet hmf.aemeasurable,
        (open_case hf hι hr hU h0 h2 h3 (s ∩ U) (hs.inter hU) inter_subset_right).2]
      congr 1
      funext b
      rw [← measure_inter_add_diff s hU.measurableSet,
        measure_mono_null (show s \ U ⊆ Uᶜ from fun x hx => hx.2)
          (null_compl hf hι hr hU h0 h2 h3 b), add_zero]
  rw [hρ, Measure.lintegral_bind hmf.aemeasurable hφ.aemeasurable]

theorem fibOfDens_holds : FibOfDens := fibOfDens_of disintStep_holds

end PI.VolStabSW.DiscreteGroups
end
end
