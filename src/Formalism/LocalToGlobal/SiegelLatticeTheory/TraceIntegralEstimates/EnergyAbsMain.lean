import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsBasic
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsTrunc
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsFolnerExp
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsSchur

section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem sumsq_eq {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) {S : Set G}
    {μS ν : Measure G} (hS : IsHaarSub S μS) [SFinite ν] {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hWc : Continuous W) (hW1 : ∫⁻ x, ‖W x‖ₑ ∂ν < ⊤) {Ω : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S)
    (hfin : μS Ω < ⊤) :
    ((∑ i, ‖yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i)‖ ^ 2 : ℝ) : ℂ) =
      ∫ z, ∫ z', ∫ q, (cnt μS Ω q).toReal • Fk σ w W z z' q ∂μS ∂ν ∂ν := by
  have hS' := hS
  obtain ⟨-, -, hSmul, hSinv, hSig, -, -, -, -, -, -⟩ := hS'
  haveI : SigmaFinite μS := hSig
  haveI : IsFiniteMeasure (μS.restrict Ω) := isFiniteMeasure_restrict.mpr hfin.ne
  have hleft : ∀ (μ : Measure G) (f : G → PiLp 2 (fun _ : Fin (Module.finrank ℂ V) => HH)),
      Integrable f μ → ∀ c, ⟪∫ x, f x ∂μ, c⟫_ℂ = ∫ x, ⟪f x, c⟫_ℂ ∂μ := by
    intro μ f hf c
    rw [← inner_conj_symm, ← integral_inner hf, ← integral_conj]
    simp_rw [inner_conj_symm]
  set g := gvec σ w W with hg
  have hgc : Continuous g := gvec_continuous hσ w hWc
  have hWn : ∀ s ∈ S, ∀ x, ‖W (s * x)‖ = ‖W x‖ := by
    intro s hs x
    rw [hWeq s hs x]
    have h := hτu s hs (W x) (W x)
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖τ s (W x)‖ ^ 2 = ‖W x‖ ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h'
  have hgn : ∀ s ∈ Ω, ∀ z, ‖g (s⁻¹ * z)‖ = ‖W z‖ := by
    intro s hs z
    rw [hg, gvec_norm hσ hw]
    exact hWn s⁻¹ (hSinv s (hΩS hs)) z
  have hgint : ∀ z, Integrable (fun s => g (s⁻¹ * z)) (μS.restrict Ω) := by
    intro z
    refine Integrable.mono' (integrable_const ‖W z‖) ?_ ?_
    · exact (hgc.comp (continuous_inv.mul continuous_const)).aestronglyMeasurable
    · exact (ae_restrict_iff' hΩm).mpr (Filter.Eventually.of_forall fun s hs => (hgn s hs z).le)
  set F : G → PiLp 2 (fun _ : Fin (Module.finrank ℂ V) => HH) :=
    fun z => ∫ s in Ω, g (s⁻¹ * z) ∂μS with hF
  have hWi : Integrable W ν := ⟨hWc.aestronglyMeasurable, hW1⟩
  have hWint : Integrable (fun z => ‖W z‖) ν := hWi.norm
  have hFint : Integrable F ν := by
    refine Integrable.mono' (hWint.const_mul (μS.real Ω)) ?_ ?_
    · have hsm : StronglyMeasurable (Function.uncurry fun (z s : G) => g (s⁻¹ * z)) := by
        apply Continuous.stronglyMeasurable
        exact hgc.comp ((continuous_snd.inv).mul continuous_fst)
      exact (hsm.integral_prod_right (ν := μS.restrict Ω)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun z => ?_
      have h1 := norm_integral_le_of_norm_le_const (μ := μS.restrict Ω) (f := fun s => g (s⁻¹ * z))
        (C := ‖W z‖) ((ae_restrict_iff' hΩm).mpr (Filter.Eventually.of_forall fun s hs => (hgn s hs z).le))
      calc ‖F z‖ ≤ ‖W z‖ * (μS.restrict Ω).real Set.univ := h1
        _ = μS.real Ω * ‖W z‖ := by
          simp only [Measure.real, Measure.restrict_apply_univ]
          ring
  have hY : ∀ i, (∫ z, F z ∂ν).ofLp i = yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i) := by
    intro i
    have h1 := (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin (Module.finrank ℂ V) => HH) i).integral_comp_comm hFint
    simp only [PiLp.proj_apply] at h1
    rw [← h1]
    unfold yv
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have h2 := (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin (Module.finrank ℂ V) => HH) i).integral_comp_comm
      (hgint z)
    simp only [PiLp.proj_apply] at h2
    simp only [hF]
    rw [← h2]
    simp [hg, gvec]
  have hr : (∑ i, ‖yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i)‖ ^ 2) = ‖∫ z, F z ∂ν‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [hY]
  rw [hr]
  push_cast
  refine (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∫ z, F z ∂ν)).symm.trans ?_
  calc ⟪∫ z, F z ∂ν, ∫ z, F z ∂ν⟫_ℂ = ∫ z, ⟪F z, ∫ z', F z' ∂ν⟫_ℂ ∂ν := hleft ν F hFint _
    _ = ∫ z, ∫ z', ⟪F z, F z'⟫_ℂ ∂ν ∂ν := by
        congr 1
        funext z
        exact (integral_inner hFint _).symm
    _ = ∫ z, ∫ z', ∫ q, (cnt μS Ω q).toReal • Fk σ w W z z' q ∂μS ∂ν ∂ν := by
        congr 1
        funext z
        congr 1
        funext z'
        have hae : ∀ᵐ p ∂((μS.restrict Ω).prod (μS.restrict Ω)), p ∈ Ω ×ˢ Ω := by
          rw [Measure.prod_restrict]
          exact ae_restrict_mem (hΩm.prod hΩm)
        have hint : Integrable (fun p : G × G => Fk σ w W z z' (p.1 * p.2⁻¹))
            ((μS.restrict Ω).prod (μS.restrict Ω)) := by
          refine Integrable.mono' (integrable_const (‖W z‖ * ‖W z'‖)) ?_ ?_
          · exact (Fk_continuous hσ w hWc (a := fun _ => z) (b := fun _ => z')
              (c := fun p : G × G => p.1 * p.2⁻¹) continuous_const continuous_const
              (continuous_fst.mul continuous_snd.inv)).aestronglyMeasurable
          · exact hae.mono fun p hp =>
              Fk_bound hσ hw hWeq hτu z z' (hSmul _ (hΩS hp.1) _ (hSinv _ (hΩS hp.2)))
        calc ⟪F z, F z'⟫_ℂ = ∫ s in Ω, ⟪g (s⁻¹ * z), F z'⟫_ℂ ∂μS := hleft _ _ (hgint z) _
          _ = ∫ s in Ω, ∫ t in Ω, ⟪g (s⁻¹ * z), g (t⁻¹ * z')⟫_ℂ ∂μS ∂μS := by
              congr 1
              funext s
              exact (integral_inner (hgint z') _).symm
          _ = ∫ s in Ω, ∫ t in Ω, Fk σ w W z z' (s * t⁻¹) ∂μS ∂μS := by
              refine setIntegral_congr_fun hΩm fun s hs => ?_
              congr 1
              funext t
              rw [hg, gvec_inner]
              exact kF hσ w hSinv hWeq hτu z z' (hΩS hs)
          _ = _ := conv_integral hS hΩm hΩS hfin _
              (Fk_continuous hσ w hWc (a := fun _ => z) (b := fun _ => z') (c := fun q => q)
                continuous_const continuous_const continuous_id).stronglyMeasurable hint

end Formalism.L2.S.Pv.EnergyAbs
end
end

section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem Fk_enorm_le {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G}
    {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (z z' : G) {q : G} (hq : q ∈ S) :
    ‖Fk σ w W z z' q‖ₑ ≤ ‖⟪σ z w, σ q (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ := by
  unfold Fk
  rw [hWeq q hq z', hσ.2.1 q z', ContinuousLinearMap.mul_apply]
  have hn : ‖τ q (W z')‖ = ‖W z'‖ := by
    have h := hτu q hq (W z') (W z')
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖τ q (W z')‖ ^ 2 = ‖W z'‖ ^ 2 := by exact_mod_cast h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h'
  have hA : ‖⟪τ q (W z'), W z⟫_ℂ‖ ≤ ‖W z‖ * ‖W z'‖ :=
    (norm_inner_le_norm _ _).trans (by rw [hn, mul_comm])
  have hAe : ‖⟪τ q (W z'), W z⟫_ℂ‖ₑ ≤ ‖W z‖ₑ * ‖W z'‖ₑ := by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hA
  rw [enorm_mul]
  calc ‖⟪τ q (W z'), W z⟫_ℂ‖ₑ * ‖⟪σ z w, σ q (σ z' w)⟫_ℂ‖ₑ
      ≤ (‖W z‖ₑ * ‖W z'‖ₑ) * ‖⟪σ z w, σ q (σ z' w)⟫_ℂ‖ₑ := by gcongr
    _ = ‖⟪σ z w, σ q (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ := by ring

private theorem continuous_Fk_uncurry {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V}
    (hWc : Continuous W) : Continuous (fun x : G × G × G => Fk σ w W x.1 x.2.1 x.2.2) := by
  have hσc := hσ.2.2.2 w
  unfold Fk
  refine Continuous.mul ?_ ?_
  · exact (hWc.comp (continuous_snd.snd.mul continuous_snd.fst)).inner (hWc.comp continuous_fst)
  · exact (hσc.comp continuous_fst).inner (hσc.comp (continuous_snd.snd.mul continuous_snd.fst))

private theorem lintegral_enorm_Fk_lt_infty {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G}
    {μS ν : Measure G} [SFinite μS] [SFinite ν] (hS0 : μS Sᶜ = 0) {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hmeas : Measurable (fun x : G × G × G => ‖Fk σ w W x.1 x.2.1 x.2.2‖ₑ))
    (hconv : ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν < ⊤) :
    ∫⁻ x, ‖Fk σ w W x.1 x.2.1 x.2.2‖ₑ ∂(ν.prod (ν.prod μS)) < ⊤ := by
  have hSae : ∀ᵐ q ∂μS, q ∈ S := by
    have h := compl_mem_ae_iff.2 hS0
    rw [compl_compl] at h
    exact h
  calc ∫⁻ x, ‖Fk σ w W x.1 x.2.1 x.2.2‖ₑ ∂(ν.prod (ν.prod μS))
      = ∫⁻ z, ∫⁻ y, ‖Fk σ w W z y.1 y.2‖ₑ ∂(ν.prod μS) ∂ν := lintegral_prod _ hmeas.aemeasurable
    _ = ∫⁻ z, ∫⁻ z', ∫⁻ q, ‖Fk σ w W z z' q‖ₑ ∂μS ∂ν ∂ν :=
        lintegral_congr fun z => lintegral_prod _ (hmeas.comp measurable_prodMk_left).aemeasurable
    _ ≤ ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν :=
        lintegral_mono fun z => lintegral_mono fun z' => lintegral_mono_ae (by
          filter_upwards [hSae] with q hq
          exact Fk_enorm_le hσ w hWeq hτu z z' hq)
    _ < ⊤ := hconv

theorem Fk_integrable {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G}
    {μS ν : Measure G} [SFinite μS] [SFinite ν] (hS0 : μS Sᶜ = 0) {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hWc : Continuous W)
    (hconv : ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν < ⊤) :
    Integrable (fun x : G × G × G => Fk σ w W x.1 x.2.1 x.2.2) (ν.prod (ν.prod μS)) := by
  have hcont := continuous_Fk_uncurry hσ w hWc
  exact ⟨hcont.aestronglyMeasurable,
    lintegral_enorm_Fk_lt_infty hσ w hS0 hWeq hτu (continuous_enorm.measurable.comp hcont.measurable) hconv⟩

theorem integral_norm_sq_eq_one {ν : Measure G} {W : G → V} (hWc : Continuous W) (h2 : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν = 1) :
    ∫ z, ‖W z‖ ^ 2 ∂ν = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _)
    ((hWc.norm.pow 2).aestronglyMeasurable)]
  have h : (fun x => ENNReal.ofReal (‖W x‖ ^ 2)) = fun x => ‖W x‖ₑ ^ 2 := by
    funext x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rw [h, h2]
  simp

theorem integral_inner_mul_inner_eq_norm_sq_div {μ : Measure G} [μ.IsMulLeftInvariant] {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ}
    (hd : 0 < d) {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {ν : Measure G} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (z : G) :
    ∫ x, ⟪W x, W z⟫_ℂ * ⟪σ z w, σ x w⟫_ℂ ∂μ = ((‖W z‖ ^ 2 / d : ℝ) : ℂ) := by
  obtain ⟨hint, heq⟩ := hW.2.2.2.2.2.1 z
  rw [← integral_mul_left_eq_self _ z]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpt : ∀ y, ⟪W (z * y), W z⟫_ℂ * ⟪σ z w, σ (z * y) w⟫_ℂ =
      conj (((1 / d : ℝ) : ℂ) * ⟪W z, ((d : ℂ) * conj ⟪w, σ y w⟫_ℂ) • W (z * y)⟫_ℂ) := by
    intro y
    rw [hσ.2.1 z y, ContinuousLinearMap.mul_apply, hσ.2.2.1, inner_smul_right]
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, inner_conj_symm]
    push_cast
    first | (field_simp; ring) | field_simp | ring
  simp_rw [hpt]
  have hself : ⟪W z, W z⟫_ℂ = ((‖W z‖ ^ 2 : ℝ) : ℂ) := by
    refine Complex.ext ?_ ?_
    · first
        | simp [inner_self_eq_norm_sq]
        | (rw [Complex.ofReal_re]; exact inner_self_eq_norm_sq (𝕜 := ℂ) (W z))
    · first
        | simp
        | (rw [Complex.ofReal_im]; exact inner_self_im (𝕜 := ℂ) (W z))
  rw [integral_conj, integral_const_mul, integral_inner hint, heq, hself, ← Complex.ofReal_mul,
    Complex.conj_ofReal]
  congr 1
  ring

theorem Fk_value {μ : Measure G} [μ.IsMulLeftInvariant] {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ}
    (hd : 0 < d) {w : HH} {S : Set G} {μS ν : Measure G} [SFinite μS] [SFinite ν] (hq : IsQuot μ μS ν)
    {τ : G → (V →L[ℂ] V)} {W : G → V} (hW : IsWAbs μ σ d w S τ ν W)
    (hΦ : Integrable (fun x : G × G × G => Fk σ w W x.1 x.2.1 x.2.2) (ν.prod (ν.prod μS))) :
    ∫ x, Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) = ((1 / d : ℝ) : ℂ) := by
  have hWc : Continuous W := hW.2.2.2.2.1
  have hL2 := hW.2.2.2.2.2.2.2
  have hm : Measurable (fun p : G × G => p.2 * p.1) := measurable_snd.mul measurable_fst
  have hmap : μ = Measure.map (fun p : G × G => p.2 * p.1) (ν.prod μS) := by
    ext s hs
    rw [Measure.map_apply hm hs, ← lintegral_indicator_one hs, hq _ (measurable_one.indicator hs),
      ← lintegral_indicator_one (hm hs),
      lintegral_prod _ ((measurable_one.indicator (hm hs)).aemeasurable)]
    first
      | rfl
      | (simp only [Set.indicator_apply, Set.mem_preimage]; rfl)
  have hinner : ∀ z, ∫ y, Fk σ w W z y.1 y.2 ∂(ν.prod μS) = ((‖W z‖ ^ 2 / d : ℝ) : ℂ) := by
    intro z
    have hg := integral_inner_mul_inner_eq_norm_sq_div hσ hd hW z
    have hgc : Continuous (fun x : G => ⟪W x, W z⟫_ℂ * ⟪σ z w, σ x w⟫_ℂ) :=
      (hWc.inner continuous_const).mul (continuous_const.inner (hσ.2.2.2 w))
    rw [hmap, integral_map hm.aemeasurable hgc.aestronglyMeasurable] at hg
    exact hg
  rw [integral_prod _ hΦ]
  refine (integral_congr_ae (ae_of_all _ fun z => hinner z)).trans ?_
  first
    | rw [integral_complex_ofReal, integral_div, integral_norm_sq_eq_one hWc hL2]
    | rw [integral_ofReal, integral_div, integral_norm_sq_eq_one hWc hL2]

end Formalism.L2.S.Pv.EnergyAbs
end
end

section
noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

section Folner

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]

theorem ratio_le_one {μS : Measure G} {Ω A : Set G} (hA : A ⊆ Ω) (hfin : μS Ω < ⊤) :
    (μS A).toReal / (μS Ω).toReal ≤ 1 := by
  apply div_le_one_of_le₀ _ ENNReal.toReal_nonneg
  exact ENNReal.toReal_mono hfin.ne (measure_mono hA)

theorem ratio_nonneg {μS : Measure G} {Ω A : Set G} : 0 ≤ (μS A).toReal / (μS Ω).toReal := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem folner_seq [LocallyCompactSpace G] [SecondCountableTopology G] {S : Set G} {μS : Measure G}
    (hS : IsHaarSub S μS) (hF : IsFolner S μS) :
    ∃ Ω : ℕ → Set G, (∀ n, MeasurableSet (Ω n) ∧ Ω n ⊆ S ∧ 0 < μS (Ω n) ∧ μS (Ω n) < ⊤) ∧
      ∀ K : Set G, IsCompact K → K ⊆ S →
        Tendsto (fun n => (μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n}).toReal / (μS (Ω n)).toReal) atTop (𝓝 1) := by
  let Kx := CompactExhaustion.choice G
  have hε : ∀ n : ℕ, (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    ENNReal.ofReal_pos.mpr (by positivity)
  choose Ω hΩm hΩS hpos hfin hle using fun n : ℕ =>
    hF (Kx n ∩ S) ((Kx.isCompact n).inter_right hS.1) Set.inter_subset_right _ (hε n)
  refine ⟨Ω, fun n => ⟨hΩm n, hΩS n, hpos n, hfin n⟩, ?_⟩
  intro K hK hKS
  obtain ⟨N, hN⟩ := Kx.exists_superset_of_isCompact hK
  have hlow : Tendsto (fun n : ℕ => 1 / (1 + 1 / ((n : ℝ) + 1))) atTop (𝓝 1) := by
    have h1 := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
    have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / (1 + 1 / ((n : ℝ) + 1))) atTop (𝓝 (1 / (1 + 0))) :=
      tendsto_const_nhds.div h1 (by norm_num)
    rwa [add_zero, div_one] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hsub : {t | t ∈ Ω n ∧ ∀ k ∈ Kx n ∩ S, k * t ∈ Ω n} ⊆ {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n} :=
      fun t ht => ⟨ht.1, fun k hk => ht.2 k ⟨Kx.subset hn (hN hk), hKS hk⟩⟩
    have hAB := measure_mono (μ := μS) hsub
    have hBΩ : μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n} ≤ μS (Ω n) := measure_mono (fun t ht => ht.1)
    have hBfin := (hBΩ.trans_lt (hfin n)).ne
    have hAfin := ((hAB.trans hBΩ).trans_lt (hfin n)).ne
    have hΩpos : 0 < (μS (Ω n)).toReal := ENNReal.toReal_pos (hpos n).ne' (hfin n).ne
    have hkey := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hAfin) (hle n)
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_one] at hkey
    have hAB' := ENNReal.toReal_mono hBfin hAB
    have hc : 0 < 1 + 1 / ((n : ℝ) + 1) := by positivity
    rw [div_le_div_iff₀ hc hΩpos]
    nlinarith [mul_le_mul_of_nonneg_left hAB' hc.le]
  · exact Filter.Eventually.of_forall fun n => ratio_le_one (fun t ht => ht.1) (hfin n)

end Folner

section Limit

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def rat (μS : Measure G) (Ω : Set G) (q : G) : ℝ := (cnt μS Ω q).toReal / (μS Ω).toReal

theorem sumsq_div_eq {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) {S : Set G}
    {μS ν : Measure G} (hS : IsHaarSub S μS) [SFinite ν] {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hWc : Continuous W) (hW1 : ∫⁻ x, ‖W x‖ₑ ∂ν < ⊤) {Ω : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S)
    (hfin : μS Ω < ⊤)
    (hint : Integrable (fun x : G × G × G => rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2) (ν.prod (ν.prod μS))) :
    (((∑ i, ‖yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i)‖ ^ 2) / (μS Ω).toReal : ℝ) : ℂ) =
      ∫ x, rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) := by
  have : SigmaFinite μS := hS.2.2.2.2.1
  by_cases hm : (μS Ω).toReal = 0
  · simp [rat, hm]
  · have hI := ‹Integrable (fun x : G × G × G => rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2)
      (ν.prod (ν.prod μS))›
    have hfI : Integrable (fun x : G × G × G => (cnt μS Ω x.2.2).toReal • Fk σ w W x.1 x.2.1 x.2.2)
        (ν.prod (ν.prod μS)) := by
      refine (hI.smul (μS Ω).toReal).congr (ae_of_all _ fun x => ?_)
      simp only [Pi.smul_apply, rat, smul_smul]
      congr 1
      first
        | rw [mul_div_assoc', mul_div_cancel_left₀ _ hm]
        | field_simp
    have hprod : ∫ x, (cnt μS Ω x.2.2).toReal • Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) =
        ∫ z, ∫ z', ∫ q, (cnt μS Ω q).toReal • Fk σ w W z z' q ∂μS ∂ν ∂ν := by
      rw [integral_prod _ hfI]
      refine integral_congr_ae ?_
      filter_upwards [hfI.prod_right_ae] with z hz
      exact integral_prod _ hz
    have hrhs : ∫ x, rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) =
        ∫ x, ((μS Ω).toReal⁻¹ : ℝ) • ((cnt μS Ω x.2.2).toReal • Fk σ w W x.1 x.2.1 x.2.2)
          ∂(ν.prod (ν.prod μS)) := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [rat, smul_smul, div_eq_inv_mul]
    rw [hrhs, integral_smul, hprod, ← sumsq_eq hσ hw hS hWeq hτu hWc hW1 hΩm hΩS hfin,
      Complex.real_smul]
    push_cast
    ring

theorem folner_limit {μ : Measure G} [μ.IsHaarMeasure] {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH}
    {S : Set G} {μS ν : Measure G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hσ : IsUnitRep σ) (hSch : IsSchur μ σ d) (hw : ‖w‖ = 1) (hS : IsHaarSub S μS) (hν : SFinite ν)
    (hq : IsQuot μ μS ν) (hW : IsWAbs μ σ d w S τ ν W)
    (hconv : ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν < ⊤)
    (Ω : ℕ → Set G) (hΩ : ∀ n, MeasurableSet (Ω n) ∧ Ω n ⊆ S ∧ 0 < μS (Ω n) ∧ μS (Ω n) < ⊤)
    (hF : ∀ K : Set G, IsCompact K → K ⊆ S →
      Tendsto (fun n => (μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n}).toReal / (μS (Ω n)).toReal) atTop (𝓝 1)) :
    Tendsto (fun n => (∑ i, ‖yv μS ν σ w W (Ω n) (stdOrthonormalBasis ℂ V i)‖ ^ 2) / (μS (Ω n)).toReal)
      atTop (𝓝 (1 / d)) := by
  have : SFinite ν := hν
  have : SigmaFinite μS := hS.2.2.2.2.1
  have hd : 0 < d := hSch.1
  have hWeq := hW.2.2.2.1
  have hτu := hW.2.2.1
  have hWc := hW.2.2.2.2.1
  have hW1 := hW.2.2.2.2.2.2.1
  have hS0 : μS Sᶜ = 0 := hS.2.2.2.2.2.2.1
  have hΦ := Fk_integrable hσ w hS0 hWeq hτu hWc hconv
  have hmeas : ∀ n, Measurable (fun x : G × G × G => rat μS (Ω n) x.2.2) := fun n =>
    (((cnt_measurable (μS := μS) (hΩ n).1).ennreal_toReal).div_const _).comp measurable_snd.snd
  have hr : ∀ n q, 0 ≤ rat μS (Ω n) q ∧ rat μS (Ω n) q ≤ 1 := by
    intro n q
    unfold rat cnt
    exact ⟨ratio_nonneg, ratio_le_one (fun t ht => ht.1) (hΩ n).2.2.2⟩
  have hbound : ∀ n (x : G × G × G), ‖rat μS (Ω n) x.2.2 • Fk σ w W x.1 x.2.1 x.2.2‖ ≤
      ‖Fk σ w W x.1 x.2.1 x.2.2‖ := by
    intro n x
    rw [norm_smul, Real.norm_of_nonneg (hr n x.2.2).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hr n x.2.2).2
  have hint_r : ∀ n, Integrable (fun x : G × G × G => rat μS (Ω n) x.2.2 • Fk σ w W x.1 x.2.1 x.2.2)
      (ν.prod (ν.prod μS)) := fun n =>
    hΦ.mono ((hmeas n).aestronglyMeasurable.smul hΦ.aestronglyMeasurable) (ae_of_all _ (hbound n))
  have hS_ae : ∀ᵐ x ∂(ν.prod (ν.prod μS)), x.2.2 ∈ S := by
    rw [ae_iff]
    have hset : {x : G × G × G | ¬ x.2.2 ∈ S} = Set.univ ×ˢ (Set.univ ×ˢ Sᶜ) := by
      ext x; simp
    rw [hset, Measure.prod_prod, Measure.prod_prod, hS0, mul_zero, mul_zero]
  have hlim : Tendsto (fun n => ∫ x, rat μS (Ω n) x.2.2 • Fk σ w W x.1 x.2.1 x.2.2
      ∂(ν.prod (ν.prod μS))) atTop (𝓝 (∫ x, Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖Fk σ w W x.1 x.2.1 x.2.2‖)
      (fun n => (hint_r n).aestronglyMeasurable) hΦ.norm (fun n => ae_of_all _ (hbound n)) ?_
    filter_upwards [hS_ae] with x hx
    have h1 : Tendsto (fun n => rat μS (Ω n) x.2.2) atTop (𝓝 1) := by
      have h0 := hF {x.2.2} isCompact_singleton (Set.singleton_subset_iff.mpr hx)
      simpa [rat, cnt] using h0
    have h2 := h1.smul_const (Fk σ w W x.1 x.2.1 x.2.2)
    rwa [one_smul] at h2
  rw [Fk_value hσ hd hq hW hΦ] at hlim
  have hlim' : Tendsto (fun n => (((∑ i, ‖yv μS ν σ w W (Ω n) (stdOrthonormalBasis ℂ V i)‖ ^ 2) /
      (μS (Ω n)).toReal : ℝ) : ℂ)) atTop (𝓝 ((1 / d : ℝ) : ℂ)) :=
    hlim.congr fun n => (sumsq_div_eq hσ hw hS hWeq hτu hWc hW1 (hΩ n).1 (hΩ n).2.1
      (hΩ n).2.2.2 (hint_r n)).symm
  have h3 := (Complex.continuous_re.tendsto _).comp hlim'
  simpa only [Function.comp_def, Complex.ofReal_re] using h3

end Limit

end Formalism.L2.S.Pv.EnergyAbs
end
end

section
noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem continuous_hsA_Xop {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (μS ν μS' ν' : Measure G) (d : ℝ)
    (w : HH) (W : G → V) (W' : G → V') (A A' : Set G) :
    Continuous (fun g => hsA (Xop μS ν μS' ν' σ d w W W' A A' g)) := by
  have hc : ∀ a : HH, Continuous (fun g => σ g a) := hσ.2.2.2
  unfold hsA Xop sand
  refine continuous_finsetSum _ fun i _ => ?_
  refine (continuous_norm.comp ?_).pow 2
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply]
  exact ((ContinuousLinearMap.adjoint _).continuous.comp (hc _)).const_smul _

theorem lintegral_hsA_Xop {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} (hSch : IsSchur μ σ d)
    (μS ν μS' ν' : Measure G) (w : HH) (W : G → V) (W' : G → V') (A A' : Set G) :
    ∫⁻ g, ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' A A' g)) ∂μ =
      ENNReal.ofReal (d * (∑ i, ‖yv μS ν σ w W A (stdOrthonormalBasis ℂ V i)‖ ^ 2) *
        (∑ j, ‖yv μS' ν' σ w W' A' (stdOrthonormalBasis ℂ V' j)‖ ^ 2)) := by
  have hd : 0 < d := hSch.1
  have h1 : ∀ g, ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' A A' g)) =
      ENNReal.ofReal (d ^ 2) *
        ENNReal.ofReal (hsA (sand σ (Yop μS ν σ w W A) (Yop μS' ν' σ w W' A') g)) := by
    intro g
    rw [Xop, hsA_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_mul (sq_nonneg d)]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_hsA_sand hSch,
    ← ENNReal.ofReal_mul (sq_nonneg d)]
  congr 1
  simp only [Yop_apply_basis]
  field_simp

theorem tendsto_energy {d : ℝ} (hd : 0 < d) {a b : ℕ → ℝ≥0∞} (ha : ∀ n, 0 < a n ∧ a n < ⊤)
    (hb : ∀ n, 0 < b n ∧ b n < ⊤) {N N' : ℕ → ℝ}
    (hN : Tendsto (fun n => N n / (a n).toReal) atTop (𝓝 (1 / d)))
    (hN' : Tendsto (fun n => N' n / (b n).toReal) atTop (𝓝 (1 / d))) :
    Tendsto (fun n => (a n * b n)⁻¹ * ENNReal.ofReal (d * N n * N' n)) atTop (𝓝 (ENNReal.ofReal (1 / d))) := by
  have key : ∀ n, (a n * b n)⁻¹ * ENNReal.ofReal (d * N n * N' n) =
      ENNReal.ofReal (d * (N n / (a n).toReal) * (N' n / (b n).toReal)) := by
    intro n
    obtain ⟨ha0, hat⟩ := ha n
    obtain ⟨hb0, hbt⟩ := hb n
    have ha' : 0 < (a n).toReal := ENNReal.toReal_pos ha0.ne' hat.ne
    have hb' : 0 < (b n).toReal := ENNReal.toReal_pos hb0.ne' hbt.ne
    have hab : (a n * b n)⁻¹ = ENNReal.ofReal (((a n).toReal * (b n).toReal)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos (mul_pos ha' hb'), ← ENNReal.toReal_mul,
        ENNReal.ofReal_toReal (ENNReal.mul_ne_top hat.ne hbt.ne)]
    rw [hab, ← ENNReal.ofReal_mul (inv_nonneg.mpr (mul_pos ha' hb').le)]
    congr 1
    field_simp
  simp_rw [key]
  apply ENNReal.tendsto_ofReal
  have hlim := (hN.const_mul d).mul hN'
  rwa [show d * (1 / d) * (1 / d) = 1 / d by field_simp] at hlim

end Formalism.L2.S.Pv.EnergyAbs
end
end

section
noncomputable section

open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def K4 (σ : G → (HH →L[ℂ] HH)) (d : ℝ) (w : HH) (W : G → V) (W' : G → V') (γ : G)
    (q : (G × G) × (G × G)) : V' →L[ℂ] V :=
  kG σ d w W W' γ (φinv q.1, φinv q.2)

section Hyp

variable {μ ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
  {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)}
  {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}

theorem integrable_liftedRankOneKernel (hσ : IsUnitRep σ) (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    Integrable (K4 σ d w W W' γ) ((ν.prod μS).prod (ν'.prod μS')) := by
  have hi := integrable_kG hσ hW hW' hinv hinv' h0 h0' hm hm' γ hB
  rw [prod_map_φinv hm hm'] at hi
  exact hi.comp_measurable (Measurable.prodMap (measurable_φinv (G := G)) (measurable_φinv (G := G)))

theorem integral_liftedRankOneKernel [μ.IsMulLeftInvariant] [SFinite μ] (hσ : IsUnitRep σ) (hW : IsWAbs μ σ d w S τ ν W)
    (hW' : IsWAbs μ σ d w S' τ' ν' W') (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S')
    (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    ∫ q, K4 σ d w W W' γ q ∂((ν.prod μS).prod (ν'.prod μS')) = ∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ := by
  have hi := integrable_kG hσ hW hW' hinv hinv' h0 h0' hm hm' γ hB
  have hF : Measurable (Prod.map (φinv : G × G → G) (φinv : G × G → G)) :=
    Measurable.prodMap (measurable_φinv (G := G)) (measurable_φinv (G := G))
  have hi' := hi
  rw [prod_map_φinv hm hm'] at hi'
  rw [← integral_kG hσ hW W' γ hi, prod_map_φinv hm hm',
    integral_map hF.aemeasurable hi'.aestronglyMeasurable]
  rfl

theorem prod_restrict_four (A A' : Set G) :
    (ν.prod (μS.restrict A)).prod (ν'.prod (μS'.restrict A')) =
      ((ν.prod μS).prod (ν'.prod μS')).restrict ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A')) := by
  have e1 : ν.prod (μS.restrict A) = (ν.prod μS).restrict (Set.univ ×ˢ A) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have e2 : ν'.prod (μS'.restrict A') = (ν'.prod μS').restrict (Set.univ ×ˢ A') := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [e1, e2, Measure.prod_restrict]

end Hyp

section Approx

variable {μ ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
  {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)}
  {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}

theorem approx_OO [μ.IsMulLeftInvariant] [SFinite μ] (hσ : IsUnitRep σ) (hW : IsWAbs μ σ d w S τ ν W)
    (hW' : IsWAbs μ σ d w S' τ' ν' W') (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S')
    (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤)
    (C C' : ℕ → Set G) (hCm : ∀ n, MeasurableSet (C n)) (hC'm : ∀ n, MeasurableSet (C' n))
    (hCmono : Monotone C) (hC'mono : Monotone C') (hCS : S ⊆ ⋃ n, C n) (hC'S : S' ⊆ ⋃ n, C' n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀, ∀ A A' : Set G, MeasurableSet A → A ⊆ S → μS A < ⊤ → MeasurableSet A' → A' ⊆ S' → μS' A' < ⊤ →
      C n₀ ⊆ A → C' n₀ ⊆ A' →
      Real.sqrt (hsA (∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ - Xop μS ν μS' ν' σ d w W W' A A' γ)) ≤ ε := by
  set P := (ν.prod μS).prod (ν'.prod μS') with hP
  have hK4 := integrable_liftedRankOneKernel hσ hW hW' hinv hinv' h0 h0' hm hm' γ hB
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ X : V' →L[ℂ] V, Real.sqrt (hsA X) ≤ c * ‖X‖ :=
    ⟨‖hsC (V := V) (V' := V')‖, norm_nonneg _, fun X => by
      rw [← norm_hsC]
      exact ContinuousLinearMap.le_opNorm _ _⟩
  let Rn : ℕ → Set ((G × G) × (G × G)) := fun n => (Set.univ ×ˢ C n) ×ˢ (Set.univ ×ˢ C' n)
  have hRm : ∀ n, MeasurableSet (Rn n) := fun n =>
    (MeasurableSet.univ.prod (hCm n)).prod (MeasurableSet.univ.prod (hC'm n))
  have hanti : Antitone fun n => (Rn n)ᶜ := fun n m hnm =>
    Set.compl_subset_compl.mpr
      (Set.prod_mono (Set.prod_mono subset_rfl (hCmono hnm)) (Set.prod_mono subset_rfl (hC'mono hnm)))
  have hnull : P (⋂ n, (Rn n)ᶜ) = 0 := by
    have hae := ae_mem_four (ν := ν) (μS := μS) (ν' := ν') (μS' := μS') h0 h0'
    rw [ae_iff] at hae
    refine measure_mono_null (fun p hp => ?_) hae
    simp only [Set.mem_iInter, Set.mem_compl_iff] at hp
    rintro ⟨h1, h2⟩
    obtain ⟨n1, hn1⟩ := Set.mem_iUnion.mp (hCS h1)
    obtain ⟨n2, hn2⟩ := Set.mem_iUnion.mp (hC'S h2)
    exact hp (max n1 n2)
      ⟨⟨trivial, hCmono (le_max_left _ _) hn1⟩, ⟨trivial, hC'mono (le_max_right _ _) hn2⟩⟩
  have hT := tendsto_setIntegral_of_antitone (μ := P) (f := fun q => ‖K4 σ d w W W' γ q‖)
    (fun n => (hRm n).compl) hanti ⟨0, hK4.norm.integrableOn⟩
  rw [setIntegral_measure_zero _ hnull] at hT
  have hT' := hT.const_mul c
  rw [mul_zero] at hT'
  obtain ⟨n₀, hn₀⟩ := (hT'.eventually (gt_mem_nhds hε)).exists
  refine ⟨n₀, fun A A' hA hAS hAf hA' hAS' hAf' hCA hC'A => ?_⟩
  have hR : MeasurableSet (((Set.univ : Set G) ×ˢ A) ×ˢ ((Set.univ : Set G) ×ˢ A')) :=
    (MeasurableSet.univ.prod hA).prod (MeasurableSet.univ.prod hA')
  have hX : Xop μS ν μS' ν' σ d w W W' A A' γ =
      ∫ q in (Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'), K4 σ d w W W' γ q ∂P := by
    rw [Xop_eq_integral hσ hW hW' hinv hinv' hA hAS hAf hA' hAS' hAf' γ
      (by rw [prod_restrict_four]; exact hK4.restrict), prod_restrict_four]
    rfl
  have hdiff : ∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ - Xop μS ν μS' ν' σ d w W W' A A' γ =
      ∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, K4 σ d w W W' γ q ∂P := by
    rw [← integral_liftedRankOneKernel hσ hW hW' hinv hinv' h0 h0' hm hm' γ hB, hX, setIntegral_compl hR hK4]
  have hsub : ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ ⊆ (Rn n₀)ᶜ :=
    Set.compl_subset_compl.mpr
      (Set.prod_mono (Set.prod_mono subset_rfl hCA) (Set.prod_mono subset_rfl hC'A))
  rw [hdiff]
  calc Real.sqrt (hsA (∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, K4 σ d w W W' γ q ∂P))
      ≤ ∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, Real.sqrt (hsA (K4 σ d w W W' γ q)) ∂P :=
        sqrt_hsA_integral_le _ hK4.restrict
    _ ≤ ∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, c * ‖K4 σ d w W W' γ q‖ ∂P :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => Real.sqrt_nonneg _)
          (hK4.norm.const_mul c).restrict (Filter.Eventually.of_forall fun q => hc _)
    _ = c * ∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, ‖K4 σ d w W W' γ q‖ ∂P :=
        integral_const_mul c _
    _ ≤ c * ∫ q in (Rn n₀)ᶜ, ‖K4 σ d w W W' γ q‖ ∂P :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set hK4.norm.integrableOn
          (Filter.Eventually.of_forall fun q => norm_nonneg _) hsub.eventuallyLE) hc0
    _ ≤ ε := hn₀.le

end Approx

end Formalism.L2.S.Pv.EnergyAbs
end
end

section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Measure Filter Topology
open scoped ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

variable {G : Type} [Group G] [MeasurableSpace G]

theorem lintegral_ge_rect {μS μS' : Measure G} [SFinite μS'] (f : G → G → ℝ≥0∞)
    (hf : Measurable (fun p : G × G => f p.1 p.2)) (E E' : Set G) (c : ℝ≥0∞)
    (h : ∀ s ∈ E, ∀ s' ∈ E', c ≤ f s s') : c * μS' E' * μS E ≤ ∫⁻ s, ∫⁻ s', f s s' ∂μS' ∂μS := by
  have hsec : ∀ s, Measurable (f s) := fun s =>
    hf.comp (by fun_prop : Measurable (fun s' : G => (s, s')))
  have hin : ∀ s ∈ E, c * μS' E' ≤ ∫⁻ s', f s s' ∂μS' := by
    intro s hs
    calc c * μS' E' ≤ c * μS' {s' | c ≤ f s s'} :=
          mul_le_mul' le_rfl (measure_mono fun s' hs' => h s hs s' hs')
      _ ≤ _ := mul_meas_ge_le_lintegral₀ (hsec s).aemeasurable c
  have hg : Measurable (fun s => ∫⁻ s', f s s' ∂μS') := hf.lintegral_prod_right'
  calc c * μS' E' * μS E ≤ c * μS' E' * μS {s | c * μS' E' ≤ ∫⁻ s', f s s' ∂μS'} :=
        mul_le_mul' le_rfl (measure_mono fun s hs => hin s hs)
    _ ≤ _ := mul_meas_ge_le_lintegral₀ hg.aemeasurable _

def folInt (Ω K : Set G) : Set G := {t | t ∈ Ω ∧ ∀ k ∈ K, k * t ∈ Ω}

theorem measure_inv_preimage {μS : Measure G} [MeasurableInv G] (hinv : μS.map (fun x => x⁻¹) = μS)
    (B : Set G) : μS {s | s⁻¹ ∈ B} = μS B := by
  have e : (μS.map (MeasurableEquiv.inv G)) B = μS ((MeasurableEquiv.inv G) ⁻¹' B) :=
    MeasurableEquiv.map_apply _ _
  have hm : μS.map (MeasurableEquiv.inv G) = μS := hinv
  rw [hm] at e
  exact e.symm

theorem tendsto_ratio_ennreal {a b : ℕ → ℝ≥0∞} (hb0 : ∀ n, 0 < b n) (hbt : ∀ n, b n < ⊤)
    (hab : ∀ n, a n ≤ b n) (h : Tendsto (fun n => (a n).toReal / (b n).toReal) atTop (𝓝 1)) :
    Tendsto (fun n => a n / b n) atTop (𝓝 1) := by
  have hfin : ∀ n, a n / b n ≠ ⊤ := fun n =>
    ENNReal.div_ne_top (ne_top_of_le_ne_top (hbt n).ne (hab n)) (hb0 n).ne'
  have hfun : (fun n => a n / b n) = fun n => ENNReal.ofReal ((a n).toReal / (b n).toReal) := by
    funext n
    rw [← ENNReal.toReal_div, ENNReal.ofReal_toReal (hfin n)]
  rw [hfun, ← ENNReal.ofReal_one]
  exact ENNReal.tendsto_ofReal h

theorem liminf_lower {μS μS' : Measure G} [SFinite μS'] [MeasurableInv G]
    (hinv : μS.map (fun x => x⁻¹) = μS) (hinv' : μS'.map (fun x => x⁻¹) = μS')
    (Ω Ω' : ℕ → Set G) (hΩ0 : ∀ n, 0 < μS (Ω n)) (hΩt : ∀ n, μS (Ω n) < ⊤)
    (hΩ0' : ∀ n, 0 < μS' (Ω' n)) (hΩt' : ∀ n, μS' (Ω' n) < ⊤)
    (f : ℕ → G → G → ℝ≥0∞) (hf : ∀ n, Measurable (fun p : G × G => f n p.1 p.2)) (h : ℝ) (hh : 0 ≤ h)
    (key : ∀ ε : ℝ, 0 < ε → ∃ K K' : Set G,
      Tendsto (fun n => μS (folInt (Ω n) K) / μS (Ω n)) atTop (𝓝 1) ∧
      Tendsto (fun n => μS' (folInt (Ω' n) K') / μS' (Ω' n)) atTop (𝓝 1) ∧
      ∀ n s s', s⁻¹ ∈ folInt (Ω n) K → s'⁻¹ ∈ folInt (Ω' n) K' →
        ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) ≤ f n s s') :
    ENNReal.ofReal h ≤
      liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ * ∫⁻ s, ∫⁻ s', f n s s' ∂μS' ∂μS) atTop := by
  set L := liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ * ∫⁻ s, ∫⁻ s', f n s s' ∂μS' ∂μS) atTop
    with hL
  have step : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) ≤ L := by
    intro ε hε
    obtain ⟨K, K', hK, hK', hf'⟩ := key ε hε
    set c := ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) with hc
    have hlim : Tendsto (fun n => c * ((μS (folInt (Ω n) K) / μS (Ω n)) *
        (μS' (folInt (Ω' n) K') / μS' (Ω' n)))) atTop (𝓝 c) := by
      have h1 := ENNReal.Tendsto.mul hK (Or.inl one_ne_zero) hK' (Or.inl one_ne_zero)
      have h2 := ENNReal.Tendsto.const_mul h1 (a := c) (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_one, mul_one] at h2
      exact h2
    rw [hL, ← hlim.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    have hA0 := (hΩ0 n).ne'
    have hAt := (hΩt n).ne
    have hmain := lintegral_ge_rect (μS := μS) (μS' := μS') (f n) (hf n)
      {s | s⁻¹ ∈ folInt (Ω n) K} {s' | s'⁻¹ ∈ folInt (Ω' n) K'} c
      (fun s hs s' hs' => hf' n s s' hs hs')
    rw [measure_inv_preimage hinv, measure_inv_preimage hinv'] at hmain
    rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt), div_eq_mul_inv, div_eq_mul_inv]
    calc c * (μS (folInt (Ω n) K) * (μS (Ω n))⁻¹ *
          (μS' (folInt (Ω' n) K') * (μS' (Ω' n))⁻¹))
        = (μS (Ω n))⁻¹ * (μS' (Ω' n))⁻¹ *
          (c * μS' (folInt (Ω' n) K') * μS (folInt (Ω n) K)) := by ring
      _ ≤ _ := mul_le_mul' le_rfl hmain
  have hcont : Continuous (fun ε : ℝ => ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2)) :=
    ENNReal.continuous_ofReal.comp (((continuous_const.sub continuous_id).max continuous_const).pow 2)
  have h0 : ENNReal.ofReal ((max (Real.sqrt h - 0) 0) ^ 2) = ENNReal.ofReal h := by
    rw [sub_zero, max_eq_left (Real.sqrt_nonneg h), Real.sq_sqrt hh]
  have hg : Tendsto (fun ε : ℝ => ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal h)) := by
    rw [← h0]
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hg (eventually_nhdsWithin_of_forall fun ε hε => step ε hε)

end Formalism.L2.S.Pv.EnergyAbs
end
end

section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem fY_linear (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (e : V) (p : G × G) :
    ∑ i, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • fY σ w W (stdOrthonormalBasis ℂ V i) p = fY σ w W e p := by
  simp only [fY]
  simp_rw [smul_smul, ← Finset.sum_smul]
  congr 1
  rw [← (stdOrthonormalBasis ℂ V).sum_inner_mul_inner (W (p.2⁻¹ * p.1)) e]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem Yop_apply_integral {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν : Measure G} [SFinite ν]
    [SFinite μS] {d : ℝ} {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (hinv : ∀ a ∈ S, a⁻¹ ∈ S) {A : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hAf : μS A < ⊤) (e : V) :
    Yop μS ν σ w W A e = ∫ p, fY σ w W e p ∂(ν.prod (μS.restrict A)) := by
  rw [Yop_apply]
  simp_rw [yv_eq_integral hσ hW hinv hA hAS hAf]
  have hint : ∀ i, Integrable (fun p => ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ •
      fY σ w W (stdOrthonormalBasis ℂ V i) p) (ν.prod (μS.restrict A)) :=
    fun i => (integrable_fY hσ hW hinv hA hAS hAf _).smul _
  symm
  calc ∫ p, fY σ w W e p ∂(ν.prod (μS.restrict A))
      = ∫ p, ∑ i, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • fY σ w W (stdOrthonormalBasis ℂ V i) p
          ∂(ν.prod (μS.restrict A)) := by
        congr 1
        funext p
        exact (fY_linear σ w W e p).symm
    _ = ∑ i, ∫ p, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • fY σ w W (stdOrthonormalBasis ℂ V i) p
          ∂(ν.prod (μS.restrict A)) := integral_finsetSum _ fun i _ => hint i
    _ = _ := by simp_rw [integral_smul]

theorem prod_restrict_translate {μS : Measure G} [SFinite μS] (ν : Measure G) [SFinite ν] {s0 : G}
    (hmap : μS.map (fun x => x * s0⁻¹) = μS) (A : Set G) :
    ν.prod (μS.restrict A) =
      (ν.prod (μS.restrict ((fun v => v * s0⁻¹) ⁻¹' A))).map (Prod.map id (fun v => v * s0⁻¹)) := by
  have hE := (MeasurableEquiv.mulRight (s0⁻¹ : G)).measurableEmbedding.restrict_map μS A
  rw [MeasurableEquiv.coe_mulRight, hmap] at hE
  rw [← Measure.map_prod_map ν _ measurable_id (measurable_mul_const s0⁻¹), Measure.map_id, ← hE]

theorem sigma_Yop {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν : Measure G} [SFinite ν] {S : Set G}
    (hS : IsHaarSub S μS) {d : ℝ} {w : HH} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) {A : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S) (hAf : μS A < ⊤)
    {s0 : G} (hs0 : s0 ∈ S) (e : V) :
    σ s0⁻¹ (Yop μS ν σ w W A e) =
      Yop μS ν σ w W ((fun v => v * s0⁻¹) ⁻¹' A) (ContinuousLinearMap.adjoint (τ s0) e) := by
  obtain ⟨-, -, hmulS, hinvS, hsig, -, -, -, -, hright, -⟩ := hS
  have : SFinite μS := by have := hsig; infer_instance
  have hmap : μS.map (fun x => x * s0⁻¹) = μS := hright _ (hinvS s0 hs0)
  have hA'm : MeasurableSet ((fun v => v * s0⁻¹) ⁻¹' A) := measurable_mul_const s0⁻¹ hA
  have hA'S : (fun v => v * s0⁻¹) ⁻¹' A ⊆ S := by
    intro v hv
    have h1 := hmulS _ (hAS hv) s0 hs0
    simpa [mul_assoc] using h1
  have hA'f : μS ((fun v => v * s0⁻¹) ⁻¹' A) < ⊤ := by
    rw [← Measure.map_apply (measurable_mul_const s0⁻¹) hA, hmap]
    exact hAf
  have hemb : MeasurableEmbedding (Prod.map id (fun v : G => v * s0⁻¹)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl G) (MeasurableEquiv.mulRight s0⁻¹)).measurableEmbedding

  rw [Yop_apply_integral hσ hW hinvS hA hAS hAf, Yop_apply_integral hσ hW hinvS hA'm hA'S hA'f,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_fY hσ hW hinvS hA hAS hAf e),
    prod_restrict_translate ν hmap A, hemb.integral_map]
  congr 1
  funext p
  simp only [fY, Prod.map, id, map_smul]
  have hq : (p.2 * s0⁻¹)⁻¹ * p.1 = s0 * (p.2⁻¹ * p.1) := by group
  rw [hq, rep_mul_apply hσ, inv_mul_cancel_left, hW.2.2.2.1 s0 hs0,
    ContinuousLinearMap.adjoint_inner_right]

theorem sand_translate {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν μS' ν' : Measure G} [SFinite ν]
    [SFinite ν'] {S S' : Set G} (hS : IsHaarSub S μS) (hS' : IsHaarSub S' μS') {d : ℝ} {w : HH}
    {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    {Ω Ω' : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) (hΩf : μS Ω < ⊤)
    (hΩm' : MeasurableSet Ω') (hΩS' : Ω' ⊆ S') (hΩf' : μS' Ω' < ⊤)
    {s0 s0' : G} (hs0 : s0 ∈ S) (hs0' : s0' ∈ S') (γ : G) :
    sand σ (Yop μS ν σ w W Ω) (Yop μS' ν' σ w W' Ω') (s0 * γ * s0'⁻¹) =
      (τ s0).comp ((sand σ (Yop μS ν σ w W ((fun v => v * s0⁻¹) ⁻¹' Ω))
        (Yop μS' ν' σ w W' ((fun v => v * s0'⁻¹) ⁻¹' Ω')) γ).comp (ContinuousLinearMap.adjoint (τ' s0'))) := by
  ext b
  refine ext_inner_left ℂ fun a => ?_
  rw [inner_sand]
  conv_rhs => rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_left, inner_sand]
  rw [← sigma_Yop hσ hS hW hΩm hΩS hΩf hs0 a, ← sigma_Yop hσ hS' hW' hΩm' hΩS' hΩf' hs0' b]
  have hmove : ∀ u : HH, σ γ (σ s0'⁻¹ u) = σ s0⁻¹ (σ (s0 * γ * s0'⁻¹) u) := by
    intro u
    rw [rep_mul_apply hσ, rep_mul_apply hσ, show s0⁻¹ * (s0 * γ * s0'⁻¹) = γ * s0'⁻¹ by group]
  rw [hmove, hσ.2.2.1]

theorem hsA_Xop_translate {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH} {S S' : Set G}
    {μS ν μS' ν' : Measure G} {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    [SFinite ν] [SFinite ν'] (hσ : IsUnitRep σ) (hS : IsHaarSub S μS) (hS' : IsHaarSub S' μS')
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    {Ω Ω' : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) (hΩf : μS Ω < ⊤)
    (hΩm' : MeasurableSet Ω') (hΩS' : Ω' ⊆ S') (hΩf' : μS' Ω' < ⊤)
    {s0 s0' : G} (hs0 : s0 ∈ S) (hs0' : s0' ∈ S') (γ : G) :
    hsA (Xop μS ν μS' ν' σ d w W W' Ω Ω' (s0 * γ * s0'⁻¹)) =
      hsA (Xop μS ν μS' ν' σ d w W W' ((fun v => v * s0⁻¹) ⁻¹' Ω) ((fun v => v * s0'⁻¹) ⁻¹' Ω') γ) := by
  simp only [Xop]
  rw [hsA_smul, hsA_smul, sand_translate hσ hS hS' hW hW' hΩm hΩS hΩf hΩm' hΩS' hΩf' hs0 hs0' γ,
    hsA_conj (τ s0) (τ' s0') (hW.2.2.1 s0 hs0) (hW'.2.2.1 s0' hs0')]

end Formalism.L2.S.Pv.EnergyAbs
end
end

section
noncomputable section

open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def cpiece (S : Set G) (n : ℕ) : Set G := CompactExhaustion.choice G n ∩ S

theorem cpiece_compact {S : Set G} (hS : IsClosed S) (n : ℕ) : IsCompact (cpiece S n) :=
  ((CompactExhaustion.choice G).isCompact n).inter_right hS

theorem cpiece_mono (S : Set G) : Monotone (cpiece S) := by
  intro m n hmn
  exact Set.inter_subset_inter_left _ ((CompactExhaustion.choice G).subset hmn)

theorem cpiece_cover (S : Set G) : S ⊆ ⋃ n, cpiece S n := by
  intro x hx
  obtain ⟨n, hn⟩ := (CompactExhaustion.choice G).exists_mem x
  exact Set.mem_iUnion.2 ⟨n, hn, hx⟩

theorem translate_props {μS : Measure G} {S : Set G} (hS : IsHaarSub S μS) {Ω : Set G} (hΩm : MeasurableSet Ω)
    (hΩS : Ω ⊆ S) (hΩt : μS Ω < ⊤) {s : G} (hs : s ∈ S) :
    MeasurableSet ((fun v => v * s⁻¹) ⁻¹' Ω) ∧ (fun v => v * s⁻¹) ⁻¹' Ω ⊆ S ∧
      μS ((fun v => v * s⁻¹) ⁻¹' Ω) < ⊤ := by
  obtain ⟨-, -, hmul, hinv, -, -, -, -, -, hr, -⟩ := hS
  refine ⟨hΩm.preimage (measurable_mul_const s⁻¹), fun v hv => ?_, ?_⟩
  · have h1 : v * s⁻¹ * s ∈ S := hmul _ (@hΩS (v * s⁻¹) hv) _ hs
    simpa using h1
  · rw [← Measure.map_apply (measurable_mul_const s⁻¹) hΩm, hr _ (hinv _ hs)]
    exact hΩt

private theorem hilbertSchmidtSq_nonneg_aux_lemma (A : V' →L[ℂ] V) : 0 ≤ Formalism.L2.SG.Pf.EnergyAbs.hsA A := by
  unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

private theorem sq_max_le_hilbertSchmidtSq_lemma_2 (A B : V' →L[ℂ] V) {ε : ℝ}
    (h : Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA (A - B)) ≤ ε) :
    max (Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA A) - ε) 0 ^ 2 ≤ Formalism.L2.SG.Pf.EnergyAbs.hsA B := by
  have hB := hilbertSchmidtSq_nonneg_aux_lemma B
  have htri := sqrt_hsA_le_add_sub A B
  have hmax : max (Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA A) - ε) 0 ≤ Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA B) :=
    max_le (by linarith) (Real.sqrt_nonneg _)
  calc max (Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA A) - ε) 0 ^ 2 ≤ Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA B) ^ 2 :=
        pow_le_pow_left₀ (le_max_right _ _) hmax 2
    _ = Formalism.L2.SG.Pf.EnergyAbs.hsA B := Real.sq_sqrt hB

theorem point_lower {μ : Measure G} [μ.IsHaarMeasure] {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ}
    {w : HH} {S S' : Set G} {μS μS' ν ν' : Measure G} {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')}
    {W : G → V} {W' : G → V'} [SFinite ν] [SFinite ν'] (hS : IsHaarSub S μS) (hS' : IsHaarSub S' μS')
    (hq : IsQuot μ μS ν) (hq' : IsQuot μ μS' ν')
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (Ω Ω' : ℕ → Set G) (hΩ : ∀ n, MeasurableSet (Ω n) ∧ Ω n ⊆ S ∧ 0 < μS (Ω n) ∧ μS (Ω n) < ⊤)
    (hΩ' : ∀ n, MeasurableSet (Ω' n) ∧ Ω' n ⊆ S' ∧ 0 < μS' (Ω' n) ∧ μS' (Ω' n) < ⊤)
    (hF : ∀ K : Set G, IsCompact K → K ⊆ S → Tendsto (fun n =>
      (μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n}).toReal / (μS (Ω n)).toReal) atTop (𝓝 1))
    (hF' : ∀ K : Set G, IsCompact K → K ⊆ S' → Tendsto (fun n =>
      (μS' {t | t ∈ Ω' n ∧ ∀ k ∈ K, k * t ∈ Ω' n}).toReal / (μS' (Ω' n)).toReal) atTop (𝓝 1))
    (hXc : ∀ n, Continuous (fun g => hsA (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) g)))
    (γ : G) (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    ENNReal.ofReal (hsA (∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ)) ≤
      liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ *
        ∫⁻ s, ∫⁻ s', ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) (s * γ * s'⁻¹)))
          ∂μS' ∂μS) atTop := by
  have hS₀ := hS
  have hS'₀ := hS'
  obtain ⟨hSc, -, -, hinvS, hσS, -, h0S, -, -, -, hinvmS⟩ := hS₀
  obtain ⟨hSc', -, -, hinvS', hσS', -, h0S', -, -, -, hinvmS'⟩ := hS'₀
  have : SigmaFinite μS := hσS
  have : SigmaFinite μS' := hσS'
  have hm : μ = (ν.prod μS).map φinv := (quot_map_inv hq) hinvmS
  have hm' : μ = (ν'.prod μS').map φinv := (quot_map_inv hq') hinvmS'
  refine liminf_lower hinvmS hinvmS' Ω Ω'
    (fun n => (hΩ n).2.2.1) (fun n => (hΩ n).2.2.2) (fun n => (hΩ' n).2.2.1) (fun n => (hΩ' n).2.2.2)
    (fun n s s' => ENNReal.ofReal (Formalism.L2.SG.Pf.EnergyAbs.hsA
      (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) (s * γ * s'⁻¹))))
    (fun n => ?_) (Formalism.L2.SG.Pf.EnergyAbs.hsA (∫ x, Formalism.L2.SG.Pf.EnergyAbs.rk1A (W x) (W' (γ⁻¹ * x)) ∂μ))
    (hilbertSchmidtSq_nonneg_aux_lemma _) (fun ε hε => ?_)
  · exact ENNReal.measurable_ofReal.comp ((hXc n).measurable.comp
      ((continuous_fst.mul continuous_const).mul continuous_snd.inv).measurable)
  · obtain ⟨n₀, hn₀⟩ := approx_OO hσ hW hW' hinvS hinvS' h0S h0S' hm hm' γ hB
      (cpiece S) (cpiece S')
      (fun n => (cpiece_compact hSc n).isClosed.measurableSet)
      (fun n => (cpiece_compact hSc' n).isClosed.measurableSet)
      (cpiece_mono S) (cpiece_mono S')
      (cpiece_cover S) (cpiece_cover S') ε hε
    refine ⟨cpiece S n₀, cpiece S' n₀, ?_, ?_, ?_⟩
    · refine tendsto_ratio_ennreal (fun n => (hΩ n).2.2.1) (fun n => (hΩ n).2.2.2)
        (fun n => measure_mono fun t ht => (show t ∈ Ω n ∧ _ from ht).1) ?_
      exact hF _ (cpiece_compact hSc n₀) Set.inter_subset_right
    · refine tendsto_ratio_ennreal (fun n => (hΩ' n).2.2.1) (fun n => (hΩ' n).2.2.2)
        (fun n => measure_mono fun t ht => (show t ∈ Ω' n ∧ _ from ht).1) ?_
      exact hF' _ (cpiece_compact hSc' n₀) Set.inter_subset_right
    · intro n s s' hs hs'
      have hs2 : s⁻¹ ∈ Ω n ∧ ∀ k ∈ cpiece S n₀, k * s⁻¹ ∈ Ω n := hs
      have hs2' : s'⁻¹ ∈ Ω' n ∧ ∀ k ∈ cpiece S' n₀, k * s'⁻¹ ∈ Ω' n := hs'
      have hsS : s ∈ S := by simpa using hinvS _ ((hΩ n).2.1 hs2.1)
      have hsS' : s' ∈ S' := by simpa using hinvS' _ ((hΩ' n).2.1 hs2'.1)
      obtain ⟨hAm, hAS, hAt⟩ := translate_props hS (hΩ n).1 (hΩ n).2.1 (hΩ n).2.2.2 hsS
      obtain ⟨hAm', hAS', hAt'⟩ :=
        translate_props hS' (hΩ' n).1 (hΩ' n).2.1 (hΩ' n).2.2.2 hsS'
      have happrox := hn₀ _ _ hAm hAS hAt hAm' hAS' hAt' (fun k hk => hs2.2 k hk)
        (fun k hk => hs2'.2 k hk)
      rw [hsA_Xop_translate hσ hS hS' hW hW' (hΩ n).1 (hΩ n).2.1
        (hΩ n).2.2.2 (hΩ' n).1 (hΩ' n).2.1 (hΩ' n).2.2.2 hsS hsS' γ]
      exact ENNReal.ofReal_le_ofReal (sq_max_le_hilbertSchmidtSq_lemma_2 _ _ happrox)

end Formalism.L2.S.Pv.EnergyAbs
end
end

section
noncomputable section

open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

theorem energyAbs_holds : EnergyAbs := by
  intro G _ _ _ _ _ _ _ _ μ _ _ HH _ _ _ σ d w V V' _ _ _ _ _ _ S S' μS μS' ν ν' τ τ' W W' C _ m h
    hσ hSch hw hS hS' hF hF' hν hν' hq hq' hW hW' hD hhm hOOi hB hC hC'
  haveI := hν
  haveI := hν'
  haveI : SigmaFinite μS := hS.2.2.2.2.1
  haveI : SigmaFinite μS' := hS'.2.2.2.2.1
  obtain ⟨Ω, hΩ, hΩF⟩ := folner_seq hS hF
  obtain ⟨Ω', hΩ', hΩF'⟩ := folner_seq hS' hF'
  have hlim := folner_limit hσ hSch hw hS hν hq hW hC Ω hΩ hΩF
  have hlim' := folner_limit hσ hSch hw hS' hν' hq' hW' hC' Ω' hΩ' hΩF'
  have hd : 0 < d := hSch.1
  set φn : ℕ → G → ℝ≥0∞ := fun n g => ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) g))
    with hφn
  have hφm : ∀ n, Measurable (φn n) := fun n =>
    ENNReal.measurable_ofReal.comp (continuous_hsA_Xop hσ μS ν μS' ν' d w W W' (Ω n) (Ω' n)).measurable
  set Fn : ℕ → C → ℝ≥0∞ := fun n c => (μS (Ω n) * μS' (Ω' n))⁻¹ *
    ∫⁻ s, ∫⁻ s', φn n (s * h c * s'⁻¹) ∂μS' ∂μS with hFn
  have hpt : ∀ c, ENNReal.ofReal (hsA (∫ x, rk1A (W x) (W' ((h c)⁻¹ * x)) ∂μ)) ≤ liminf (fun n => Fn n c) atTop :=
    fun c => point_lower hσ hS hS' hq hq' hW hW' Ω Ω' hΩ hΩ' hΩF hΩF'
      (fun n => continuous_hsA_Xop hσ μS ν μS' ν' d w W W' (Ω n) (Ω' n)) (h c) (hB c)
  have hinner : ∀ n, Measurable (fun c => ∫⁻ s, ∫⁻ s', φn n (s * h c * s'⁻¹) ∂μS' ∂μS) := by
    intro n
    have h3 : Measurable (fun r : (C × G) × G => φn n (r.1.2 * h r.1.1 * r.2⁻¹)) :=
      (hφm n).comp (((measurable_snd.comp measurable_fst).mul (hhm.comp (measurable_fst.comp measurable_fst))).mul
        measurable_snd.inv)
    exact h3.lintegral_prod_right'.lintegral_prod_right'
  have hmeasF : ∀ n, Measurable (Fn n) := fun n => (hinner n).const_mul _
  have hint : ∀ n, ∫⁻ c, Fn n c ∂m = (μS (Ω n) * μS' (Ω' n))⁻¹ *
      ENNReal.ofReal (d * (∑ i, ‖yv μS ν σ w W (Ω n) (stdOrthonormalBasis ℂ V i)‖ ^ 2) *
        (∑ j, ‖yv μS' ν' σ w W' (Ω' n) (stdOrthonormalBasis ℂ V' j)‖ ^ 2)) := by
    intro n
    rw [lintegral_const_mul _ (hinner n), ← hD (φn n) (hφm n), lintegral_hsA_Xop hSch]
  have htend := tendsto_energy hd (fun n => ⟨(hΩ n).2.2.1, (hΩ n).2.2.2⟩)
    (fun n => ⟨(hΩ' n).2.2.1, (hΩ' n).2.2.2⟩) hlim hlim'
  calc ∫⁻ c, ENNReal.ofReal (hsA (∫ x, rk1A (W x) (W' ((h c)⁻¹ * x)) ∂μ)) ∂m
      ≤ ∫⁻ c, liminf (fun n => Fn n c) atTop ∂m := lintegral_mono hpt
    _ ≤ liminf (fun n => ∫⁻ c, Fn n c ∂m) atTop := lintegral_liminf_le hmeasF
    _ = ENNReal.ofReal (1 / d) := by
        simp only [hint]
        exact htend.liminf_eq

end Formalism.L2.S.Pv.EnergyAbs
end
end
