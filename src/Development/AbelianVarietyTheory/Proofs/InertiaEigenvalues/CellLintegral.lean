import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUniformizerTorusTranslateUnipotentQuoti
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tl_inv_mul_mem_C0_off_finset : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) →
    ∀ g : GA E n, ∃ l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ), (∀ v ∈ S, l v = 0) ∧
      (GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S := by
  first | exact @GlobalTheory.CellDec.adelic_iwasawa_decomposition_off_finset | exact GlobalTheory.CellDec.adelic_iwasawa_decomposition_off_finset | (intros; apply GlobalTheory.CellDec.adelic_iwasawa_decomposition_off_finset <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_iwasawa_cells_disjoint_off_finset : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) →
    ∀ (l l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n), (∀ v ∈ S, l v = 0) → (∀ v ∈ S, l' v = 0) →
      (GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → (GlobalTheory.CellDec.tl n ϖ l')⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → l = l' := by
  first | exact @GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 | exact GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 | (intros; apply GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_C0 : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    IsOpen (GlobalTheory.CellDec.C0 E n S) := by
  first | exact @GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet | exact GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet | (intros; apply GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet <;> assumption)
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.UnfoldCplx

variable {α ι : Type} [MeasurableSpace α] [Countable ι]

theorem integrable_comp {μ : Measure α} {𝓕 A : Set α} {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {T : ι → α → α} (hT : ∀ i, Measurable (T i)) {H : Set (α → α)}
    (hU : ∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ)
    {B : α → ℂ} (hB : Measurable B) (hBi : Integrable B (μ.restrict 𝓕))
    (hH : ∀ h ∈ H, ∀ x, B (h x) = B x) (i : ι) :
    Integrable (fun x => B (T i x)) (μ.restrict A) := by
  refine ⟨(hB.comp (hT i)).aestronglyMeasurable, ?_⟩
  have h1 := hU (fun x => ‖B x‖ₑ) hB.enorm (fun h hh x => by simp [hH h hh x])
  have hfin : ∫⁻ x in 𝓕, ‖B x‖ₑ ∂μ < ∞ := hBi.2
  have hle : ENNReal.ofReal (c i) * ∫⁻ x in A, ‖B (T i x)‖ₑ ∂μ ≤ ∫⁻ x in 𝓕, ‖B x‖ₑ ∂μ := by
    rw [h1]; exact ENNReal.le_tsum (f := fun i => ENNReal.ofReal (c i) * ∫⁻ x in A, ‖B (T i x)‖ₑ ∂μ) i
  have hne : ENNReal.ofReal (c i) ≠ 0 := by simpa using hc i
  show ∫⁻ x in A, ‖B (T i x)‖ₑ ∂μ < ∞
  by_contra hh
  rw [not_lt, top_le_iff] at hh
  rw [hh, ENNReal.mul_top hne] at hle
  exact absurd (lt_of_le_of_lt hle hfin) (lt_irrefl _)

theorem hasSum_nonneg {μ : Measure α} {𝓕 A : Set α} {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {T : ι → α → α} (hT : ∀ i, Measurable (T i)) {H : Set (α → α)}
    (hU : ∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ)
    {g : α → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g (μ.restrict 𝓕))
    (hH : ∀ h ∈ H, ∀ x, g (h x) = g x) :
    HasSum (fun i => c i * ∫ x in A, g (T i x) ∂μ) (∫ x in 𝓕, g x ∂μ) := by
  have h1 := hU (fun x => ENNReal.ofReal (g x)) hg.ennreal_ofReal (fun h hh x => by simp [hH h hh x])
  have hfin : ∫⁻ x in 𝓕, ENNReal.ofReal (g x) ∂μ ≠ ∞ := (hgi.lintegral_lt_top).ne
  set F : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (c i) * ∫⁻ x in A, ENNReal.ofReal (g (T i x)) ∂μ with hF
  have hsum : ∑' i, F i ≠ ∞ := by rw [← h1]; exact hfin
  have hFi : ∀ i, F i ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hsum
  have key := ENNReal.hasSum_toReal hsum
  rw [← ENNReal.tsum_toReal_eq hFi, ← h1, ← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hg0) hg.aestronglyMeasurable] at key
  convert key using 1
  funext i
  simp only [hF, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hc i).le]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => hg0 _))
    (hg.comp (hT i)).aestronglyMeasurable]

theorem hasSum_real {μ : Measure α} {𝓕 A : Set α} {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {T : ι → α → α} (hT : ∀ i, Measurable (T i)) {H : Set (α → α)}
    (hU : ∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ)
    {g : α → ℝ} (hg : Measurable g) (hgi : Integrable g (μ.restrict 𝓕))
    (hgA : ∀ i, Integrable (fun x => g (T i x)) (μ.restrict A))
    (hH : ∀ h ∈ H, ∀ x, g (h x) = g x) :
    HasSum (fun i => c i * ∫ x in A, g (T i x) ∂μ) (∫ x in 𝓕, g x ∂μ) := by
  have hp := hasSum_nonneg hc hT hU (g := fun x => max (g x) 0) (hg.max measurable_const)
    (fun x => le_max_right _ _) hgi.pos_part (fun h hh x => by simp only [hH h hh x])
  have hn := hasSum_nonneg hc hT hU (g := fun x => max (-g x) 0) (hg.neg.max measurable_const)
    (fun x => le_max_right _ _) hgi.neg_part (fun h hh x => by simp only [hH h hh x])
  have hsplit : ∀ y : ℝ, max y 0 - max (-y) 0 = y := fun y => by
    rcases le_total y 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
  have e1 : ∫ x in 𝓕, g x ∂μ = (∫ x in 𝓕, max (g x) 0 ∂μ) - ∫ x in 𝓕, max (-g x) 0 ∂μ := by
    rw [← integral_sub hgi.pos_part hgi.neg_part]; simp only [hsplit]
  have hf : (fun i => c i * ∫ x in A, g (T i x) ∂μ) = fun i =>
      c i * (∫ x in A, max (g (T i x)) 0 ∂μ) - c i * ∫ x in A, max (-g (T i x)) 0 ∂μ := by
    funext i
    rw [← mul_sub, ← integral_sub (hgA i).pos_part (hgA i).neg_part]; simp only [hsplit]
  rw [e1, hf]
  exact hp.sub hn

theorem hasSum_complex : ∀ {α ι : Type} [MeasurableSpace α] [Countable ι] (μ : Measure α) (𝓕 A : Set α) (c : ι → ℝ), (∀ i, 0 < c i) →
    ∀ (T : ι → α → α), (∀ i, Measurable (T i)) → ∀ (H : Set (α → α)),
    (∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ) →
    ∀ B : α → ℂ, Measurable B → Integrable B (μ.restrict 𝓕) → (∀ h ∈ H, ∀ x, B (h x) = B x) →
      (∀ i, Integrable (fun x => B (T i x)) (μ.restrict A)) ∧
        HasSum (fun i => (c i : ℂ) * ∫ x in A, B (T i x) ∂μ) (∫ x in 𝓕, B x ∂μ) := by
  intro α ι _ _ μ 𝓕 A c hc T hT H hU B hB hBi hH
  have hBA := integrable_comp hc hT hU hB hBi hH
  refine ⟨hBA, ?_⟩
  rw [Complex.hasSum_iff]
  constructor
  · have := hasSum_real hc hT hU (g := fun x => (B x).re) (Complex.measurable_re.comp hB) hBi.re
      (fun i => (hBA i).re) (fun h hh x => by simp only [hH h hh x])
    have e2 : ∫ x in 𝓕, (B x).re ∂μ = (∫ x in 𝓕, B x ∂μ).re := integral_re hBi
    have hf : (fun i => c i * ∫ x in A, (B (T i x)).re ∂μ) =
        fun i => ((c i : ℂ) * ∫ x in A, B (T i x) ∂μ).re := by
      funext i
      rw [Complex.re_ofReal_mul]; congr 1; exact integral_re (hBA i)
    rw [e2, hf] at this
    exact this
  · have := hasSum_real hc hT hU (g := fun x => (B x).im) (Complex.measurable_im.comp hB) hBi.im
      (fun i => (hBA i).im) (fun h hh x => by simp only [hH h hh x])
    have e2 : ∫ x in 𝓕, (B x).im ∂μ = (∫ x in 𝓕, B x ∂μ).im := integral_im hBi
    have hf : (fun i => c i * ∫ x in A, (B (T i x)).im ∂μ) =
        fun i => ((c i : ℂ) * ∫ x in A, B (T i x) ∂μ).im := by
      funext i
      rw [Complex.im_ofReal_mul]; congr 1; exact integral_im (hBA i)
    rw [e2, hf] at this
    exact this

end GlobalTheory.UnfoldCplx
end

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_unfolding_of_complex_invariant_integrable : ∀ {α ι : Type} [MeasurableSpace α] [Countable ι] (μ : Measure α) (𝓕 A : Set α) (c : ι → ℝ), (∀ i, 0 < c i) →
    ∀ (T : ι → α → α), (∀ i, Measurable (T i)) → ∀ (H : Set (α → α)),
    (∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ) →
    ∀ B : α → ℂ, Measurable B → Integrable B (μ.restrict 𝓕) → (∀ h ∈ H, ∀ x, B (h x) = B x) →
      (∀ i, Integrable (fun x => B (T i x)) (μ.restrict A)) ∧
        HasSum (fun i => (c i : ℂ) * ∫ x in A, B (T i x) ∂μ) (∫ x in 𝓕, B x ∂μ) := by
  atlas_forward_decl GlobalTheory.UnfoldCplx.hasSum_complex
end

section
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem cell_lintegral [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] (μ : Measure (GA E n)) [μ.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (𝓕 : Set (GA E n)) (h𝓕 : IsFundamentalDomain (NE E n) 𝓕 μ)
    (B : GA E n → ℝ≥0∞) (hB : Measurable B) (hinv : ∀ u ∈ NA E n, ∀ g, B (u * g) = B g) :
    ∫⁻ g in 𝓕, B g ∂μ =
      ∑' l : abelian₂ E n S, ENNReal.ofReal (dinv n l.1) * ∫⁻ g in 𝓕 ∩ C0 E n S, B (tl n ϖ l.1 * g) ∂μ := by
  have hC : MeasurableSet (C0 E n S) := (GlobalTheory.T.isOpen_C0 E n S).measurableSet
  let cellS : abelian₂ E n S → Set (GA E n) := fun l => {g | (tl n ϖ l.1)⁻¹ * g ∈ C0 E n S}
  have hmeas : ∀ l, MeasurableSet (cellS l) := fun l =>
    ((GlobalTheory.T.isOpen_C0 E n S).preimage (continuous_const.mul continuous_id)).measurableSet
  have hpart : ∀ g, ∑' l : abelian₂ E n S, (cellS l).indicator B g = B g := by
    intro g
    obtain ⟨l0, hl0S, hl0⟩ := GlobalTheory.T.exists_tl_inv_mul_mem_C0_off_finset E n S ϖ hϖ g
    have hz : ∀ l : abelian₂ E n S, l ≠ (⟨l0, hl0S⟩ : abelian₂ E n S) → (cellS l).indicator B g = 0 := fun l hl =>
      Set.indicator_of_notMem (show g ∉ cellS l from fun hg => hl (Subtype.ext (GlobalTheory.T.adelic_iwasawa_cells_disjoint_off_finset E n S ϖ hϖ l.1 l0 g l.2 hl0S hg hl0))) B
    rw [tsum_eq_single _ hz]
    exact Set.indicator_of_mem (show g ∈ cellS ⟨l0, hl0S⟩ from hl0) _
  calc ∫⁻ g in 𝓕, B g ∂μ = ∫⁻ g in 𝓕, ∑' l, (cellS l).indicator B g ∂μ := by simp_rw [hpart]
    _ = ∑' l, ∫⁻ g in 𝓕, (cellS l).indicator B g ∂μ :=
        lintegral_tsum fun l => (hB.indicator (hmeas l)).aemeasurable
    _ = _ := tsum_congr fun l => ?_
  let t := tl n ϖ l.1
  let F : GA E n → ℝ≥0∞ := (C0 E n S).indicator fun h => B (t * h)
  have e : (cellS l).indicator B = fun g => F (t⁻¹ * g) := by
    funext g
    show (cellS l).indicator B g = (C0 E n S).indicator (fun h => B (t * h)) (t⁻¹ * g)
    by_cases hg : t⁻¹ * g ∈ C0 E n S
    · rw [Set.indicator_of_mem (show g ∈ cellS l from hg), Set.indicator_of_mem hg, mul_inv_cancel_left]
    · rw [Set.indicator_of_notMem (show g ∉ cellS l from hg), Set.indicator_of_notMem hg]
  have hF : Measurable F := (hB.comp (measurable_const_mul t)).indicator hC
  have hFinv : ∀ u ∈ NA E n, ∀ g, F (u * g) = F g := by
    intro u hu g
    show (C0 E n S).indicator (fun h => B (t * h)) (u * g) = (C0 E n S).indicator (fun h => B (t * h)) g
    by_cases hg : g ∈ C0 E n S
    · rw [Set.indicator_of_mem (adelicUnitriangular_mul_mem_unipotentTimesIntegral hu hg), Set.indicator_of_mem hg]
      change B (t * (u * g)) = B (t * g)
      rw [show t * (u * g) = (t * u * t⁻¹) * (t * g) by group]
      exact hinv _ (tl_conj_mem ϖ l.1 hu) _
    · have : u * g ∉ C0 E n S := fun h => hg (by simpa using adelicUnitriangular_mul_mem_unipotentTimesIntegral (inv_mem hu) h)
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hg]
  rw [e, GlobalTheory.T.lintegral_uniformizerTorus_translate_unipotentQuotient E n μ ϖ hϖ l.1 𝓕 h𝓕 F hF hFinv]
  congr 1
  rw [lintegral_indicator hC, Measure.restrict_restrict hC, Set.inter_comm]

theorem cell_integral [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] (μ : Measure (GA E n)) [μ.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (𝓕 : Set (GA E n)) (h𝓕 : IsFundamentalDomain (NE E n) 𝓕 μ)
    (B : GA E n → ℂ) (hB : Measurable B) (hBi : Integrable B (μ.restrict 𝓕))
    (hinv : ∀ u ∈ NA E n, ∀ g, B (u * g) = B g) :
    (∀ l : abelian₂ E n S, Integrable (fun g => B (tl n ϖ l.1 * g)) (μ.restrict (𝓕 ∩ C0 E n S))) ∧
      HasSum (fun l : abelian₂ E n S => (dinv n l.1 : ℂ) * ∫ g in 𝓕 ∩ C0 E n S, B (tl n ϖ l.1 * g) ∂μ)
        (∫ g in 𝓕, B g ∂μ) := by
  have hpos : ∀ l : abelian₂ E n S, 0 < dinv n l.1 := fun l =>
    Finset.prod_pos fun v _ => zpow_pos (by exact_mod_cast (GlobalTheory.LFun.qV_ne_zero v).bot_lt) _
  exact GlobalTheory.T.hasSum_unfolding_of_complex_invariant_integrable μ 𝓕 (𝓕 ∩ C0 E n S) (fun l : abelian₂ E n S => dinv n l.1) hpos (fun l g => tl n ϖ l.1 * g)
    (fun l => measurable_const_mul _) ((fun u : GA E n => fun g => u * g) '' (NA E n : Set (GA E n)))
    (fun f hf hfi => cell_lintegral μ S ϖ hϖ 𝓕 h𝓕 f hf fun u hu g => hfi _ ⟨u, hu, rfl⟩ g)
    B hB hBi (by rintro _ ⟨u, hu, rfl⟩ x; exact hinv u hu x)

end GlobalTheory.CellDec
end
end
