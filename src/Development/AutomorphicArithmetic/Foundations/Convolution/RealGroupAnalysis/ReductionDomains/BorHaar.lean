import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.BorHomeo

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem lintegral_mul_left_adele {F : Type} [Field F] [NumberField F] (c : (A F)ˣ) (g : A F → ℝ≥0∞) :
    ∫⁻ s, g ((c : A F) * s) ∂(adeleMeasure F) = ENNReal.ofReal (ab c)⁻¹ * ∫⁻ s, g s ∂(adeleMeasure F) := by
  have he : MeasurableEmbedding (fun x : A F => c • x) := (Homeomorph.smul c).measurableEmbedding
  have h1 : ∫⁻ s, g ((c : A F) * s) ∂(adeleMeasure F) =
      ∫⁻ s, g s ∂((adeleMeasure F).map (fun x : A F => c • x)) :=
    (he.lintegral_map g).symm
  rw [h1, map_smul_adeleMeasure, lintegral_smul_measure]
  rfl

private theorem wt_mul {F : Type} [Field F] [NumberField F] (s t : (A F)ˣ) : M.wt (s * t) = M.wt s * M.wt t := by
  have hs : 0 ≤ ((ab s)⁻¹ ^ 2 : ℝ) := by positivity
  simp only [M.wt]
  rw [← ENNReal.ofReal_mul hs, M.ab_mul, mul_inv, mul_pow]

theorem UpperTheory.ConvolutionTheory.R2.M.borLeft :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (f : G1 F → ℝ≥0∞), Measurable f → ∀ (b₀ : A F) (a₀ : (A F)ˣ), ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b₀ * mD a₀ * (nU b * mD a)) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F) = ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b * mD a) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F) := by
  intro F _ _ f _ b₀ a₀
  have key : ∀ (a : (A F)ˣ) (b : A F), nU b₀ * mD a₀ * (nU b * mD a) =
      nU (b₀ + ((a₀ * a₀ : (A F)ˣ) : A F) * b) * mD (a₀ * a) := by
    intro a b
    rw [M.nU_add, M.mD_mul, mul_assoc (nU b₀), ← mul_assoc (mD a₀), M.mD_mul_nU]
    simp [pow_two, mul_assoc]
  have hc : ENNReal.ofReal (ab (a₀ * a₀))⁻¹ = M.wt a₀ := by
    simp only [M.wt]
    rw [M.ab_mul, mul_inv, pow_two]
  have inner : ∀ a : IdeleGroup F,
      ∫⁻ b, f (nU b₀ * mD a₀ * (nU b * mD a)) * M.wt a ∂(adeleMeasure F) =
        ∫⁻ b, f (nU b * mD (a₀ * a)) * M.wt (a₀ * a) ∂(adeleMeasure F) := by
    intro a
    have hwa : M.wt a ≠ ∞ := ENNReal.ofReal_ne_top
    have hwb : M.wt (a₀ * a) ≠ ∞ := ENNReal.ofReal_ne_top
    simp only [key]
    rw [lintegral_mul_const' _ _ hwa, lintegral_mul_const' _ _ hwb,
      lintegral_mul_left_adele (a₀ * a₀) (fun s => f (nU (b₀ + s) * mD (a₀ * a))),
      lintegral_add_left_eq_self (fun s => f (nU s * mD (a₀ * a))) b₀, hc, wt_mul]
    ring
  simp only [inner]
  exact lintegral_mul_left_eq_self
    (fun x : IdeleGroup F => ∫⁻ b, f (nU b * mD x) * M.wt x ∂(adeleMeasure F)) a₀
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.borHaar :
    ∀ (F : Type) [Field F] [NumberField F], ∃ μS : Measure (M.Bor F), μS.IsHaarMeasure ∧ ∀ (f : G1 F → ℝ≥0∞), Measurable f → ∫⁻ s, f s ∂μS = ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b * mD a) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F) := by
  intro F _ _
  obtain ⟨hcl, e, he⟩ := M.borHomeo F
  have hcont : Continuous fun a : IdeleGroup F => (ab a)⁻¹ ^ 2 :=
    (M.continuous_ab.inv₀ fun a => (M.ab_pos a).ne').pow 2
  have hwm : Measurable (M.wt : IdeleGroup F → ℝ≥0∞) := M.measurable_wt
  have hw0 : ∀ a : IdeleGroup F, M.wt a ≠ 0 := fun a => by
    have : 0 < (ab a)⁻¹ ^ 2 := pow_pos (inv_pos.2 (M.ab_pos a)) 2
    exact (ENNReal.ofReal_pos.2 this).ne'
  set ν : Measure (IdeleGroup F) := (ideleMeasure F).withDensity M.wt with hν
  haveI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hcont
  haveI : ν.IsOpenPosMeasure :=
    (withDensity_absolutelyContinuous' hwm.aemeasurable (ae_of_all _ hw0)).isOpenPosMeasure
  haveI : SFinite ν := by rw [hν]; infer_instance
  set ρ : Measure (IdeleGroup F × A F) := ν.prod (adeleMeasure F) with hρ
  have hint : ∀ f : G1 F → ℝ≥0∞, Measurable f → ∫⁻ s, f s ∂(ρ.map e) =
      ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b * mD a) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F) := by
    intro f hf
    have hc : Continuous fun p : IdeleGroup F × A F => nU p.2 * mD p.1 :=
      (M.continuous_nU.comp continuous_snd).mul (M.continuous_mD.comp continuous_fst)
    have hfm : Measurable fun p : IdeleGroup F × A F => f (nU p.2 * mD p.1) := hf.comp hc.measurable
    rw [show ∫⁻ s, f s ∂(ρ.map e) = ∫⁻ p, f (e p) ∂ρ from
      lintegral_map (f := fun s : M.Bor F => f s) (hf.comp measurable_subtype_coe) e.continuous.measurable]
    simp only [he]
    rw [hρ, lintegral_prod _ hfm.aemeasurable, hν,
      lintegral_withDensity_eq_lintegral_mul _ hwm hfm.lintegral_prod_right']
    refine lintegral_congr fun a => ?_
    have hne : M.wt a ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [Pi.mul_apply, lintegral_mul_const' _ _ hne, mul_comm]
  refine ⟨ρ.map e, ?_, hint⟩
  haveI : IsFiniteMeasureOnCompacts (ρ.map e) := ⟨fun K hK => by
    rw [e.measurableEmbedding.map_apply]
    exact ((e.isCompact_preimage).2 hK).measure_lt_top⟩
  haveI : (ρ.map e).IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  haveI : (ρ.map e).IsMulLeftInvariant := ⟨fun g => by
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs]
    have hS : MeasurableSet (Subtype.val '' s : Set (G1 F)) := hcl.measurableSet.subtype_image hs
    set f : G1 F → ℝ≥0∞ := (Subtype.val '' s : Set (G1 F)).indicator 1 with hfdef
    have hf : Measurable f := measurable_one.indicator hS
    have hval : ∀ x : M.Bor F, f x = s.indicator 1 x := fun x => by
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx, hfdef, Set.indicator_of_mem (Set.mem_image_of_mem _ hx)]; rfl
      · rw [Set.indicator_of_notMem hx, hfdef, Set.indicator_of_notMem]
        rintro ⟨y, hy, hyx⟩
        exact hx (Subtype.ext hyx ▸ hy)
    have h1 : (ρ.map e) s = ∫⁻ x, f x ∂(ρ.map e) := by
      simp only [hval]; rw [lintegral_indicator_one hs]
    have h2 : (ρ.map e) ((fun x => g * x) ⁻¹' s) = ∫⁻ x, (fun y => f (g.1 * y)) x ∂(ρ.map e) := by
      have hs' : MeasurableSet ((fun x => g * x) ⁻¹' s) := measurable_const_mul g hs
      rw [← lintegral_indicator_one hs']
      refine lintegral_congr fun x => ?_
      have := hval (g * x)
      simpa [Set.indicator] using this.symm
    obtain ⟨p, rfl⟩ := e.surjective g
    rw [h1, h2, hint (fun y => f ((e p : G1 F) * y)) (hf.comp (measurable_const_mul _)), hint f hf]
    simp only [he]
    exact M.borLeft F f hf p.2 p.1⟩
  exact {}
end
