import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces
import GroundTheory.AutomorphicForms.TraceFormulaConvolution
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Unimodular

section
open MeasureTheory Set Filter Topology Function
open scoped ENNReal Pointwise InnerProductSpace ComplexConjugate

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

section HilbertSchmidt

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isHilbertSchmidt_of_ae_eq_dual (T : H →L[ℂ] Lp ℂ 2 ν) (e : X → StrongDual ℂ H) (B : ℝ)
    (hB : ∀ x, ‖e x‖ ≤ B) (hT : ∀ v, T v =ᵐ[ν] fun x => e x v) : IsHilbertSchmidt T := by
  set b := stdHilbertBasis ℂ H
  have hpt : ∀ x, ∑' i, ‖e x (b i)‖ₑ ^ 2 ≤ ENNReal.ofReal B ^ 2 := by
    intro x
    set k := (InnerProductSpace.toDual ℂ H).symm (e x)
    have hk : ∀ w, e x w = ⟪k, w⟫_ℂ := fun w => (InnerProductSpace.toDual_symm_apply).symm
    have hkn : ‖k‖ = ‖e x‖ := LinearIsometryEquiv.norm_map _ _
    calc ∑' i, ‖e x (b i)‖ₑ ^ 2 = ∑' i, ‖⟪b i, k⟫_ℂ‖ₑ ^ 2 := by
          congr 1; ext i; rw [hk, enorm_inner_comm]
      _ = ‖k‖ₑ ^ 2 := (enorm_sq_eq_tsum b k).symm
      _ ≤ ENNReal.ofReal B ^ 2 := by
          gcongr
          rw [← ofReal_norm, hkn]
          exact ENNReal.ofReal_le_ofReal (hB x)
  have hmeas : ∀ i, AEMeasurable (fun x => ‖e x (b i)‖ₑ ^ 2) ν := fun i =>
    ((Lp.aestronglyMeasurable (T (b i))).enorm.pow_const 2).congr
      ((hT (b i)).mono fun x hx => by simp only [hx])
  unfold IsHilbertSchmidt
  calc hsNormSq T = ∑' i, ‖T (b i)‖ₑ ^ 2 := rfl
    _ = ∑' i, ∫⁻ x, ‖e x (b i)‖ₑ ^ 2 ∂ν := by
        congr 1; ext i
        rw [Lp.enorm_def, L2Kernel.eLpNorm_two_sq]
        exact lintegral_congr_ae ((hT (b i)).mono fun x hx => by simp only [hx])
    _ ≤ ∫⁻ x, ∑' i, ‖e x (b i)‖ₑ ^ 2 ∂ν := by
        rw [ENNReal.tsum_eq_iSup_sum]
        refine iSup_le fun F => ?_
        rw [← lintegral_finsetSum' F fun i _ => hmeas i]
        exact lintegral_mono fun x => ENNReal.sum_le_tsum F
    _ ≤ ∫⁻ _, ENNReal.ofReal B ^ 2 ∂ν := lintegral_mono hpt
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top (by simp) (measure_lt_top ν univ)

end HilbertSchmidt

theorem norm_le_of_enorm_sq_le {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    {z : E} {v : F} {A : ℝ≥0∞} (hA : A ≠ ⊤) (h : ‖z‖ₑ ^ 2 ≤ A * ‖v‖ₑ ^ 2) :
    ‖z‖ ≤ √A.toReal * ‖v‖ := by
  have h' : ‖z‖ ^ 2 ≤ A.toReal * ‖v‖ ^ 2 := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top hA (by simp)) h
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm] using this
  rw [← Real.sqrt_sq (norm_nonneg z), ← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul
    ENNReal.toReal_nonneg]
  exact Real.sqrt_le_sqrt h'

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ]

omit [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in

theorem exists_encard_le_of_isCompact {C : Set G} (hC : IsCompact C) :
    ∃ N : ℕ, ∀ g : G, {γ : Γ | γ • g ∈ C}.encard ≤ N := by
  have hfin := finite_setOf_mem_of_isCompact Γ (hC.mul hC.inv)
  refine ⟨hfin.toFinset.card, fun g => ?_⟩
  rcases eq_empty_or_nonempty {γ : Γ | γ • g ∈ C} with h | ⟨γ₀, hγ₀⟩
  · rw [h, encard_empty]; simp
  have hsub : (fun γ : Γ => γ * γ₀⁻¹) '' {γ : Γ | γ • g ∈ C} ⊆ {δ : Γ | (δ : G) ∈ C * C⁻¹} := by
    rintro _ ⟨γ, hγ, rfl⟩
    refine ⟨γ • g, hγ, (γ₀ • g)⁻¹, Set.inv_mem_inv.2 hγ₀, ?_⟩
    simp only [Subgroup.smul_def, smul_eq_mul, mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  calc {γ : Γ | γ • g ∈ C}.encard
      = ((fun γ : Γ => γ * γ₀⁻¹) '' {γ : Γ | γ • g ∈ C}).encard :=
        ((mul_left_injective γ₀⁻¹).injOn).encard_image.symm
    _ ≤ {δ : Γ | (δ : G) ∈ C * C⁻¹}.encard := encard_le_encard hsub
    _ = hfin.toFinset.card := hfin.encard_eq_coe_toFinset_card

variable (μ : Measure G) [μ.IsMulLeftInvariant]

theorem lintegral_indicator_le {E : Set G} (hE : MeasurableSet E) {N : ℕ}
    (hN : ∀ g : G, {γ : Γ | γ • g ∈ E}.encard ≤ N) {h : RightCosetSpace Γ → ℝ≥0∞}
    (hh : Measurable h) :
    ∫⁻ g in E, h (mk Γ g) ∂μ ≤ N * ∫⁻ x, h x ∂quotientMeasure Γ μ := by
  rw [← lintegral_indicator hE, lintegral_eq_lintegral_automorphize (Γ := Γ) μ
    (f := E.indicator fun g => h (mk Γ g)) ((hh.comp (measurable_mk Γ)).indicator hE).aemeasurable,
    ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)]
  refine lintegral_mono fun x => ?_
  obtain ⟨g, rfl⟩ := mk_surjective Γ x
  change ∑' γ : Γ, E.indicator (fun g => h (mk Γ g)) (γ • g) ≤ N * h (mk Γ g)
  have hrw : ∀ γ : Γ, E.indicator (fun g => h (mk Γ g)) (γ • g) =
      {γ : Γ | γ • g ∈ E}.indicator (fun _ => h (mk Γ g)) γ := by
    intro γ
    by_cases hγ : γ • g ∈ E
    · rw [indicator_of_mem hγ, indicator_of_mem (show γ ∈ {γ : Γ | γ • g ∈ E} from hγ), mk_smul]
    · rw [indicator_of_notMem hγ, indicator_of_notMem (show γ ∉ {γ : Γ | γ • g ∈ E} from hγ)]
  simp_rw [hrw]
  rw [← tsum_subtype, ENNReal.tsum_set_const]
  gcongr
  have := hN g
  exact_mod_cast this

theorem quasiMeasurePreserving_mk :
    Measure.QuasiMeasurePreserving (mk Γ) μ (quotientMeasure Γ μ) := by
  refine ⟨measurable_mk Γ, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply (measurable_mk Γ) hs]
  have hs' : MeasurableSet (mk Γ ⁻¹' s) := hs.preimage (measurable_mk Γ)
  rw [← lintegral_indicator_one hs', lintegral_eq_lintegral_automorphize (Γ := Γ) μ
    (f := (mk Γ ⁻¹' s).indicator 1) (measurable_one.indicator hs').aemeasurable]
  refine nonpos_iff_eq_zero.1 ?_
  calc ∫⁻ x, MulAction.automorphize ((mk Γ ⁻¹' s).indicator 1) x ∂quotientMeasure Γ μ
      ≤ ∫⁻ x, s.indicator (fun _ => ⊤) x ∂quotientMeasure Γ μ := by
        refine lintegral_mono fun x => ?_
        obtain ⟨g, rfl⟩ := mk_surjective Γ x
        by_cases hx : mk Γ g ∈ s
        · rw [indicator_of_mem hx]; exact le_top
        · change ∑' γ : Γ, (mk Γ ⁻¹' s).indicator 1 (γ • g) ≤ _
          have : ∀ γ : Γ, (mk Γ ⁻¹' s).indicator (1 : G → ℝ≥0∞) (γ • g) = 0 := fun γ =>
            indicator_of_notMem (by simpa [mk_smul] using hx) _
          simp [this]
    _ = 0 := by rw [lintegral_indicator_const hs, h0, mul_zero]

theorem stronglyMeasurable_lift (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    StronglyMeasurable fun g => φ (mk Γ g) :=
  (Lp.stronglyMeasurable φ).comp_measurable (measurable_mk Γ)

theorem lintegral_lift_sq_le (φ : Lp ℂ 2 (quotientMeasure Γ μ)) {E : Set G} (hE : MeasurableSet E)
    {N : ℕ} (hN : ∀ g : G, {γ : Γ | γ • g ∈ E}.encard ≤ N) :
    ∫⁻ g in E, ‖φ (mk Γ g)‖ₑ ^ 2 ∂μ ≤ N * ‖φ‖ₑ ^ 2 := by
  rw [Lp.enorm_def, L2Kernel.eLpNorm_two_sq]
  exact lintegral_indicator_le Γ μ hE hN
    ((Lp.stronglyMeasurable φ).measurable.enorm.pow_const 2)

theorem lintegral_lift_sq_lt_top (φ : Lp ℂ 2 (quotientMeasure Γ μ)) {C : Set G} (hC : IsCompact C) :
    ∫⁻ g in C, ‖φ (mk Γ g)‖ₑ ^ 2 ∂μ < ⊤ := by
  obtain ⟨N, hN⟩ := exists_encard_le_of_isCompact Γ hC
  refine (lintegral_lift_sq_le Γ μ φ hC.measurableSet hN).trans_lt ?_
  exact ENNReal.mul_lt_top (by simp) (ENNReal.pow_lt_top enorm_lt_top)

variable [IsFiniteMeasureOnCompacts μ]

theorem integrableOn_lift (φ : Lp ℂ 2 (quotientMeasure Γ μ)) {C : Set G} (hC : IsCompact C) :
    IntegrableOn (fun g => φ (mk Γ g)) C μ := by
  have hm : MemLp (fun g => φ (mk Γ g)) 2 (μ.restrict C) := by
    refine ⟨(stronglyMeasurable_lift Γ μ φ).aestronglyMeasurable, ?_⟩
    refine L2Kernel.lt_top_of_sq_lt_top ?_
    rw [L2Kernel.eLpNorm_two_sq]
    exact lintegral_lift_sq_lt_top Γ μ φ hC
  have : IsFiniteMeasure (μ.restrict C) := ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  exact hm.integrable one_le_two

def rconv (f : G → ℂ) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) (x : G) : ℂ :=
  ∫ y, f (x⁻¹ * y) * φ (mk Γ y) ∂μ

theorem integrable_rconv (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) (x : G) :
    Integrable (fun y => f (x⁻¹ * y) * φ (mk Γ y)) μ := by
  have hC : IsCompact ((x * ·) '' tsupport (f : G → ℂ)) :=
    f.hasCompactSupport.isCompact.image (continuous_const_mul x)
  have hzero : ∀ y ∉ (x * ·) '' tsupport (f : G → ℂ), f (x⁻¹ * y) * φ (mk Γ y) = 0 := by
    intro y hy
    have : x⁻¹ * y ∉ tsupport (f : G → ℂ) := fun h => hy ⟨x⁻¹ * y, h, by simp⟩
    simp [image_eq_zero_of_notMem_tsupport this]
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hzero
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  exact (integrableOn_lift Γ μ φ hC).bdd_mul
    (f.continuous.comp (continuous_const_mul x⁻¹)).aestronglyMeasurable
    (Eventually.of_forall fun y => hM _)

theorem rconv_mul_left (f : G → ℂ) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) {γ : G} (hγ : γ ∈ Γ)
    (x : G) : rconv Γ μ f φ (γ * x) = rconv Γ μ f φ x := by
  unfold rconv
  rw [← integral_mul_left_eq_self (fun y => f ((γ * x)⁻¹ * y) * φ (mk Γ y)) γ]
  congr 1
  ext y
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left, mk_mul_of_mem hγ]

theorem rconv_add (f : CompactlySupportedContinuousMap G ℂ) (φ ψ : Lp ℂ 2 (quotientMeasure Γ μ))
    (x : G) : rconv Γ μ f (φ + ψ) x = rconv Γ μ f φ x + rconv Γ μ f ψ x := by
  unfold rconv
  rw [← integral_add (integrable_rconv Γ μ f φ x) (integrable_rconv Γ μ f ψ x)]
  refine integral_congr_ae ?_
  filter_upwards [(quasiMeasurePreserving_mk Γ μ).ae_eq_comp (Lp.coeFn_add φ ψ)] with y hy
  simp only [comp_apply, Pi.add_apply] at hy
  rw [hy, mul_add]

theorem rconv_smul (f : CompactlySupportedContinuousMap G ℂ) (c : ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) (x : G) :
    rconv Γ μ f (c • φ) x = c * rconv Γ μ f φ x := by
  unfold rconv
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [(quasiMeasurePreserving_mk Γ μ).ae_eq_comp (Lp.coeFn_smul c φ)] with y hy
  simp only [comp_apply, Pi.smul_apply, smul_eq_mul] at hy
  rw [hy]
  ring

theorem enorm_rconv_sq_le (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) (x : G) {S : Set G} (hS : MeasurableSet S)
    (hfS : ∀ y ∉ S, f (x⁻¹ * y) = 0) {N : ℕ} (hN : ∀ g : G, {γ : Γ | γ • g ∈ S}.encard ≤ N) :
    ‖rconv Γ μ f φ x‖ₑ ^ 2 ≤ (∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) * (N * ‖φ‖ₑ ^ 2) := by
  have hm1 : AEMeasurable (fun y => ‖f (x⁻¹ * y)‖ₑ) μ :=
    (f.continuous.comp (continuous_const_mul x⁻¹)).measurable.enorm.aemeasurable
  have hm2 : AEMeasurable (S.indicator fun y => ‖φ (mk Γ y)‖ₑ) μ :=
    ((stronglyMeasurable_lift Γ μ φ).measurable.enorm.indicator hS).aemeasurable
  calc ‖rconv Γ μ f φ x‖ₑ ^ 2
      ≤ (∫⁻ y, ‖f (x⁻¹ * y)‖ₑ * S.indicator (fun y => ‖φ (mk Γ y)‖ₑ) y ∂μ) ^ 2 := by
        gcongr
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        congr 1
        ext y
        by_cases hy : y ∈ S
        · rw [indicator_of_mem hy, enorm_mul]
        · rw [indicator_of_notMem hy, hfS y hy]
          simp
    _ ≤ (∫⁻ y, ‖f (x⁻¹ * y)‖ₑ ^ 2 ∂μ) *
          ∫⁻ y, S.indicator (fun y => ‖φ (mk Γ y)‖ₑ) y ^ 2 ∂μ :=
        L2Kernel.lintegral_mul_sq_le μ hm1 hm2
    _ = (∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) * ∫⁻ y in S, ‖φ (mk Γ y)‖ₑ ^ 2 ∂μ := by
        congr 1
        · exact lintegral_mul_left_eq_self (fun y => ‖f y‖ₑ ^ 2) x⁻¹
        · rw [← lintegral_indicator hS]
          congr 1
          ext y
          by_cases hy : y ∈ S
          · simp [hy]
          · simp [hy]
    _ ≤ _ := by
        gcongr
        exact lintegral_lift_sq_le Γ μ φ hS hN

theorem exists_norm_rconv_le (f : CompactlySupportedContinuousMap G ℂ) (x : G) :
    ∃ C : ℝ, ∀ φ : Lp ℂ 2 (quotientMeasure Γ μ), ‖rconv Γ μ f φ x‖ ≤ C * ‖φ‖ := by
  have hC : IsCompact ((x * ·) '' tsupport (f : G → ℂ)) :=
    f.hasCompactSupport.isCompact.image (continuous_const_mul x)
  obtain ⟨N, hN⟩ := exists_encard_le_of_isCompact Γ hC
  have hf2 : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have := (f.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 2) f.hasCompactSupport).2
    rw [← L2Kernel.eLpNorm_two_sq]
    exact (ENNReal.pow_lt_top this).ne
  refine ⟨√((∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) * N).toReal, fun φ => ?_⟩
  refine norm_le_of_enorm_sq_le (ENNReal.mul_ne_top hf2 (by simp)) ?_
  rw [mul_assoc]
  refine enorm_rconv_sq_le Γ μ f φ x hC.measurableSet (fun y hy => ?_) hN
  have : x⁻¹ * y ∉ tsupport (f : G → ℂ) := fun h => hy ⟨x⁻¹ * y, h, by simp⟩
  exact image_eq_zero_of_notMem_tsupport this

def rconvCLM (f : CompactlySupportedContinuousMap G ℂ) (x : G) :
    StrongDual ℂ (Lp ℂ 2 (quotientMeasure Γ μ)) :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun φ => rconv Γ μ f φ x
      map_add' := fun φ ψ => rconv_add Γ μ f φ ψ x
      map_smul' := fun c φ => rconv_smul Γ μ f c φ x }
    (exists_norm_rconv_le Γ μ f x)

@[simp] theorem rconvCLM_apply (f : CompactlySupportedContinuousMap G ℂ) (x : G)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) : rconvCLM Γ μ f x φ = rconv Γ μ f φ x :=
  rfl

theorem continuous_rconv (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) : Continuous (rconv Γ μ f φ) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds x₀
  have hS : IsCompact (V * tsupport (f : G → ℂ)) := hVc.mul f.hasCompactSupport
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  refine continuousAt_of_dominated
    (bound := (V * tsupport (f : G → ℂ)).indicator fun y => M * ‖φ (mk Γ y)‖)
    (Eventually.of_forall fun x => (integrable_rconv Γ μ f φ x).aestronglyMeasurable) ?_ ?_ ?_
  · filter_upwards [hV] with x hx
    refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ V * tsupport (f : G → ℂ)
    · rw [indicator_of_mem hy, norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · have : x⁻¹ * y ∉ tsupport (f : G → ℂ) := fun h => hy ⟨x, hx, x⁻¹ * y, h, by simp⟩
      rw [indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport this, zero_mul, norm_zero]
  · exact (show IntegrableOn (fun y => M * ‖φ (mk Γ y)‖) (V * tsupport (f : G → ℂ)) μ from
      (integrableOn_lift Γ μ φ hS).norm.const_mul M).integrable_indicator hS.measurableSet
  · refine Eventually.of_forall fun y => ?_
    exact ((f.continuous.comp ((continuous_inv.comp continuous_id).mul continuous_const)).mul
      continuous_const).continuousAt

def rconvQ (f : CompactlySupportedContinuousMap G ℂ) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    RightCosetSpace Γ → ℂ :=
  Quotient.lift (rconv Γ μ f φ) fun a b hab => by
    obtain ⟨γ, rfl⟩ := hab
    exact rconv_mul_left Γ μ f φ γ.2 b

@[simp] theorem rconvQ_mk (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) (x : G) : rconvQ Γ μ f φ (mk Γ x) = rconv Γ μ f φ x :=
  rfl

theorem continuous_rconvQ (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) : Continuous (rconvQ Γ μ f φ) :=
  (isOpenQuotientMap_mk Γ).isQuotientMap.continuous_iff.2 (continuous_rconv Γ μ f φ)

section Operator

variable [μ.IsMulRightInvariant] [IsFiniteMeasure (quotientMeasure Γ μ)]

theorem integrable_prod_rightMul (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    Integrable (uncurry fun (g : G) (x : RightCosetSpace Γ) => f g * φ (rightMul Γ g x))
      (μ.prod (quotientMeasure Γ μ)) := by
  have hcont : Continuous fun p : G × RightCosetSpace Γ => rightMul Γ p.1 p.2 :=
    (continuous_rightMul_prod Γ).comp (continuous_snd.prodMk continuous_fst)
  have hmeas : StronglyMeasurable
      (uncurry fun (g : G) (x : RightCosetSpace Γ) => f g * φ (rightMul Γ g x)) :=
    (f.continuous.comp continuous_fst).stronglyMeasurable.mul
      ((Lp.stronglyMeasurable φ).comp_measurable hcont.measurable)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hφ1 : ∫⁻ x, ‖φ x‖ₑ ∂quotientMeasure Γ μ < ⊤ := ((Lp.memLp φ).integrable one_le_two).2
  have hf1 : ∫⁻ g, ‖f g‖ₑ ∂μ < ⊤ :=
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).2
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hmeas.aestronglyMeasurable.enorm]
  calc ∫⁻ g, ∫⁻ x, ‖uncurry (fun g x => f g * φ (rightMul Γ g x)) (g, x)‖ₑ ∂quotientMeasure Γ μ ∂μ
      = ∫⁻ g, ‖f g‖ₑ * ∫⁻ x, ‖φ x‖ₑ ∂quotientMeasure Γ μ ∂μ := by
        congr 1
        ext g
        simp only [uncurry_apply_pair, enorm_mul]
        rw [lintegral_const_mul' _ _ enorm_ne_top,
          (measurePreserving_rightMul μ g).lintegral_comp (Lp.stronglyMeasurable φ).measurable.enorm]
    _ = (∫⁻ g, ‖f g‖ₑ ∂μ) * ∫⁻ x, ‖φ x‖ₑ ∂quotientMeasure Γ μ := lintegral_mul_const' _ _ hφ1.ne
    _ < ⊤ := ENNReal.mul_lt_top hf1 hφ1

theorem rconvQ_eq_integral (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) (x : RightCosetSpace Γ) :
    rconvQ Γ μ f φ x = ∫ g, f g * φ (rightMul Γ g x) ∂μ := by
  obtain ⟨a, rfl⟩ := mk_surjective Γ x
  rw [rconvQ_mk, rconv, ← integral_mul_left_eq_self _ a]
  congr 1
  ext g
  rw [inv_mul_cancel_left, rightMul_mk]

theorem integrable_rconvQ (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) : Integrable (rconvQ Γ μ f φ) (quotientMeasure Γ μ) := by
  have := (integrable_prod_rightMul Γ μ f φ).integral_prod_right
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [uncurry_apply_pair]
  exact (rconvQ_eq_integral Γ μ f φ x).symm

theorem integrated_ae_eq_rconvQ (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f) φ : RightCosetSpace Γ → ℂ)
      =ᵐ[quotientMeasure Γ μ] rconvQ Γ μ f φ := by
  have hint := integrable_rconvQ Γ μ f φ
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ _ => ((Lp.memLp _).integrable one_le_two).integrableOn)
    (fun s _ _ => hint.integrableOn) fun s hs hμs => ?_
  rw [← L2.inner_indicatorConstLp_one hs hμs.ne, UnitaryRep.inner_integrated]
  have hcoef : ∀ g, ⟪indicatorConstLp 2 hs hμs.ne (1 : ℂ), rightRegularRep Γ μ g φ⟫_ℂ =
      ∫ x in s, φ (rightMul Γ g x) ∂quotientMeasure Γ μ := by
    intro g
    rw [L2.inner_indicatorConstLp_one]
    exact setIntegral_congr_ae hs ((coeFn_rightRegularRep Γ μ g φ).mono fun x hx _ => hx)
  have hFs : Integrable (uncurry fun (g : G) (x : RightCosetSpace Γ) => f g * φ (rightMul Γ g x))
      (μ.prod ((quotientMeasure Γ μ).restrict s)) := by
    have := (integrable_prod_rightMul Γ μ f φ).restrict (s := univ ×ˢ s)
    rwa [← Measure.prod_restrict, Measure.restrict_univ] at this
  calc ∫ g, (UnitaryRep.ccToL1 μ f) g *
        ⟪indicatorConstLp 2 hs hμs.ne 1, rightRegularRep Γ μ g φ⟫_ℂ ∂μ
      = ∫ g, ∫ x in s, f g * φ (rightMul Γ g x) ∂quotientMeasure Γ μ ∂μ := by
        refine integral_congr_ae ((coeFn_compactSupportToL1 μ f).mono fun g hg => ?_)
        dsimp only
        rw [hg, hcoef, integral_const_mul]
    _ = ∫ x in s, ∫ g, f g * φ (rightMul Γ g x) ∂μ ∂quotientMeasure Γ μ := integral_integral_swap hFs
    _ = ∫ x in s, rconvQ Γ μ f φ x ∂quotientMeasure Γ μ := by simp_rw [rconvQ_eq_integral]

end Operator

end RightCosetSpace

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem det_unipMatrix {r : ℕ} {R : Type*} [CommRing R] (X : UPos n r → R) :
    (unipMatrix X).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    have h : ¬ ((i : ℕ) < r ∧ r ≤ (i : ℕ)) := by omega
    simp [unipMatrix, blockEntry_apply, h]
  · intro i j hij
    have hji : (j : ℕ) < i := hij
    have h1 : i ≠ j := fun h => by rw [h] at hji; exact lt_irrefl _ hji
    have h2 : ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) := by omega
    simp [unipMatrix, blockEntry_apply, h1, h2]

theorem unipGL_mem_normOneGL {r : ℕ} (X : UPos n r → 𝔸[K]) :
    unipGL X ∈ normOneGL K n := by
  have h1 : AdelicGLn.det K n (unipGL X) = 1 :=
    Units.ext (by rw [AdelicGLn.coe_det, coe_unipGL, det_unipMatrix, Units.val_one])
  rw [mem_normOneGL, h1, map_one]
  rfl

variable (K n) in

def unipOne (r : ℕ) (X : UPos n r → 𝔸[K]) : normOneGL K n :=
  ⟨unipGL X, unipGL_mem_normOneGL X⟩

@[simp] theorem coe_unipOne (r : ℕ) (X : UPos n r → 𝔸[K]) :
    (unipOne K n r X : AdelicGLn.AdelicGL K n) = unipGL X := rfl

theorem unipOne_add (r : ℕ) (X Y : UPos n r → 𝔸[K]) :
    unipOne K n r (X + Y) = unipOne K n r X * unipOne K n r Y :=
  Subtype.ext (unipGL_add X Y)

theorem unipOne_zero (r : ℕ) : unipOne K n r 0 = 1 :=
  Subtype.ext unipGL_zero

theorem continuous_unipOne (r : ℕ) : Continuous (unipOne K n r) :=
  continuous_induced_rng.2 continuous_unipGL

theorem unipOne_mem_rationalGLOne (r : ℕ) (ξ : unipLattice K n r) :
    unipOne K n r ξ ∈ rationalGLOne K n := by
  obtain ⟨_, ξ, rfl⟩ := ξ
  change unipGL (fun p => algebraMap K 𝔸[K] (ξ p)) ∈ AdelicGLn.rationalGL K n
  rw [← diagonal_unipGL]
  exact ⟨unipGL ξ, rfl⟩

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

local notation "Γ₁" => rationalGLOne K n

instance (r : ℕ) : SigmaFinite (unipMeasure K n r) := by
  unfold unipMeasure
  infer_instance

theorem lintegral_lift_le {T : Set (normOneGL K n)}
    (hT : IsCompact T) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ ψ : Lp ℂ 2 (quotientMeasure Γ₁ μ),
      (∫⁻ y in T, ‖ψ (mk Γ₁ y)‖ₑ ∂μ) ^ 2 ≤ C * ‖ψ‖ₑ ^ 2 := by
  obtain ⟨N, hN⟩ := exists_encard_le_of_isCompact Γ₁ hT
  refine ⟨μ T * N, ENNReal.mul_ne_top hT.measure_lt_top.ne (by simp), fun ψ => ?_⟩
  have h := L2Kernel.lintegral_mul_sq_le (μ.restrict T) (f := fun _ => 1)
    (g := fun y => ‖ψ (mk Γ₁ y)‖ₑ) aemeasurable_const
    (stronglyMeasurable_lift Γ₁ μ ψ).measurable.enorm.aemeasurable
  simp only [one_mul, one_pow, lintegral_const, Measure.restrict_apply_univ] at h
  refine h.trans ?_
  rw [mul_assoc]
  gcongr
  exact lintegral_lift_sq_le Γ₁ μ ψ hT.measurableSet hN

theorem ae_of_forall_isCompact {p : normOneGL K n → Prop}
    (h : ∀ S : Set (normOneGL K n), IsCompact S → ∀ᵐ y ∂μ.restrict S, p y) : ∀ᵐ y ∂μ, p y := by
  have : ∀ᵐ y ∂μ.restrict (⋃ k, compactCovering (normOneGL K n) k), p y :=
    (ae_restrict_iUnion_iff _ _).2 fun k => h _ (isCompact_compactCovering _ k)
  rwa [iUnion_compactCovering, Measure.restrict_univ] at this

theorem continuous_unipOne_mul (r : ℕ) :
    Continuous fun p : (UPos n r → 𝔸[K]) × normOneGL K n => unipOne K n r p.1 * p.2 :=
  ((continuous_unipOne r).comp continuous_fst).mul continuous_snd

theorem setLIntegral_mul_left (F : normOneGL K n → ℝ≥0∞) (g : normOneGL K n)
    {S : Set (normOneGL K n)} (hS : IsCompact S) :
    ∫⁻ y in S, F (g * y) ∂μ = ∫⁻ z in (g * ·) '' S, F z ∂μ := by
  have hS' : MeasurableSet ((g * ·) '' S) := (hS.image (continuous_const_mul g)).measurableSet
  rw [← lintegral_indicator hS.measurableSet, ← lintegral_indicator hS']
  refine Eq.trans ?_ (lintegral_mul_left_eq_self (fun z => ((g * ·) '' S).indicator F z) g)
  congr 1
  ext y
  by_cases hy : y ∈ S
  · rw [indicator_of_mem hy, indicator_of_mem (mem_image_of_mem _ hy)]
  · rw [indicator_of_notMem hy, indicator_of_notMem]
    rintro ⟨y', hy', h⟩
    exact hy (mul_left_cancel h ▸ hy')

theorem exists_lintegral_unip_sq_le (r : ℕ) {S : Set (normOneGL K n)} (hS : IsCompact S) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ φ : Lp ℂ 2 (quotientMeasure Γ₁ μ),
      (∫⁻ y in S, ∫⁻ X in unipFundamentalDomain K n r,
        ‖φ (mk Γ₁ (unipOne K n r X * y))‖ₑ ∂unipMeasure K n r ∂μ) ^ 2 ≤ C * ‖φ‖ₑ ^ 2 := by
  obtain ⟨D', hD'c, hDD'⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n)
    (r := r)
  set T := (fun p : (UPos n r → 𝔸[K]) × normOneGL K n => unipOne K n r p.1 * p.2) '' (D' ×ˢ S)
  have hT : IsCompact T := (hD'c.prod hS).image (continuous_unipOne_mul r)
  obtain ⟨C, hC, hCφ⟩ := lintegral_lift_le μ hT
  refine ⟨C, hC, fun φ => le_trans (pow_le_pow_left₀ zero_le ?_ 2) (hCφ φ)⟩
  have hmeas : Measurable fun p : (UPos n r → 𝔸[K]) × normOneGL K n =>
      ‖φ (mk Γ₁ (unipOne K n r p.1 * p.2))‖ₑ :=
    ((Lp.stronglyMeasurable φ).measurable.comp ((measurable_mk Γ₁).comp
      (continuous_unipOne_mul r).measurable)).enorm
  have hswap : ∫⁻ y in S, ∫⁻ X in unipFundamentalDomain K n r,
        ‖φ (mk Γ₁ (unipOne K n r X * y))‖ₑ ∂unipMeasure K n r ∂μ =
      ∫⁻ X in unipFundamentalDomain K n r, ∫⁻ y in S,
        ‖φ (mk Γ₁ (unipOne K n r X * y))‖ₑ ∂μ ∂unipMeasure K n r := by
    refine lintegral_lintegral_swap ?_
    exact (hmeas.comp measurable_swap).aemeasurable
  rw [hswap]
  calc ∫⁻ X in unipFundamentalDomain K n r, ∫⁻ y in S,
        ‖φ (mk Γ₁ (unipOne K n r X * y))‖ₑ ∂μ ∂unipMeasure K n r
      ≤ ∫⁻ _ in unipFundamentalDomain K n r, ∫⁻ y in T, ‖φ (mk Γ₁ y)‖ₑ ∂μ ∂unipMeasure K n r := by
        refine setLIntegral_mono' measurableSet_unipFundamentalDomain fun X hX => ?_
        rw [setLIntegral_mul_left μ (fun z => ‖φ (mk Γ₁ z)‖ₑ) (unipOne K n r X) hS]
        refine lintegral_mono_set ?_
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨(X, y), ⟨hDD' hX, hy⟩, rfl⟩
    _ = ∫⁻ y in T, ‖φ (mk Γ₁ y)‖ₑ ∂μ := by
        rw [setLIntegral_const, unipMeasure_unipFundamentalDomain, mul_one]

variable (K n) in

def ctFun (r : ℕ) (F : RightCosetSpace Γ₁ → ℂ) (y : normOneGL K n) : ℂ :=
  ∫ X in unipFundamentalDomain K n r, F (mk Γ₁ (unipOne K n r X * y)) ∂unipMeasure K n r

def constantTermL2 (r : ℕ) (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (y : normOneGL K n) : ℂ :=
  ctFun K n r φ y

theorem ae_ae_unip_notMem {Z : Set (RightCosetSpace Γ₁)} (hZ : quotientMeasure Γ₁ μ Z = 0)
    (r : ℕ) : ∀ᵐ y ∂μ, ∀ᵐ X ∂unipMeasure K n r, mk Γ₁ (unipOne K n r X * y) ∉ Z := by
  set Z' := toMeasurable (quotientMeasure Γ₁ μ) Z
  have hZ' : quotientMeasure Γ₁ μ Z' = 0 := by rw [measure_toMeasurable]; exact hZ
  have hmeas : MeasurableSet {p : (UPos n r → 𝔸[K]) × normOneGL K n |
      mk Γ₁ (unipOne K n r p.1 * p.2) ∉ Z'} :=
    ((measurableSet_toMeasurable _ _).preimage ((measurable_mk Γ₁).comp
      (continuous_unipOne_mul r).measurable)).compl
  have h1 : ∀ᵐ X ∂unipMeasure K n r, ∀ᵐ y ∂μ, mk Γ₁ (unipOne K n r X * y) ∉ Z' := by
    refine Eventually.of_forall fun X => ?_
    rw [ae_iff]
    simp only [not_not]
    have := measure_preimage_mul μ (unipOne K n r X) (mk Γ₁ ⁻¹' Z')
    rw [(quasiMeasurePreserving_mk Γ₁ μ).preimage_null hZ'] at this
    exact this
  have h2 := (Measure.ae_ae_comm hmeas).1 h1
  filter_upwards [h2] with y hy
  filter_upwards [hy] with X hX
  exact fun h => hX (subset_toMeasurable _ _ h)

theorem ae_ctFun_congr (r : ℕ) {F F' : RightCosetSpace Γ₁ → ℂ}
    (h : F =ᵐ[quotientMeasure Γ₁ μ] F') : ∀ᵐ y ∂μ, ctFun K n r F y = ctFun K n r F' y := by
  have hZ : quotientMeasure Γ₁ μ {x | F x ≠ F' x} = 0 := ae_iff.1 h
  filter_upwards [ae_ae_unip_notMem μ hZ r] with y hy
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hy] with X hX
  simpa using hX

theorem ae_integrableOn_unip (r : ℕ) (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) :
    ∀ᵐ y ∂μ, IntegrableOn (fun X => φ (mk Γ₁ (unipOne K n r X * y)))
      (unipFundamentalDomain K n r) (unipMeasure K n r) := by
  have hmeas : Measurable fun p : (UPos n r → 𝔸[K]) × normOneGL K n =>
      ‖φ (mk Γ₁ (unipOne K n r p.1 * p.2))‖ₑ :=
    ((Lp.stronglyMeasurable φ).measurable.comp ((measurable_mk Γ₁).comp
      (continuous_unipOne_mul r).measurable)).enorm
  refine ae_of_forall_isCompact μ fun S hS => ?_
  obtain ⟨C, hC, hCφ⟩ := exists_lintegral_unip_sq_le μ r hS
  have hfin : ∫⁻ y in S, ∫⁻ X in unipFundamentalDomain K n r,
      ‖φ (mk Γ₁ (unipOne K n r X * y))‖ₑ ∂unipMeasure K n r ∂μ ≠ ⊤ := by
    refine (L2Kernel.lt_top_of_sq_lt_top ((hCφ φ).trans_lt ?_)).ne
    exact ENNReal.mul_lt_top hC.lt_top (ENNReal.pow_lt_top enorm_lt_top)
  have hm2 : Measurable fun y => ∫⁻ X in unipFundamentalDomain K n r,
      ‖φ (mk Γ₁ (unipOne K n r X * y))‖ₑ ∂unipMeasure K n r :=
    hmeas.lintegral_prod_left'
  filter_upwards [ae_lt_top' hm2.aemeasurable hfin] with y hy
  refine ⟨?_, hy⟩
  exact ((Lp.stronglyMeasurable φ).comp_measurable ((measurable_mk Γ₁).comp
    ((continuous_unipOne_mul r).comp (continuous_id.prodMk continuous_const)).measurable)).aestronglyMeasurable

theorem stronglyMeasurable_ctFun (r : ℕ) {F : RightCosetSpace Γ₁ → ℂ} (hF : StronglyMeasurable F) :
    StronglyMeasurable (ctFun K n r F) := by
  have : StronglyMeasurable (uncurry fun (X : UPos n r → 𝔸[K]) (y : normOneGL K n) =>
      F (mk Γ₁ (unipOne K n r X * y))) :=
    hF.comp_measurable ((measurable_mk Γ₁).comp (continuous_unipOne_mul r).measurable)
  exact this.integral_prod_left (μ := (unipMeasure K n r).restrict (unipFundamentalDomain K n r))

theorem ae_constantTermL2_add (r : ℕ) (φ ψ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) :
    ∀ᵐ y ∂μ, constantTermL2 μ r (φ + ψ) y = constantTermL2 μ r φ y + constantTermL2 μ r ψ y := by
  filter_upwards [ae_ctFun_congr μ r (Lp.coeFn_add φ ψ), ae_integrableOn_unip μ r φ,
    ae_integrableOn_unip μ r ψ] with y h1 h2 h3
  rw [constantTermL2, h1]
  simp only [constantTermL2, ctFun, Pi.add_apply]
  exact integral_add h2 h3

theorem ae_constantTermL2_smul (r : ℕ) (c : ℂ) (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) :
    ∀ᵐ y ∂μ, constantTermL2 μ r (c • φ) y = c * constantTermL2 μ r φ y := by
  filter_upwards [ae_ctFun_congr μ r (Lp.coeFn_smul c φ)] with y h1
  rw [constantTermL2, h1, ctFun, constantTermL2, ctFun, ← integral_const_mul]
  rfl

theorem ae_constantTermL2_sub (r : ℕ) (φ ψ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) :
    ∀ᵐ y ∂μ, constantTermL2 μ r (φ - ψ) y = constantTermL2 μ r φ y - constantTermL2 μ r ψ y := by
  filter_upwards [ae_ctFun_congr μ r (Lp.coeFn_sub φ ψ), ae_integrableOn_unip μ r φ,
    ae_integrableOn_unip μ r ψ] with y h1 h2 h3
  rw [constantTermL2, h1]
  simp only [constantTermL2, ctFun, Pi.sub_apply]
  exact integral_sub h2 h3

theorem exists_lintegral_constantTermL2_sq_le (r : ℕ) {S : Set (normOneGL K n)} (hS : IsCompact S) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ φ : Lp ℂ 2 (quotientMeasure Γ₁ μ),
      (∫⁻ y in S, ‖constantTermL2 μ r φ y‖ₑ ∂μ) ^ 2 ≤ C * ‖φ‖ₑ ^ 2 := by
  obtain ⟨C, hC, hCφ⟩ := exists_lintegral_unip_sq_le μ r hS
  refine ⟨C, hC, fun φ => le_trans ?_ (hCφ φ)⟩
  gcongr with y
  exact enorm_integral_le_lintegral_enorm _

instance isMulRightInvariant_haar : μ.IsMulRightInvariant := isMulRightInvariant_normOneGL μ

def IsCuspidalL2 (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) : Prop :=
  ∀ r : ℕ, 0 < r → r < n → constantTermL2 μ r φ =ᵐ[μ] 0

def cuspidalL2 : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ₁ μ)) where
  carrier := {φ | IsCuspidalL2 μ φ}
  zero_mem' := fun r _ _ => by
    filter_upwards [ae_ctFun_congr μ r (Lp.coeFn_zero ℂ 2 (quotientMeasure Γ₁ μ))] with y hy
    rw [constantTermL2, hy]
    simp [ctFun]
  add_mem' := fun {φ ψ} hφ hψ r hr hrn => by
    filter_upwards [ae_constantTermL2_add μ r φ ψ, hφ r hr hrn, hψ r hr hrn] with y h1 h2 h3
    rw [h1, h2, h3]
    simp
  smul_mem' := fun c φ hφ r hr hrn => by
    filter_upwards [ae_constantTermL2_smul μ r c φ, hφ r hr hrn] with y h1 h2
    rw [h1, h2]
    simp


theorem isClosed_cuspidalL2 : IsClosed (cuspidalL2 μ : Set (Lp ℂ 2 (quotientMeasure Γ₁ μ))) := by
  refine isClosed_of_closure_subset fun φ hφ r hr hrn => ?_
  refine ae_of_forall_isCompact μ fun S hS => ?_
  obtain ⟨C, hC, hCφ⟩ := exists_lintegral_constantTermL2_sq_le μ r hS
  set I := ∫⁻ y in S, ‖constantTermL2 μ r φ y‖ₑ ∂μ
  have hle : ∀ ε : ℝ, 0 < ε → I ^ 2 ≤ C * ENNReal.ofReal ε ^ 2 := by
    intro ε hε
    obtain ⟨ψ, hψ, hdist⟩ := Metric.mem_closure_iff.1 hφ ε hε
    have hI : I = ∫⁻ y in S, ‖constantTermL2 μ r (φ - ψ) y‖ₑ ∂μ := by
      refine lintegral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [ae_constantTermL2_sub μ r φ ψ, (hψ : IsCuspidalL2 μ ψ) r hr hrn] with y h1 h2
      rw [h1, h2, Pi.zero_apply, sub_zero]
    rw [hI]
    refine (hCφ (φ - ψ)).trans ?_
    gcongr
    rw [← ofReal_norm, ← dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal hdist.le
  have hI0 : I ^ 2 = 0 := by
    refine le_antisymm ?_ zero_le
    have ht : Tendsto (fun ε : ℝ => C * ENNReal.ofReal ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun ε : ℝ => ENNReal.ofReal ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have := (((ENNReal.continuous_pow 2).comp ENNReal.continuous_ofReal).tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        simpa [Function.comp_def] using this
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inr hC)
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => hle ε hε)
  have hI' : I = 0 := pow_eq_zero_iff two_ne_zero |>.1 hI0
  have hm : AEMeasurable (fun y => ‖constantTermL2 μ r φ y‖ₑ) (μ.restrict S) :=
    (stronglyMeasurable_ctFun r (Lp.stronglyMeasurable φ)).measurable.enorm.aemeasurable
  filter_upwards [(lintegral_eq_zero_iff' hm).1 hI'] with y hy
  simpa using hy

theorem isInvariant_cuspidalL2 : (rightRegularRep Γ₁ μ).IsInvariant (cuspidalL2 μ) := by
  intro g φ hφ r hr hrn
  have h2 := ae_ctFun_congr μ r (coeFn_rightRegularRep Γ₁ μ g φ)
  have h3 : ∀ y, ctFun K n r (fun z => φ (rightMul Γ₁ g z)) y = constantTermL2 μ r φ (y * g) := by
    intro y
    simp only [ctFun, constantTermL2, rightMul_mk, mul_assoc]
  have h4 : ∀ᵐ y ∂μ, constantTermL2 μ r φ (y * g) = 0 :=
    (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae ((hφ : IsCuspidalL2 μ φ) r hr hrn)
  filter_upwards [h2, h4] with y hy1 hy2
  rw [constantTermL2, hy1, h3, hy2, Pi.zero_apply]

theorem integral_rconv_unip_eq_zero (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} (hφ : φ ∈ cuspidalL2 μ) {r : ℕ} (hr : 0 < r) (hrn : r < n)
    (x : normOneGL K n) :
    ∫ X in unipFundamentalDomain K n r, rconv Γ₁ μ f φ (unipOne K n r X * x)
      ∂unipMeasure K n r = 0 := by
  set S := (x * ·) '' tsupport (f : normOneGL K n → ℂ)
  have hS : IsCompact S := f.hasCompactSupport.isCompact.image (continuous_const_mul x)
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hfS : ∀ z ∉ S, f (x⁻¹ * z) = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz ⟨x⁻¹ * z, h, by simp⟩
  set F : (UPos n r → 𝔸[K]) → normOneGL K n → ℂ :=
    fun X z => f (x⁻¹ * z) * φ (mk Γ₁ (unipOne K n r X * z))
  have hFm : StronglyMeasurable (uncurry F) :=
    (f.continuous.comp (continuous_const_mul x⁻¹ |>.comp continuous_snd)).stronglyMeasurable.mul
      ((Lp.stronglyMeasurable φ).comp_measurable ((measurable_mk Γ₁).comp
        (continuous_unipOne_mul r).measurable))
  have hint : Integrable (uncurry F)
      (((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod μ) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    obtain ⟨C, hC, hCφ⟩ := exists_lintegral_unip_sq_le μ r hS
    have hfin : ∫⁻ z in S, ∫⁻ X in unipFundamentalDomain K n r,
        ‖φ (mk Γ₁ (unipOne K n r X * z))‖ₑ ∂unipMeasure K n r ∂μ < ⊤ :=
      L2Kernel.lt_top_of_sq_lt_top ((hCφ φ).trans_lt
        (ENNReal.mul_lt_top hC.lt_top (ENNReal.pow_lt_top enorm_lt_top)))
    have hmeas : Measurable fun p : (UPos n r → 𝔸[K]) × normOneGL K n =>
        ‖φ (mk Γ₁ (unipOne K n r p.1 * p.2))‖ₑ :=
      ((Lp.stronglyMeasurable φ).measurable.comp ((measurable_mk Γ₁).comp
        (continuous_unipOne_mul r).measurable)).enorm
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hFm.aestronglyMeasurable.enorm]
    calc ∫⁻ X in unipFundamentalDomain K n r, ∫⁻ z, ‖uncurry F (X, z)‖ₑ ∂μ ∂unipMeasure K n r
        ≤ ∫⁻ X in unipFundamentalDomain K n r, ∫⁻ z in S,
            ENNReal.ofReal M * ‖φ (mk Γ₁ (unipOne K n r X * z))‖ₑ ∂μ ∂unipMeasure K n r := by
          refine lintegral_mono fun X => ?_
          rw [← lintegral_indicator hS.measurableSet]
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ S
          · rw [indicator_of_mem hz]
            simp only [F, uncurry_apply_pair, enorm_mul]
            gcongr
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hM _)
          · rw [indicator_of_notMem hz]
            simp [F, hfS z hz]
      _ = ENNReal.ofReal M * ∫⁻ z in S, ∫⁻ X in unipFundamentalDomain K n r,
            ‖φ (mk Γ₁ (unipOne K n r X * z))‖ₑ ∂unipMeasure K n r ∂μ := by
          simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact lintegral_lintegral_swap hmeas.aemeasurable
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have hinner : ∀ X, rconv Γ₁ μ f φ (unipOne K n r X * x) = ∫ z, F X z ∂μ := by
    intro X
    rw [rconv, ← integral_mul_left_eq_self _ (unipOne K n r X)]
    congr 1
    ext z
    simp only [F, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hCT : ∀ z, ∫ X in unipFundamentalDomain K n r, F X z ∂unipMeasure K n r =
      f (x⁻¹ * z) * constantTermL2 μ r φ z := by
    intro z
    simp only [F, constantTermL2, ctFun]
    exact integral_const_mul _ _
  simp_rw [hinner]
  rw [integral_integral_swap hint]
  simp_rw [hCT]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [(hφ : IsCuspidalL2 μ φ) r hr hrn] with z hz
  rw [hz, Pi.zero_apply, mul_zero]

end CuspidalSpectrum

end

end GroundTheory.Automorphic
end
