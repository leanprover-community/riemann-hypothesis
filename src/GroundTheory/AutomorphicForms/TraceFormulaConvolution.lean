import Mathlib
import GroundTheory.AutomorphicForms.QuotientKernel
import GroundTheory.AutomorphicForms.KernelTrace
import GroundTheory.AutomorphicForms.LocallyConstantCompact

section
namespace GroundTheory.Automorphic

open MeasureTheory Filter Topology Uniformity Set
open scoped InnerProductSpace ENNReal

noncomputable section

section Uniform

variable {X : Type*} [UniformSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

theorem continuous_integral_mul_of_uniformSpace (a b : C(X × X, ℂ)) :
    Continuous fun z : X × X => ∫ y, a (z.1, y) * b (y, z.2) ∂μ := by
  refine UniformContinuous.continuous ?_
  refine (Metric.uniformity_basis_dist.tendsto_right_iff).2 fun ε hε => ?_
  set A := ‖a‖
  set B := ‖b‖
  set M := μ.real univ
  set δ : ℝ := ε / ((A + B) * M + 1)
  have hδ : 0 < δ := by positivity
  obtain ⟨u₁, hu₁, v₁, hv₁, h₁⟩ := entourageProd_subset
    (CompactSpace.uniformContinuous_of_continuous a.continuous (Metric.dist_mem_uniformity hδ))
  obtain ⟨u₂, hu₂, v₂, hv₂, h₂⟩ := entourageProd_subset
    (CompactSpace.uniformContinuous_of_continuous b.continuous (Metric.dist_mem_uniformity hδ))
  filter_upwards [entourageProd_mem_uniformity hu₁ hv₂] with w hw
  obtain ⟨⟨x, z⟩, ⟨x', z'⟩⟩ := w
  obtain ⟨hx, hz⟩ := hw
  change dist (∫ y, a (x, y) * b (y, z) ∂μ) (∫ y, a (x', y) * b (y, z') ∂μ) < ε
  have hrowa : ∀ x, Continuous fun y => a (x, y) := fun x =>
    a.continuous.comp (continuous_const.prodMk continuous_id)
  have hcolb : ∀ z, Continuous fun y => b (y, z) := fun z =>
    b.continuous.comp (continuous_id.prodMk continuous_const)
  have hint : ∀ x z, Integrable (fun y => a (x, y) * b (y, z)) μ := fun x z =>
    integrable_of_continuous_compact ((hrowa x).mul (hcolb z)) μ
  rw [dist_eq_norm, ← integral_sub (hint x z) (hint x' z')]
  have hpt : ∀ y, ‖a (x, y) * b (y, z) - a (x', y) * b (y, z')‖ ≤ δ * B + A * δ := by
    intro y
    have ha : ‖a (x, y) - a (x', y)‖ < δ := by
      rw [← dist_eq_norm]
      exact h₁ (show ((x, y), (x', y)) ∈ entourageProd u₁ v₁ from ⟨hx, refl_mem_uniformity hv₁⟩)
    have hb : ‖b (y, z) - b (y, z')‖ < δ := by
      rw [← dist_eq_norm]
      exact h₂ (show ((y, z), (y, z')) ∈ entourageProd u₂ v₂ from ⟨refl_mem_uniformity hu₂, hz⟩)
    have e : a (x, y) * b (y, z) - a (x', y) * b (y, z') =
        (a (x, y) - a (x', y)) * b (y, z) + a (x', y) * (b (y, z) - b (y, z')) := by ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul ha.le (b.norm_coe_le_norm _) (norm_nonneg _) hδ.le
    · rw [norm_mul]
      exact mul_le_mul (a.norm_coe_le_norm _) hb.le (norm_nonneg _) (norm_nonneg _)
  refine (norm_integral_le_of_norm_le_const (ae_of_all _ hpt)).trans_lt ?_
  have hM : 0 ≤ M := measureReal_nonneg
  have hAB : 0 ≤ A + B := by positivity
  have e : (δ * B + A * δ) * M = ε * ((A + B) * M / ((A + B) * M + 1)) := by
    simp only [δ]; field_simp; ring
  rw [e]
  have : (A + B) * M / ((A + B) * M + 1) < 1 := (div_lt_one (by positivity)).2 (lt_add_one _)
  nlinarith

end Uniform

section Comp

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def compKernel (a b : C(X × X, ℂ)) : C(X × X, ℂ) where
  toFun z := ∫ y, a (z.1, y) * b (y, z.2) ∂μ
  continuous_toFun := by
    let _ : UniformSpace X := uniformSpaceOfCompactR1
    exact continuous_integral_mul_of_uniformSpace μ a b

theorem compKernel_apply (a b : C(X × X, ℂ)) (z : X × X) :
    compKernel μ a b z = ∫ y, a (z.1, y) * b (y, z.2) ∂μ := rfl

theorem contKernelOp_comp (a b : C(X × X, ℂ)) :
    (contKernelOp μ a).comp (contKernelOp μ b) = contKernelOp μ (compKernel μ a b) := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [contKernelOp_apply_ae μ a (contKernelOp μ b f),
    contKernelOp_apply_ae μ (compKernel μ a b) f] with x h1 h2
  rw [ContinuousLinearMap.comp_apply, h1, h2]
  have h3 : (fun y => a (x, y) * contKernelOp μ b f y) =ᵐ[μ]
      fun y => ∫ z, a (x, y) * (b (y, z) * f z) ∂μ := by
    filter_upwards [contKernelOp_apply_ae μ b f] with y hy
    rw [hy, integral_const_mul]
  rw [integral_congr_ae h3]
  have hf : Integrable (fun z => f z) μ := (Lp.memLp f).integrable one_le_two
  have hab : Continuous fun p : X × X => a (x, p.1) * b (p.1, p.2) :=
    (a.continuous.comp (continuous_const.prodMk continuous_fst)).mul b.continuous
  have hint : Integrable (Function.uncurry fun y z => a (x, y) * (b (y, z) * f z)) (μ.prod μ) := by
    have h1 : Integrable (fun p : X × X => (1 : ℂ) * f p.2) (μ.prod μ) :=
      (integrable_const (1 : ℂ)).mul_prod hf
    have h2 := h1.bdd_mul (c := ‖a‖ * ‖b‖)
      (measurable_of_continuous_compactProd hab).aestronglyMeasurable
      (ae_of_all _ fun p => by
        rw [norm_mul]
        exact mul_le_mul (a.norm_coe_le_norm _) (b.norm_coe_le_norm _) (norm_nonneg _)
          (norm_nonneg _))
    refine h2.congr (ae_of_all _ fun p => ?_)
    obtain ⟨y, z⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [compKernel_apply]
  rw [← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  ring

end Comp

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

section Convolution

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G)

def convFun (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) (x : G) : ℂ :=
  ∫ g, f₁ g * f₂ (g⁻¹ * x) ∂μ

theorem convFun_eq_setIntegral (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) (x : G) :
    convFun μ f₁ f₂ x = ∫ g in tsupport f₁, f₁ g * f₂ (g⁻¹ * x) ∂μ := by
  rw [convFun, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro g hg
  rw [image_eq_zero_of_notMem_tsupport hg, zero_mul]

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G] [IsFiniteMeasureOnCompacts μ] in
theorem continuous_convFun (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) :
    Continuous (convFun μ f₁ f₂) := by
  have h : convFun μ f₁ f₂ = fun x => ∫ g in tsupport f₁, f₁ g * f₂ (g⁻¹ * x) ∂μ :=
    funext (convFun_eq_setIntegral μ f₁ f₂)
  rw [h]
  exact continuous_parametric_integral_of_continuous (f := fun x g => f₁ g * f₂ (g⁻¹ * x))
    (by fun_prop) f₁.hasCompactSupport

theorem convFun_eq_zero (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) {x : G}
    (hx : x ∉ tsupport f₁ * tsupport f₂) : convFun μ f₁ f₂ x = 0 := by
  rw [convFun]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun g => ?_)
  by_cases h1 : g ∈ tsupport f₁
  · have h2 : g⁻¹ * x ∉ tsupport f₂ := fun h2 =>
      hx ⟨g, h1, g⁻¹ * x, h2, by simp only [mul_inv_cancel_left]⟩
    simp [image_eq_zero_of_notMem_tsupport h2]
  · simp [image_eq_zero_of_notMem_tsupport h1]

variable [IsTopologicalGroup G] [T2Space G] in
theorem hasCompactSupport_convFun (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) :
    HasCompactSupport (convFun μ f₁ f₂) :=
  HasCompactSupport.intro (f₁.hasCompactSupport.mul f₂.hasCompactSupport)
    fun _ hx => convFun_eq_zero μ f₁ f₂ hx

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
  [BorelSpace G] [IsFiniteMeasureOnCompacts μ]

def conv (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) : CompactlySupportedContinuousMap G ℂ where
  toFun := convFun μ f₁ f₂
  continuous_toFun := continuous_convFun μ f₁ f₂
  hasCompactSupport' := hasCompactSupport_convFun μ f₁ f₂

theorem conv_apply (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) (x : G) :
    conv μ f₁ f₂ x = ∫ g, f₁ g * f₂ (g⁻¹ * x) ∂μ :=
  rfl

end Convolution

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] in

theorem finite_setOf_mem_of_isCompact [IsTopologicalGroup G] {C : Set G} (hC : IsCompact C) :
    {δ : Γ | (δ : G) ∈ C}.Finite := by
  have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete
  exact (hcl.isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage hC).finite_of_discrete

section Kernel

variable (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]

theorem quotientKernel_conv (f₁ f₂ : CompactlySupportedContinuousMap G ℂ)
    (x z : RightCosetSpace Γ) :
    quotientKernel Γ (conv μ f₁ f₂) (x, z) =
      ∫ y, quotientKernel Γ f₁ (x, y) * quotientKernel Γ f₂ (y, z) ∂quotientMeasure Γ μ := by
  obtain ⟨a, rfl⟩ := mk_surjective Γ x
  obtain ⟨b, rfl⟩ := mk_surjective Γ z
  let φ : C(RightCosetSpace Γ, ℂ) :=
    ⟨fun y => quotientKernel Γ f₂ (y, mk Γ b),
      (continuous_quotientKernel Γ f₂).comp (continuous_id.prodMk continuous_const)⟩
  have hφ := integral_mul_rightMul_eq Γ μ f₁ φ (mk Γ a)
  simp only [φ, ContinuousMap.coe_mk] at hφ
  rw [← hφ]

  set C : Set G := a • ((tsupport f₁ * tsupport f₂) * {b⁻¹}) with hC
  have hCc : IsCompact C :=
    ((f₁.hasCompactSupport.mul f₂.hasCompactSupport).mul isCompact_singleton).smul a
  have hfin := finite_setOf_mem_of_isCompact Γ hCc
  set S := hfin.toFinset
  have hmem : ∀ δ : Γ, (∃ g, f₁ g * f₂ (g⁻¹ * (a⁻¹ * δ * b)) ≠ 0) → δ ∈ S := by
    rintro δ ⟨g, hg⟩
    rw [Finite.mem_toFinset]
    have h1 : g ∈ tsupport f₁ := subset_tsupport _ (left_ne_zero_of_mul hg)
    have h2 : g⁻¹ * (a⁻¹ * δ * b) ∈ tsupport f₂ := subset_tsupport _ (right_ne_zero_of_mul hg)
    refine ⟨(a⁻¹ * δ * b) * b⁻¹, ⟨a⁻¹ * δ * b, ⟨g, h1, _, h2, by group⟩, b⁻¹, rfl, rfl⟩, ?_⟩
    simp only [smul_eq_mul]
    group
  have hsupp' : (support fun δ : Γ => conv μ f₁ f₂ (a⁻¹ * δ * b)) ⊆ S := by
    intro δ hδ
    rw [mem_support, conv_apply] at hδ
    by_contra hS
    exact hδ (integral_eq_zero_of_ae (Eventually.of_forall fun g => by
      by_contra h
      exact hS (hmem δ ⟨g, h⟩)))
  have hint : ∀ δ : Γ, Integrable (fun g => f₁ g * f₂ (g⁻¹ * (a⁻¹ * δ * b))) μ := fun δ =>
    (by fun_prop : Continuous fun g => f₁ g * f₂ (g⁻¹ * (a⁻¹ * δ * b))).integrable_of_hasCompactSupport
      f₁.hasCompactSupport.mul_right
  rw [quotientKernel_mk, finsum_eq_sum_of_support_subset _ hsupp']
  simp only [conv_apply]
  rw [← integral_finsetSum _ fun δ _ => hint δ]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [rightMul_mk, quotientKernel_mk]
  by_cases hg : f₁ g = 0
  · simp [hg]
  rw [finsum_eq_sum_of_support_subset _ (s := S) ?_, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun δ _ => ?_
    congr 2
    group
  · intro δ hδ
    refine hmem δ ⟨g, mul_ne_zero hg ?_⟩
    rw [mem_support] at hδ
    have : g⁻¹ * (a⁻¹ * δ * b) = (a * g)⁻¹ * δ * b := by group
    rwa [this]

def quotientKernelC (f : CompactlySupportedContinuousMap G ℂ) :
    C(RightCosetSpace Γ × RightCosetSpace Γ, ℂ) :=
  ⟨quotientKernel Γ f, continuous_quotientKernel Γ f⟩

@[simp] theorem quotientKernelC_apply (f : CompactlySupportedContinuousMap G ℂ)
    (p : RightCosetSpace Γ × RightCosetSpace Γ) : quotientKernelC Γ f p = quotientKernel Γ f p :=
  rfl

variable [CompactSpace (RightCosetSpace Γ)]

theorem quotientKernelC_conv (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) :
    quotientKernelC Γ (conv μ f₁ f₂) =
      compKernel (quotientMeasure Γ μ) (quotientKernelC Γ f₁) (quotientKernelC Γ f₂) := by
  ext ⟨x, z⟩
  rw [compKernel_apply, quotientKernelC_apply, quotientKernel_conv Γ μ f₁ f₂ x z]
  rfl

end Kernel

section Operator

variable (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ]
  [CompactSpace (RightCosetSpace Γ)]

theorem kernelOperator_eq_contKernelOp (f : CompactlySupportedContinuousMap G ℂ) :
    kernelOperator Γ μ f = contKernelOp (quotientMeasure Γ μ) (quotientKernelC Γ f) :=
  rfl

theorem integrated_conv (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) :
    (rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ (conv μ f₁ f₂)) =
      ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f₁)).comp
        ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f₂)) := by
  rw [integrated_rightRegularRep_eq_kernelOperator, integrated_rightRegularRep_eq_kernelOperator,
    integrated_rightRegularRep_eq_kernelOperator, kernelOperator_eq_contKernelOp,
    kernelOperator_eq_contKernelOp, kernelOperator_eq_contKernelOp, quotientKernelC_conv,
    contKernelOp_comp]


end Operator

end RightCosetSpace

section TotallyDisconnected

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def indicatorOne (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    CompactlySupportedContinuousMap G ℂ where
  toFun := (K : Set G).indicator 1
  continuous_toFun := by
    rw [← LocallyConstant.coe_charFn ℂ K.isClopen]
    exact (LocallyConstant.charFn ℂ K.isClopen).continuous
  hasCompactSupport' := HasCompactSupport.intro hK fun _ hx => indicator_of_notMem hx _


variable (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]


variable [TotallyDisconnectedSpace G]


end TotallyDisconnected

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [TotallyDisconnectedSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]


end RightCosetSpace

end

end GroundTheory.Automorphic
end
