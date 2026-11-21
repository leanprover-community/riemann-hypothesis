import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
import BuildAid.ForwardExisting
import GroundTheory.AutomorphicForms.GKModules.Garding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftTranslateBoundedDerivFunctional

section
section
open MeasureTheory Pointwise

namespace GlobalTheory

theorem integral_mul_convolution_eq (H : Type) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] (μ : Measure H) (hμ : μ.IsHaarMeasure)
    (K : Set H) (hK : IsCompact K) (κ a : H → ℂ) (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) (ha : Measurable a) (hai : Integrable a μ)
    (haK : ∀ x ∉ K, a x = 0) (f : H → ℂ) (hf : Continuous f) :
    ∫ z, f z * (∫ x, κ x * a (x⁻¹ * z) ∂μ) ∂μ = ∫ x, κ x * ∫ y, f (x * y) * a y ∂μ ∂μ := by
  haveI := hμ
  have hC : IsCompact (tsupport κ) := hκc
  obtain ⟨M, hM⟩ : ∃ M, ∀ w ∈ tsupport κ * K, ‖f w‖ ≤ M :=
    (hC.mul hK).exists_bound_of_continuousOn hf.continuousOn
  set G : H × H → ℂ := fun p => κ p.1 * (f p.2 * a (p.1⁻¹ * p.2)) with hG
  have hGm : AEStronglyMeasurable G (μ.prod μ) := by
    have h1 : Measurable fun p : H × H => a (p.1⁻¹ * p.2) :=
      ha.comp (measurable_fst.inv.mul measurable_snd)
    exact (hκ.comp continuous_fst).aestronglyMeasurable.mul
      ((hf.comp continuous_snd).aestronglyMeasurable.mul h1.aestronglyMeasurable)
  have hbound : Integrable (fun p : H × H => (‖κ p.1‖ * M) * ‖a p.2‖) (μ.prod μ) :=
    Integrable.mul_prod ((hκ.integrable_of_hasCompactSupport hκc).norm.mul_const M) hai.norm
  have hGs : Integrable (G ∘ fun p : H × H => (p.1, p.1 * p.2)) (μ.prod μ) := by
    refine hbound.mono' (hGm.comp_measurePreserving (measurePreserving_prod_mul μ μ)) ?_
    refine Filter.Eventually.of_forall fun p => ?_
    simp only [Function.comp, G, inv_mul_cancel_left]
    by_cases h1 : κ p.1 = 0
    · simp only [h1, zero_mul, norm_zero, mul_zero]; positivity
    by_cases h2 : a p.2 = 0
    · simp only [h2, mul_zero, norm_zero]; rfl
    have hx : p.1 ∈ tsupport κ := subset_tsupport _ h1
    have hy : p.2 ∈ K := by
      by_contra h; exact h2 (haK _ h)
    have hfM := hM _ (Set.mul_mem_mul hx hy)
    rw [norm_mul, norm_mul]
    calc ‖κ p.1‖ * (‖f (p.1 * p.2)‖ * ‖a p.2‖) ≤ ‖κ p.1‖ * (M * ‖a p.2‖) := by gcongr
      _ = ‖κ p.1‖ * M * ‖a p.2‖ := by ring
  have hGi : Integrable G (μ.prod μ) :=
    ((measurePreserving_prod_mul μ μ).integrable_comp hGm).1 hGs
  have hF : Integrable (Function.uncurry fun z x => f z * (κ x * a (x⁻¹ * z))) (μ.prod μ) := by
    refine hGi.swap.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp, G, Prod.fst_swap, Prod.snd_swap, Function.uncurry]
    ring
  calc ∫ z, f z * (∫ x, κ x * a (x⁻¹ * z) ∂μ) ∂μ
      = ∫ z, ∫ x, f z * (κ x * a (x⁻¹ * z)) ∂μ ∂μ := by
        congr 1; funext z; exact (integral_const_mul _ _).symm
    _ = ∫ x, ∫ z, f z * (κ x * a (x⁻¹ * z)) ∂μ ∂μ := integral_integral_swap hF
    _ = ∫ x, κ x * ∫ y, f (x * y) * a y ∂μ ∂μ := by
        congr 1; funext x
        rw [← integral_mul_left_eq_self (fun z => f z * (κ x * a (x⁻¹ * z))) x,
          ← integral_const_mul]
        congr 1; funext y
        simp only [inv_mul_cancel_left]
        ring

end GlobalTheory
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_mul_convolution_eq_alt : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∀ κ a : H → ℂ, Continuous κ → HasCompactSupport κ → Measurable a → Integrable a μ → (∀ x ∉ K, a x = 0) → ∀ f : H → ℂ, Continuous f → ∫ z, f z * (∫ x, κ x * a (x⁻¹ * z) ∂μ) ∂μ = ∫ x, κ x * ∫ y, f (x * y) * a y ∂μ ∂μ := by
  atlas_forward_decl GlobalTheory.integral_mul_convolution_eq
end

section
section
open MeasureTheory Pointwise

namespace GlobalTheory

theorem lintegral_inv_le_of_support_compact : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ φ : H → ENNReal, Measurable φ → (∀ x ∉ K, φ x = 0) → ∫⁻ x, φ x⁻¹ ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by
  intro H _ _ _ _ _ _ _ _ μ hμ K hK
  obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : H)
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have hC0 : μ C ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hC1).ne'
  have hCt : μ C ≠ ⊤ := hCc.measure_lt_top.ne
  have hLc : IsCompact (C * K⁻¹) := hCc.mul hK.inv
  have hLt : μ (C * K⁻¹) ≠ ⊤ := hLc.measure_lt_top.ne
  have hpre : ∀ y : H, μ ((· * y) ⁻¹' C) = (Measure.modularCharacterFun y : ENNReal) * μ C := by
    intro y
    rw [← Measure.map_apply (measurable_mul_const y) hCm,
      Measure.map_right_mul_eq_modularCharacterFun_smul μ y]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hbound : ∀ y ∈ K, Measure.modularCharacterFun y ≤ (μ (C * K⁻¹)).toNNReal / (μ C).toNNReal := by
    intro y hy
    have hsub : (· * y) ⁻¹' C ⊆ (C * K⁻¹) := by
      intro z hz
      exact ⟨z * y, hz, y⁻¹, by simpa using hy, by simp⟩
    have h1 : (Measure.modularCharacterFun y : ENNReal) * μ C ≤ μ (C * K⁻¹) := (hpre y) ▸ measure_mono hsub
    have hCpos : 0 < (μ C).toNNReal := ENNReal.toNNReal_pos hC0 hCt
    rw [le_div_iff₀ hCpos]
    have := ENNReal.toNNReal_mono hLt h1
    simpa [ENNReal.toNNReal_mul] using this
  refine ⟨(μ (C * K⁻¹)).toNNReal / (μ C).toNNReal, fun φ hφ hsupp => ?_⟩
  have key : ∫⁻ x, φ x ∂μ = ∫⁻ x, (Measure.modularCharacterFun x : ENNReal) * φ x⁻¹ ∂μ := by
    have h := measure_mul_lintegral_eq μ μ hCm φ hφ
    simp_rw [hpre, mul_comm _ (μ C), mul_assoc] at h
    rw [lintegral_const_mul' _ _ hCt] at h
    exact (ENNReal.mul_right_inj hC0 hCt).1 h
  rw [key, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono fun x => ?_
  by_cases hx : x⁻¹ ∈ K
  · have hb := hbound _ hx
    have hmul : (Measure.modularCharacterFun x⁻¹ : ENNReal) * Measure.modularCharacterFun x = 1 := by
      rw [← ENNReal.coe_mul, ← Measure.modularCharacterFun_map_mul, inv_mul_cancel,
        Measure.modularCharacterFun_map_one, ENNReal.coe_one]
    calc φ x⁻¹ = ((Measure.modularCharacterFun x⁻¹ : ENNReal) * Measure.modularCharacterFun x) * φ x⁻¹ := by rw [hmul, one_mul]
      _ = (Measure.modularCharacterFun x⁻¹ : ENNReal) * ((Measure.modularCharacterFun x : ENNReal) * φ x⁻¹) := by ring
      _ ≤ _ := by gcongr
  · rw [hsupp _ hx]; exact bot_le

end GlobalTheory
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_inv_le_of_support_compact_alt : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ φ : H → ENNReal, Measurable φ → (∀ x ∉ K, φ x = 0) → ∫⁻ x, φ x⁻¹ ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by
  atlas_forward_decl GlobalTheory.lintegral_inv_le_of_support_compact
end

section
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff Manifold

namespace GlobalTheory

theorem isSmoothFun_integral_mul_right : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [IsFiniteMeasure ν] (K : Set G), IsCompact K → ν Kᶜ = 0 → ∀ κ : G → ℂ, h.IsSmoothFun κ → h.IsSmoothFun (fun z => ∫ y, κ (z * y) ∂ν) := by
  intro 𝔸 _ _ _ _ G 𝔤 h _ _ ν _ K hK hν κ hκ
  haveI := secondCountableTopology_subgroup_units G
  haveI := h.locallyCompactSpace
  obtain ⟨ψ, hψ1, -, hψc, -⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro g
  have hae : ∀ᵐ y ∂ν, y ∈ K := by
    rw [ae_iff]; exact hν
  have e : (fun Y : 𝔤 => ∫ y, κ (g * h.expG Y * y) ∂ν) =
      fun Y => ∫ y, ((ψ y : ℝ) : ℂ) * κ (g * h.expG Y * y) ∂ν := by
    funext Y
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    simp [hψ1 hy]
  rw [e]
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hκg : ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (fun x : G => κ (g * x)) :=
    ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hκ (contMDiff_const.mul contMDiff_id)
  set Φ : 𝔤 → G → ℂ := fun Y y => κ (g * h.expG Y * y) with hΦdef
  have hΦ : ∀ y₀ : G, ContDiff ℝ ∞ (fun q : 𝔤 × 𝔤 => Φ q.1 (y₀ * h.expG q.2)) := by
    intro y₀
    have := h.contDiff_comp_expG_mul_expG hκg contDiff_fst y₀ contDiff_snd
    simpa [hΦdef, mul_assoc] using this
  have hΦY : ∀ y : G, ContDiff ℝ ∞ (fun Y => Φ Y y) := by
    intro y
    have := h.contDiff_comp_expG_mul_expG hκg contDiff_id y (contDiff_const (c := (0 : 𝔤)))
    simpa [hΦdef, mul_assoc] using this
  have hD : ∀ (k : ℕ) (Y : 𝔤) (y : G),
      iteratedFDeriv ℝ k (fun Y => ((ψ y : ℝ) : ℂ) * Φ Y y) Y =
        ((ψ y : ℝ) : ℂ) • iteratedFDeriv ℝ k (fun Y => Φ Y y) Y := by
    intro k Y y
    have e : (fun Y => ((ψ y : ℝ) : ℂ) * Φ Y y) = ((ψ y : ℝ) : ℂ) • fun Y => Φ Y y := by
      funext Y; simp [smul_eq_mul]
    rw [e, iteratedFDeriv_const_smul_apply ((hΦY y).contDiffAt.of_le (by exact_mod_cast le_top))]
  change ContDiff ℝ ∞ fun Y : 𝔤 => ∫ y, ((ψ y : ℝ) : ℂ) * Φ Y y ∂ν
  refine contDiff_integral_of_iteratedFDeriv (μ := ν) (fun (Y : 𝔤) (y : G) => ((ψ y : ℝ) : ℂ) * Φ Y y)
    (fun y => contDiff_const.mul (hΦY y)) (fun k => ?_) (fun Y₀ => ?_)
  · have hc := h.continuous_iteratedFDeriv_param Φ hΦ k
    refine (((Complex.continuous_ofReal.comp ψ.continuous).comp continuous_snd).smul hc).congr fun q => ?_
    exact (hD k q.1 q.2).symm
  · refine ⟨Set.univ, Filter.univ_mem, tsupport ψ, hψc, fun Y _ y hy => ?_⟩
    simp [image_eq_zero_of_notMem_tsupport hy]

end GlobalTheory
end

open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothFun_integral_mul_right' : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [IsFiniteMeasure ν] (K : Set G), IsCompact K → ν Kᶜ = 0 → ∀ κ : G → ℂ, h.IsSmoothFun κ → h.IsSmoothFun (fun z => ∫ y, κ (z * y) ∂ν) := by
  atlas_forward_decl GlobalTheory.isSmoothFun_integral_mul_right
end

section
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.ConvSmooth

theorem secondCountable_units (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] : SecondCountableTopology 𝔸ˣ := by
  haveI : ProperSpace 𝔸 := FiniteDimensional.proper ℝ 𝔸
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem isSmoothFun_density {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) {L : Set G} (hL : IsCompact L)
    {κ : G → ℂ} (hκ : h.IsSmoothFun κ) {p : G → NNReal} (hp : Measurable p)
    (hpi : Integrable (fun y => (p y : ℝ)) μ) (hpL : ∀ y ∉ L, p y = 0) :
    h.IsSmoothFun (fun z => ∫ y, κ (z * y) * ((p y : ℝ) : ℂ) ∂μ) := by
  set ν := μ.withDensity (fun y => (p y : ENNReal)) with hν
  have hlt : ∫⁻ y, (p y : ENNReal) ∂μ < ⊤ := by
    have := hpi.lintegral_lt_top
    simpa using this
  haveI : IsFiniteMeasure ν := ⟨by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hlt⟩
  have hνL : ν Lᶜ = 0 := by
    rw [hν, withDensity_apply _ hL.isClosed.measurableSet.compl]
    have : ∀ y ∈ Lᶜ, (p y : ENNReal) = 0 := fun y hy => by simp [hpL y hy]
    rw [setLIntegral_congr_fun hL.isClosed.measurableSet.compl this]
    simp
  have key := GlobalTheory.T.isSmoothFun_integral_mul_right' 𝔸 G 𝔤 h ν L hL hνL κ hκ
  convert key using 2 with z
  rw [hν, integral_withDensity_eq_integral_smul hp]
  congr 1
  funext y
  rw [NNReal.smul_def, Complex.real_smul, mul_comm]

end GlobalTheory.ConvSmooth

namespace GlobalTheory.ConvSmooth

theorem posPart_decomp (w : ℂ) :
    w = (((Real.toNNReal w.re : NNReal) : ℝ) : ℂ) - (((Real.toNNReal (-w.re) : NNReal) : ℝ) : ℂ) +
      Complex.I * ((((Real.toNNReal w.im : NNReal) : ℝ) : ℂ) -
        (((Real.toNNReal (-w.im) : NNReal) : ℝ) : ℂ)) := by
  apply Complex.ext <;> simp [Real.coe_toNNReal', max_zero_sub_max_neg_zero_eq_self]

theorem conv_smooth_compactSupport : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ K : Set G, IsCompact K → ∀ κ a : G → ℂ, h.IsSmoothFun κ → HasCompactSupport κ → Measurable a → Integrable a μ → (∀ x ∉ K, a x = 0) → h.IsSmoothFun (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) ∧ HasCompactSupport (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) := by
  intro 𝔸 _ _ _ _ G 𝔤 h _ _ μ hμ K hK κ a hκ hκc ha hai haK
  haveI := h.locallyCompactSpace
  haveI := secondCountable_units 𝔸
  haveI : SecondCountableTopology G := Topology.IsInducing.subtypeVal.secondCountableTopology
  constructor
  · set b : G → ℂ := fun y => a y⁻¹ with hb
    have hbm : Measurable b := ha.comp measurable_inv
    have hbK : ∀ y ∉ K⁻¹, b y = 0 := fun y hy => haK _ (by simpa [Set.mem_inv] using hy)
    have hbi : Integrable b μ := by
      obtain ⟨B, hB⟩ := GlobalTheory.T.lintegral_inv_le_of_support_compact_alt G μ hμ K hK
      refine ⟨hbm.aestronglyMeasurable, ?_⟩
      have h1 := hB (fun x => ‖a x‖ₑ) ha.enorm (fun x hx => by simp [haK x hx])
      exact lt_of_le_of_lt h1 (ENNReal.mul_lt_top ENNReal.coe_lt_top hai.2)
    have hcv : ∀ z, ∫ x, κ x * a (x⁻¹ * z) ∂μ = ∫ y, κ (z * y) * b y ∂μ := by
      intro z
      rw [← integral_mul_left_eq_self (fun x => κ x * a (x⁻¹ * z)) z]
      congr 1; funext y; simp [hb, mul_inv_rev, mul_assoc]
    have hκcont : Continuous κ := by
      letI := h.chartedSpace
      exact ContMDiff.continuous hκ
    obtain ⟨C, hC⟩ := hκcont.bounded_above_of_compact_support hκc
    have hre : Integrable (fun y => (b y).re) μ := by simpa using hbi.re
    have him : Integrable (fun y => (b y).im) μ := by simpa using hbi.im
    have hpos : ∀ f : G → ℝ, Integrable f μ → Integrable (fun y => ((Real.toNNReal (f y) : NNReal) : ℝ)) μ :=
      fun f hf => by simpa [Real.coe_toNNReal'] using hf.pos_part
    have hK' : IsCompact K⁻¹ := hK.inv
    have hre' : Integrable (fun y => -(b y).re) μ := hre.neg
    have him' : Integrable (fun y => -(b y).im) μ := him.neg
    have S : ∀ f : G → ℝ, Measurable f → Integrable f μ → (∀ y ∉ K⁻¹, f y = 0) →
        h.IsSmoothFun (fun z => ∫ y, κ (z * y) * (((Real.toNNReal (f y) : NNReal) : ℝ) : ℂ) ∂μ) :=
      fun f hfm hf hf0 => isSmoothFun_density h μ hK' hκ hfm.real_toNNReal (hpos f hf)
        (fun y hy => by simp [hf0 y hy])
    have hbre : ∀ y ∉ K⁻¹, (b y).re = 0 := fun y hy => by simp [hbK y hy]
    have hbim : ∀ y ∉ K⁻¹, (b y).im = 0 := fun y hy => by simp [hbK y hy]
    have s1 := S _ (Complex.measurable_re.comp hbm) hre hbre
    have s2 := S _ (Complex.measurable_re.comp hbm).neg hre' (fun y hy => by simp [hbre y hy])
    have s3 := S _ (Complex.measurable_im.comp hbm) him hbim
    have s4 := S _ (Complex.measurable_im.comp hbm).neg him' (fun y hy => by simp [hbim y hy])
    have hI : ∀ (z : G) (f : G → ℝ), Integrable f μ →
        Integrable (fun y => κ (z * y) * (((Real.toNNReal (f y) : NNReal) : ℝ) : ℂ)) μ := by
      intro z f hf
      refine ((hpos f hf).ofReal (𝕜 := ℂ)).bdd_mul (hκcont.comp (continuous_const_mul z)).aestronglyMeasurable (ae_of_all _ fun y => hC _)
    have hsum : (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) =
        (fun z => ∫ y, κ (z * y) * (((Real.toNNReal (b y).re : NNReal) : ℝ) : ℂ) ∂μ) -
        (fun z => ∫ y, κ (z * y) * (((Real.toNNReal (-(b y).re) : NNReal) : ℝ) : ℂ) ∂μ) +
        Complex.I • ((fun z => ∫ y, κ (z * y) * (((Real.toNNReal (b y).im : NNReal) : ℝ) : ℂ) ∂μ) -
        (fun z => ∫ y, κ (z * y) * (((Real.toNNReal (-(b y).im) : NNReal) : ℝ) : ℂ) ∂μ)) := by
      funext z
      rw [hcv z]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have e : (fun y => κ (z * y) * b y) = fun y =>
          (κ (z * y) * (((Real.toNNReal (b y).re : NNReal) : ℝ) : ℂ) -
            κ (z * y) * (((Real.toNNReal (-(b y).re) : NNReal) : ℝ) : ℂ)) +
          Complex.I * (κ (z * y) * (((Real.toNNReal (b y).im : NNReal) : ℝ) : ℂ) -
            κ (z * y) * (((Real.toNNReal (-(b y).im) : NNReal) : ℝ) : ℂ)) := by
        funext y
        conv_lhs => rw [posPart_decomp (b y)]
        ring
      rw [e, integral_add ?_ ?_, integral_sub ?_ ?_, integral_const_mul, integral_sub ?_ ?_]
      all_goals first
        | exact hI z _ hre | exact hI z _ hre' | exact hI z _ him | exact hI z _ him'
        | exact (hI z _ hre).sub (hI z _ hre')
        | exact ((hI z _ him).sub (hI z _ him')).const_mul _
    rw [← h.mem_smoothFuns, hsum]
    exact Submodule.add_mem _ (Submodule.sub_mem _ s1 s2)
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ s3 s4))
  · refine HasCompactSupport.intro (hκc.mul hK) fun z hz => ?_
    have : (fun x => κ x * a (x⁻¹ * z)) = 0 := by
      funext x
      by_cases hx : x ∈ tsupport κ
      · have : x⁻¹ * z ∉ K := fun h' => hz ⟨x, hx, x⁻¹ * z, h', by simp⟩
        simp [haK _ this]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    simp only [this]; exact integral_zero' ..

end GlobalTheory.ConvSmooth
end

open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_hasCompactSupport_conv_of_integrable_compact : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ K : Set G, IsCompact K → ∀ κ a : G → ℂ, h.IsSmoothFun κ → HasCompactSupport κ → Measurable a → Integrable a μ → (∀ x ∉ K, a x = 0) → h.IsSmoothFun (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) ∧ HasCompactSupport (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) := by
  atlas_forward_decl GlobalTheory.ConvSmooth.conv_smooth_compactSupport
end

section
section
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem smFn_contDiff_line :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ l i, ∀ f ∈ S, ContDiff ℝ ∞ (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) ∧ ∀ (p : ℕ) (s : ℝ), iteratedDeriv p (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) s = Λ (List.replicate p i ++ l) fun y => f (h.expG (s • b i) * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ _ S _ hS K _ Λ hΛ l i f hf
  have hd : ∀ (l : List (Fin d)) (s : ℝ), HasDerivAt (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y))
      (Λ (i :: l) fun y => f (h.expG (s • b i) * y)) s := by
    intro l s
    have h1 := hΛ.der l i _ (hS f hf (h.expG (s • b i)))
    have h2 : HasDerivAt (fun t : ℝ => Λ l fun y => f (h.expG ((s + t) • b i) * y))
        (Λ (i :: l) fun y => f (h.expG (s • b i) * y)) (s - s) := by
      rw [sub_self]
      simpa only [h.expG_add_smul, mul_assoc] using h1
    have h3 := h2.comp_sub_const s s
    simpa only [add_sub_cancel] using h3
  have hi : ∀ p : ℕ, iteratedDeriv p (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y))
      = fun s : ℝ => Λ (List.replicate p i ++ l) fun y => f (h.expG (s • b i) * y) := by
    intro p
    induction p with
    | zero => simp
    | succ p ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      rw [(hd _ s).deriv, List.replicate_succ, List.cons_append]
  refine ⟨contDiff_of_differentiable_iteratedDeriv fun m _ => ?_, fun p s => by rw [hi p]⟩
  rw [hi m]
  exact fun s => (hd _ s).differentiableAt

end GlobalTheory.HCA
end

open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedDerivFunctional_contDiff_expLine : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ l i, ∀ f ∈ S, ContDiff ℝ ∞ (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) ∧ ∀ (p : ℕ) (s : ℝ), iteratedDeriv p (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) s = Λ (List.replicate p i ++ l) fun y => f (h.expG (s • b i) * y) := by
  atlas_forward_decl GlobalTheory.HCA.smFn_contDiff_line
end

section
section
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem smFn_tsum_replicate : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ i, ∃ M : ℕ → ℝ, (∀ p, 0 ≤ M p) ∧ (∀ p, ∀ f ∈ S, ‖Λ (List.replicate p i) f‖ ≤ M p * ∫ x in K, ‖f x‖ ∂μ) ∧ ∀ c : ℕ → ℝ, Summable (fun p => |c p| * M p) → SmFn h b μ S K fun l f => ∑' p, (c p : ℂ) * Λ (l ++ List.replicate p i) f := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hSc hSL K hK Λ hΛ i
  classical
  haveI := hμ
  choose C0 hC0 using hΛ.bdd
  let C : List (Fin d) → ℝ := fun l => max 0 (C0 l)
  have hC0' : ∀ l, 0 ≤ C l := fun l => le_max_left _ _
  have hC : ∀ l, ∀ f ∈ S, ‖Λ l f‖ ≤ C l * ∫ x in K, ‖f x‖ ∂μ := by
    intro l f hf
    have hI : 0 ≤ ∫ x in K, ‖f x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
    exact (hC0 l f hf).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hI)
  let D : ℕ → ℕ → ℝ := fun p k =>
    C (((Encodable.decode k : Option (List (Fin d))).getD []) ++ List.replicate p i)
  let M : ℕ → ℝ := fun p => C (List.replicate p i) + ∑ k ∈ Finset.range (p + 1), D p k
  have hD0 : ∀ p k, 0 ≤ D p k := fun p k => hC0' _
  have hM0 : ∀ p, 0 ≤ M p := fun p => add_nonneg (hC0' _) (Finset.sum_nonneg fun k _ => hD0 p k)
  have hMl : ∀ l : List (Fin d), ∀ p, Encodable.encode l ≤ p → C (l ++ List.replicate p i) ≤ M p := by
    intro l p hp
    have h1 : D p (Encodable.encode l) ≤ ∑ k ∈ Finset.range (p + 1), D p k :=
      Finset.single_le_sum (f := D p) (fun k _ => hD0 p k) (Finset.mem_range.2 (Nat.lt_succ_of_le hp))
    have h2 : D p (Encodable.encode l) = C (l ++ List.replicate p i) := by
      simp only [D, Encodable.encodek, Option.getD_some]
    have h3 := hC0' (List.replicate p i)
    simp only [M]
    linarith
  refine ⟨M, hM0, ?_, ?_⟩
  · intro p f hf
    refine (hC _ f hf).trans (mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun _ => norm_nonneg _))
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hD0 p k)
  intro c hc
  have hsum : ∀ l, Summable (fun p => |c p| * C (l ++ List.replicate p i)) := by
    intro l
    refine Summable.of_norm_bounded_eventually_nat hc ?_
    filter_upwards [Filter.eventually_ge_atTop (Encodable.encode l)] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (hC0' _))]
    exact mul_le_mul_of_nonneg_left (hMl l p hp) (abs_nonneg _)
  have hterm : ∀ l, ∀ f ∈ S, ∀ p, ‖(c p : ℂ) * Λ (l ++ List.replicate p i) f‖ ≤
      |c p| * C (l ++ List.replicate p i) * ∫ x in K, ‖f x‖ ∂μ := by
    intro l f hf p
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC _ f hf) (abs_nonneg _)
  have hsumm : ∀ l, ∀ f ∈ S, Summable (fun p => (c p : ℂ) * Λ (l ++ List.replicate p i) f) :=
    fun l f hf => Summable.of_norm_bounded ((hsum l).mul_right _) (hterm l f hf)
  have hexp0 : h.expG 0 = 1 := by
    apply Subtype.ext; apply Units.ext; simp
  refine ⟨?_, ?_, ?_⟩
  · intro l f hf f' hf' a
    have e : ∀ p, (c p : ℂ) * Λ (l ++ List.replicate p i) (a • f + f') =
        a * ((c p : ℂ) * Λ (l ++ List.replicate p i) f) + (c p : ℂ) * Λ (l ++ List.replicate p i) f' := by
      intro p; rw [hΛ.lin _ f hf f' hf' a]; ring
    simp_rw [e]
    rw [Summable.tsum_add ((hsumm l f hf).mul_left a) (hsumm l f' hf'), tsum_mul_left]
  · intro l
    refine ⟨∑' p, |c p| * C (l ++ List.replicate p i), fun f hf => ?_⟩
    rw [← tsum_mul_right]
    exact tsum_of_norm_bounded ((hsum l).mul_right _).hasSum (hterm l f hf)
  · intro l j f hf
    have hft : ∀ t : ℝ, (fun y => f (h.expG (t • b j) * y)) ∈ S := fun t => hSL f hf _
    have hcont : Continuous fun q : ℝ × G => f (h.expG (q.1 • b j) * q.2) :=
      (hSc f hf).comp ((h.continuous_expG.comp (continuous_fst.smul continuous_const)).mul continuous_snd)
    obtain ⟨A, hA⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod hK).exists_bound_of_continuousOn
      hcont.continuousOn
    have hB : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∫ x in K, ‖f (h.expG (t • b j) * x)‖ ∂μ ≤ max 0 A * μ.real K := by
      intro t ht
      have h1 := norm_setIntegral_le_of_norm_le_const (μ := μ) (C := max 0 A)
        (f := fun x => ‖f (h.expG (t • b j) * x)‖) hK.measure_lt_top (fun x hx => by
          rw [norm_norm]; exact (hA (t, x) ⟨ht, hx⟩).trans (le_max_right _ _))
      exact (Real.le_norm_self _).trans h1
    have hderiv : ∀ (m : List (Fin d)) (t : ℝ), HasDerivAt (fun s : ℝ => Λ m fun y => f (h.expG (s • b j) * y))
        (Λ (j :: m) fun y => f (h.expG (t • b j) * y)) t := by
      intro m t
      have h0 := hΛ.der m j _ (hft t)
      have e1 : (fun s : ℝ => Λ m fun y => f (h.expG (t • b j) * (h.expG (s • b j) * y))) =
          fun s => Λ m fun y => f (h.expG ((t + s) • b j) * y) := by
        funext s; congr 1; funext y; rw [h.expG_add_smul, mul_assoc]
      rw [e1] at h0
      have h1 : HasDerivAt (fun s : ℝ => Λ m fun y => f (h.expG ((t + s) • b j) * y))
          (Λ (j :: m) fun y => f (h.expG (t • b j) * y)) (t - t) := by rw [sub_self]; exact h0
      have h2 := h1.comp_sub_const t t
      have e2 : ∀ u : ℝ, t + (u - t) = u := fun u => by ring
      simp only [e2] at h2
      exact h2
    have key := hasDerivAt_tsum_of_isPreconnected (t := Set.Ioo (-1 : ℝ) 1) (y₀ := 0) (y := 0)
      (g := fun p s => (c p : ℂ) * Λ (l ++ List.replicate p i) fun y => f (h.expG (s • b j) * y))
      (g' := fun p s => (c p : ℂ) * Λ (j :: (l ++ List.replicate p i)) fun y => f (h.expG (s • b j) * y))
      (u := fun p => |c p| * C ((j :: l) ++ List.replicate p i) * (max 0 A * μ.real K))
      ((hsum (j :: l)).mul_right _) isOpen_Ioo isPreconnected_Ioo
      (fun p s _ => (hderiv _ s).const_mul _)
      (fun p s hs => (hterm (j :: l) _ (hft s) p).trans
        (mul_le_mul_of_nonneg_left (hB s (Set.Ioo_subset_Icc_self hs)) (mul_nonneg (abs_nonneg _) (hC0' _))))
      (by norm_num) (hsumm l _ (hft 0)) (by norm_num)
    simp only [zero_smul, hexp0, one_mul] at key
    exact key

end GlobalTheory.HCA
end

open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedDerivFunctional_tsum_replicate : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ i, ∃ M : ℕ → ℝ, (∀ p, 0 ≤ M p) ∧ (∀ p, ∀ f ∈ S, ‖Λ (List.replicate p i) f‖ ≤ M p * ∫ x in K, ‖f x‖ ∂μ) ∧ ∀ c : ℕ → ℝ, Summable (fun p => |c p| * M p) → SmFn h b μ S K fun l f => ∑' p, (c p : ℂ) * Λ (l ++ List.replicate p i) f := by
  atlas_forward_decl GlobalTheory.HCA.smFn_tsum_replicate
end

section
section
noncomputable section

open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic Set
open scoped ContDiff

namespace GlobalTheory.HCA

theorem smFn_dixmierMalliavin_step : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ (i : Fin d) (ε : ℝ), 0 < ε → ∃ (Λ' : List (Fin d) → (G → ℂ) → ℂ) (u v : ℝ → ℂ), SmFn h b μ S K Λ' ∧ ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ v ∧ tsupport u ⊆ Set.Icc (-ε) ε ∧ tsupport v ⊆ Set.Icc (-ε) ε ∧ ∀ f ∈ S, Λ [] f = (∫ t, u t * Λ' [] fun y => f (h.expG (t • b i) * y)) + ∫ t, v t * Λ [] fun y => f (h.expG (t • b i) * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hcont hinv K hK Λ hΛ i ε hε
  obtain ⟨M, hM0, hMb, hser⟩ := GlobalTheory.T.boundedDerivFunctional_tsum_replicate 𝔸 G 𝔤 h d b μ hμ S hcont hinv K hK Λ hΛ i
  obtain ⟨c, u, v, hu, hv, hus, hvs, hc, hid⟩ := exists_dixmierMalliavin_line M hε
  refine ⟨fun l f => ∑' p, (c p : ℂ) * Λ (l ++ List.replicate p i) f, u, v,
    hser c hc, hu, hv, hus, hvs, fun f hf => ?_⟩
  have hmem : ∀ t : ℝ, (fun y => f (h.expG (t • b i) * y)) ∈ S := fun t => hinv f hf _
  set F : ℝ → ℂ := fun t => Λ [] fun y => f (h.expG (t • b i) * y) with hFdef
  obtain ⟨hF, hD'⟩ := GlobalTheory.T.boundedDerivFunctional_contDiff_expLine 𝔸 G 𝔤 h d b μ hμ S hcont hinv K hK Λ hΛ [] i f hf
  have hD : ∀ p t, iteratedDeriv p F t = Λ (List.replicate p i) fun y => f (h.expG (t • b i) * y) := by
    intro p t; rw [hD' p t, List.append_nil]

  have hfc : Continuous f := hcont f hf
  have hjc : Continuous fun q : ℝ × G => f (h.expG (q.1 • b i) * q.2) :=
    hfc.comp ((h.continuous_expG.comp (continuous_fst.smul continuous_const)).mul continuous_snd)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hjc.continuousOn
  set B : ℝ := max C 0 * μ.real K with hB
  have hB0 : 0 ≤ B := mul_nonneg (le_max_right _ _) measureReal_nonneg
  have hKint : ∀ t ∈ Icc (-ε) ε, (∫ x in K, ‖f (h.expG (t • b i) * x)‖ ∂μ) ≤ B := by
    intro t ht
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := K) (C := max C 0)
      (f := fun x => ‖f (h.expG (t • b i) * x)‖) hK.measure_lt_top (fun x hx => by
        rw [norm_norm]; exact (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _))
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)] at this
    exact this
  have hDb : ∀ p, ∀ t ∈ Icc (-ε) ε, ‖iteratedDeriv p F t‖ ≤ M p * B := by
    intro p t ht
    rw [hD]
    exact (hMb p _ (hmem t)).trans (mul_le_mul_of_nonneg_left (hKint t ht) (hM0 p))

  set a : ℂ := ((B + 1 : ℝ) : ℂ)⁻¹ with ha
  have hB1 : (0 : ℝ) < B + 1 := by linarith
  have ha0 : a ≠ 0 := inv_ne_zero (by exact_mod_cast hB1.ne')
  have hFa : ContDiff ℝ ∞ fun t => a * F t := contDiff_const.mul hF
  have hDa : ∀ p t, iteratedDeriv p (fun t => a * F t) t = a * iteratedDeriv p F t := by
    intro p t
    exact iteratedDeriv_const_mul a (hF.contDiffAt.of_le (by exact_mod_cast le_top))
  have key := hid (fun t => a * F t) hFa (fun p t ht => by
    rw [hDa, norm_mul, ha, norm_inv, Complex.norm_real, Real.norm_of_nonneg hB1.le]
    rw [inv_mul_le_iff₀ hB1]
    calc ‖iteratedDeriv p F t‖ ≤ M p * B := hDb p t ht
      _ ≤ (B + 1) * M p := by nlinarith [hM0 p])
  simp_rw [hDa] at key
  have e1 : ∀ p, (c p : ℂ) * ∫ t, a * iteratedDeriv p F t * u t = a * ((c p : ℂ) * ∫ t, iteratedDeriv p F t * u t) := by
    intro p
    simp_rw [mul_assoc a, integral_const_mul]; ring
  have e2 : ∫ t, a * F t * v t = a * ∫ t, F t * v t := by
    rw [← integral_const_mul a]; simp_rw [mul_assoc]
  simp_rw [e1] at key
  rw [e2, tsum_mul_left, ← mul_add] at key
  have key' := mul_left_cancel₀ ha0 key
  have hF0 : F 0 = Λ [] f := by
    simp only [hFdef, zero_smul]; rw [h.expG_zero]; simp only [one_mul]
  rw [← hF0, key']
  congr 1
  · have hugc : HasCompactSupport u := isCompact_Icc.of_isClosed_subset (isClosed_tsupport u) hus
    have hcD : ∀ p, Continuous (fun t => iteratedDeriv p F t) := fun p =>
      hF.continuous_iteratedDeriv p (by exact_mod_cast le_top)
    let T : ℕ → ℝ → ℂ := fun p t => (c p : ℂ) * (iteratedDeriv p F t * u t)
    have hTi : ∀ p, Integrable (T p) := fun p =>
      (((hcD p).mul hu.continuous).integrable_of_hasCompactSupport hugc.mul_left).const_mul _
    have hTb : ∀ p t, ‖T p t‖ ≤ |c p| * M p * (B * ‖u t‖) := by
      intro p t
      by_cases ht : t ∈ tsupport u
      · simp only [T, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have := hDb p t (hus ht)
        calc |c p| * (‖iteratedDeriv p F t‖ * ‖u t‖) ≤ |c p| * ((M p * B) * ‖u t‖) := by gcongr
          _ = |c p| * M p * (B * ‖u t‖) := by ring
      · have hu0 : u t = 0 := image_eq_zero_of_notMem_tsupport ht
        simp only [T, hu0, mul_zero, norm_zero, le_refl]
    have hgi : Integrable (fun t => B * ‖u t‖) :=
      (hu.continuous.integrable_of_hasCompactSupport hugc).norm.const_mul _
    have hsum : Summable fun p => ∫ t, ‖T p t‖ := by
      refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _)
        (fun p => ?_) (hc.mul_right (∫ t, B * ‖u t‖))
      rw [← integral_const_mul]
      exact integral_mono (hTi p).norm (hgi.const_mul _) (fun t => hTb p t)
    have e3 : ∀ p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * u t = ∫ t, T p t := fun p =>
      (integral_const_mul _ _).symm
    simp_rw [e3]
    rw [integral_tsum_of_summable_integral_norm hTi hsum]
    congr 1
    funext t
    simp only [T, hD, List.nil_append]
    rw [← tsum_mul_left]
    congr 1
    funext p
    ring
  · congr 1; funext t; rw [mul_comm]

end GlobalTheory.HCA

end
end

open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dixmierMalliavin_factorisation_basis_step : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ (i : Fin d) (ε : ℝ), 0 < ε → ∃ (Λ' : List (Fin d) → (G → ℂ) → ℂ) (u v : ℝ → ℂ), SmFn h b μ S K Λ' ∧ ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ v ∧ tsupport u ⊆ Set.Icc (-ε) ε ∧ tsupport v ⊆ Set.Icc (-ε) ε ∧ ∀ f ∈ S, Λ [] f = (∫ t, u t * Λ' [] fun y => f (h.expG (t • b i) * y)) + ∫ t, v t * Λ [] fun y => f (h.expG (t • b i) * y) := by
  atlas_forward_decl GlobalTheory.HCA.smFn_dixmierMalliavin_step
end

section
section
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem integrable_integral_fin_cons {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {F : (Fin (n + 1) → ℝ) → E} (hF : Integrable F) :
    Integrable (fun s : ℝ => ∫ t', F (Fin.cons s t')) := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hint : Integrable (fun p : ℝ × (Fin n → ℝ) =>
      F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p))
      ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin n => (volume : Measure ℝ))) :=
    (hmp.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  refine hint.integral_prod_left.congr (ae_of_all _ fun s => ?_)
  simp only
  congr 1; funext t'
  congr 1
  simp [MeasurableEquiv.piFinSuccAbove]
  rfl

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem prodExp_fin_succ (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin (n + 1) → 𝔤) (t : Fin (n + 1) → ℝ) :
    h.prodExp X t = h.expG (t 0 • X 0) * h.prodExp (Fin.tail X) (Fin.tail t) := by
  simp [IsExpLieAlgebra.prodExp, List.ofFn_succ, Fin.tail]

theorem integral_mul_sum_cons_kernel (h : IsExpLieAlgebra G 𝔤) {n N : ℕ} (X : Fin (n + 1) → 𝔤) {ε : ℝ}
    (hε : 0 ≤ ε) {u : ℝ → ℂ} (hu : Continuous u) (hus : tsupport u ⊆ Set.Icc (-ε) ε)
    {κ : Fin N → (Fin n → ℝ) → ℂ} (hκ : ∀ m, Continuous (κ m))
    (hκs : ∀ m, tsupport (κ m) ⊆ Metric.closedBall 0 ε) {Φ : Fin N → G → ℂ}
    (hΦ : ∀ m, Continuous (Φ m)) (Ψ : ℝ → ℂ)
    (hΨ : ∀ s, Ψ s = ∑ m, ∫ t', κ m t' * Φ m (h.expG (s • X 0) * h.prodExp (Fin.tail X) t')) :
    ∫ s, u s * Ψ s = ∑ m, ∫ t, u (t 0) * κ m (Fin.tail t) * Φ m (h.prodExp X t) := by
  have hF : ∀ m, Integrable (fun t : Fin (n + 1) → ℝ => u (t 0) * κ m (Fin.tail t) * Φ m (h.prodExp X t)) := by
    intro m
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hu.comp (continuous_apply 0)).mul
        ((hκ m).comp (continuous_pi fun j => continuous_apply j.succ))).mul
        ((hΦ m).comp (h.continuous_prodExp X))
    · exact HasCompactSupport.mul_right (f := fun t : Fin (n + 1) → ℝ => u (t 0) * κ m (Fin.tail t))
        ((isCompact_closedBall 0 ε).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_cons_kernel hε hus (hκs m)))
  have heq : ∀ m s, u s * ∫ t', κ m t' * Φ m (h.expG (s • X 0) * h.prodExp (Fin.tail X) t') =
      ∫ t', u ((Fin.cons s t' : Fin (n + 1) → ℝ) 0) * κ m (Fin.tail (Fin.cons s t' : Fin (n + 1) → ℝ)) *
        Φ m (h.prodExp X (Fin.cons s t')) := by
    intro m s
    rw [← integral_const_mul]
    congr 1; funext t'
    simp only [Fin.cons_zero, Fin.tail_cons, prodExp_fin_succ h X, mul_assoc]
  simp_rw [hΨ, Finset.mul_sum]
  rw [integral_finsetSum _ (fun m _ => by
    simp_rw [heq m]; exact integrable_integral_fin_cons (hF m))]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp_rw [heq m]
  exact (integral_fin_succ_cons (hF m)).symm

end GlobalTheory.HCA

namespace GlobalTheory.HCA

theorem SmFn.exists_decomp_prodExp : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (j : Fin n → Fin d) (Λ : List (Fin d) → (G → ℂ) → ℂ), SmFn h b μ S K Λ → ∃ (N : ℕ) (Λ' : Fin N → List (Fin d) → (G → ℂ) → ℂ) (κ : Fin N → (Fin n → ℝ) → ℂ), (∀ m, SmFn h b μ S K (Λ' m) ∧ ContDiff ℝ ∞ (κ m) ∧ tsupport (κ m) ⊆ Metric.closedBall 0 ε) ∧ ∀ f ∈ S, Λ [] f = ∑ m, ∫ t, κ m t * Λ' m [] fun y => f (h.prodExp (fun k => b (j k)) t * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hS hL K hK ε hε n
  induction n with
  | zero =>
    intro j Λ hΛ
    refine ⟨1, fun _ => Λ, fun _ _ => 1, fun _ => ⟨hΛ, contDiff_const, ?_⟩, fun f hf => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      have hP : ∀ t : Fin 0 → ℝ, h.prodExp (fun k => b (j k)) t = 1 := fun t => by
        simp [IsExpLieAlgebra.prodExp]
      simp [hP, hv]
  | succ n ih =>
    intro j Λ hΛ
    obtain ⟨Λ', u, v, hΛ', hu, hv, hus, hvs, hdec⟩ :=
      GlobalTheory.T.dixmierMalliavin_factorisation_basis_step 𝔸 G 𝔤 h d b μ hμ S hS hL K hK Λ hΛ (j 0) ε hε
    obtain ⟨N₁, Λ₁, κ₁, h₁, hd₁⟩ := ih (Fin.tail j) Λ' hΛ'
    obtain ⟨N₂, Λ₂, κ₂, h₂, hd₂⟩ := ih (Fin.tail j) Λ hΛ
    refine ⟨N₁ + N₂, Fin.append Λ₁ Λ₂,
      Fin.append (fun m t => u (t 0) * κ₁ m (Fin.tail t)) (fun m t => v (t 0) * κ₂ m (Fin.tail t)),
      ?_, ?_⟩
    · intro m
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · simp only [Fin.append_left]
        exact ⟨(h₁ m).1, contDiff_cons_kernel hu (h₁ m).2.1, tsupport_cons_kernel hε.le hus (h₁ m).2.2⟩
      · simp only [Fin.append_right]
        exact ⟨(h₂ m).1, contDiff_cons_kernel hv (h₂ m).2.1, tsupport_cons_kernel hε.le hvs (h₂ m).2.2⟩
    · intro f hf
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hdec f hf]
      have hc : ∀ (Λ₀ : List (Fin d) → (G → ℂ) → ℂ), SmFn h b μ S K Λ₀ →
          Continuous fun x : G => Λ₀ [] fun y => f (x * y) := fun Λ₀ hΛ₀ =>
        SmFn.continuous_leftTranslate 𝔸 G 𝔤 h d b μ hμ S hS hL K hK Λ₀ hΛ₀ [] f hf
      congr 1
      · exact integral_mul_sum_cons_kernel h (fun k => b (j k)) hε.le hu.continuous hus
          (fun m => (h₁ m).2.1.continuous) (fun m => (h₁ m).2.2)
          (Φ := fun m x => Λ₁ m [] fun y => f (x * y)) (fun m => hc _ (h₁ m).1) _
          (fun s => by
            rw [hd₁ _ (hL f hf _)]
            simp only [mul_assoc]
            rfl)
      · exact integral_mul_sum_cons_kernel h (fun k => b (j k)) hε.le hv.continuous hvs
          (fun m => (h₂ m).2.1.continuous) (fun m => (h₂ m).2.2)
          (Φ := fun m x => Λ₂ m [] fun y => f (x * y)) (fun m => hc _ (h₂ m).1) _
          (fun s => by
            rw [hd₂ _ (hL f hf _)]
            simp only [mul_assoc]
            rfl)

end GlobalTheory.HCA
end

open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dixmierMalliavin_decomp_prodExp : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (j : Fin n → Fin d) (Λ : List (Fin d) → (G → ℂ) → ℂ), SmFn h b μ S K Λ → ∃ (N : ℕ) (Λ' : Fin N → List (Fin d) → (G → ℂ) → ℂ) (κ : Fin N → (Fin n → ℝ) → ℂ), (∀ m, SmFn h b μ S K (Λ' m) ∧ ContDiff ℝ ∞ (κ m) ∧ tsupport (κ m) ⊆ Metric.closedBall 0 ε) ∧ ∀ f ∈ S, Λ [] f = ∑ m, ∫ t, κ m t * Λ' m [] fun y => f (h.prodExp (fun k => b (j k)) t * y) := by
  atlas_forward_decl GlobalTheory.HCA.SmFn.exists_decomp_prodExp
end

section
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_leftTranslate_boundedDerivFunctional : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ l, ∀ f ∈ S, Continuous fun x : G => Λ l fun y => f (x * y) := by
  first | exact @GlobalTheory.HCA.SmFn.continuous_leftTranslate | exact GlobalTheory.HCA.SmFn.continuous_leftTranslate | (intros; apply GlobalTheory.HCA.SmFn.continuous_leftTranslate <;> assumption)
end

section
section
open MeasureTheory

namespace GlobalTheory

theorem exists_integrable_density_of_bound_by_integral_compact : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (K : Set X), IsCompact K → μ K < ⊤ → ∀ (S : Submodule ℂ (X → ℂ)), (∀ f ∈ S, Continuous f) → ∀ (Λ : (X → ℂ) → ℂ) (C : ℝ), (∀ f ∈ S, ∀ f' ∈ S, ∀ c : ℂ, Λ (c • f + f') = c * Λ f + Λ f') → (∀ f ∈ S, ‖Λ f‖ ≤ C * ∫ x in K, ‖f x‖ ∂μ) → ∃ a : X → ℂ, Measurable a ∧ Integrable a μ ∧ (∀ x ∉ K, a x = 0) ∧ ∀ f ∈ S, ∫ x, f x * a x ∂μ = Λ f := by
  intro X _ _ _ _ μ K hK hμK S hS Λ C hlin hbd
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set ν := μ.restrict K with hν
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hμK.ne
  have hmem : ∀ f : S, MemLp (f : X → ℂ) 2 ν := by
    intro f
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hS f f.2).continuousOn
    exact MemLp.of_bound (hS f f.2).aestronglyMeasurable M
      ((ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall hM))
  let T : S →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun f => (hmem f).toLp _
      map_add' := fun f g => MemLp.toLp_add (hmem f) (hmem g)
      map_smul' := fun c f => MemLp.toLp_const_smul c (hmem f) }
  have hT : ∀ f : S, T f = (hmem f).toLp _ := fun f => rfl
  have hΛ0 : Λ 0 = 0 := by
    have := hlin 0 S.zero_mem 0 S.zero_mem 1
    simpa using this
  let Λ' : S →ₗ[ℂ] ℂ :=
    { toFun := fun f => Λ f
      map_add' := fun f g => by
        have := hlin f f.2 g g.2 1
        simpa using this
      map_smul' := fun c f => by
        have := hlin f f.2 0 S.zero_mem c
        simpa [hΛ0] using this }
  have hΛ' : ∀ f : S, Λ' f = Λ f := fun f => rfl

  have hkey : ∀ f : S, ∫ x in K, ‖(f : X → ℂ) x‖ ∂μ ≤ ((ν Set.univ) ^ (1/2 : ℝ)).toReal * ‖T f‖ := by
    intro f
    have h12 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (μ := ν)
      (by norm_num) (hS f f.2).aestronglyMeasurable
    have hexp : (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) = (1 / 2 : ℝ) := by norm_num
    rw [hexp] at h12
    have hint : ∫ x in K, ‖(f : X → ℂ) x‖ ∂μ = (eLpNorm (f : X → ℂ) 1 ν).toReal := by
      rw [integral_norm_eq_lintegral_enorm (hS f f.2).aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm]
    have hfin : eLpNorm (f : X → ℂ) 2 ν * ν Set.univ ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.mul_ne_top (hmem f).eLpNorm_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _))
    rw [hint, hT, Lp.norm_toLp]
    calc _ ≤ (eLpNorm (f : X → ℂ) 2 ν * ν Set.univ ^ (1 / 2 : ℝ)).toReal :=
          ENNReal.toReal_mono hfin h12
      _ = _ := by rw [ENNReal.toReal_mul, mul_comm]
  set B : ℝ := max C 0 * ((ν Set.univ) ^ (1/2 : ℝ)).toReal with hBdef
  have hB : ∀ f : S, ‖Λ' f‖ ≤ B * ‖T f‖ := by
    intro f
    have hI0 : 0 ≤ ∫ x in K, ‖(f : X → ℂ) x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
    rw [hΛ']
    calc ‖Λ f‖ ≤ C * ∫ x in K, ‖(f : X → ℂ) x‖ ∂μ := hbd f f.2
      _ ≤ max C 0 * ∫ x in K, ‖(f : X → ℂ) x‖ ∂μ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hI0
      _ ≤ max C 0 * (((ν Set.univ) ^ (1/2 : ℝ)).toReal * ‖T f‖) :=
          mul_le_mul_of_nonneg_left (hkey f) (le_max_right _ _)
      _ = B * ‖T f‖ := by rw [hBdef, mul_assoc]
  have hker : LinearMap.ker T ≤ LinearMap.ker Λ' := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    have := hB f
    rw [hf, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let φ₀ : LinearMap.range T →ₗ[ℂ] ℂ :=
    ((LinearMap.ker T).liftQ Λ' hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hφ₀ : ∀ f : S, φ₀ ⟨T f, LinearMap.mem_range_self T f⟩ = Λ f := by
    intro f
    have h1 : T.quotKerEquivRange.symm ⟨T f, LinearMap.mem_range_self T f⟩
        = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [φ₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h1,
      Submodule.liftQ_apply, hΛ']
  have hφb : ∀ v, ‖φ₀ v‖ ≤ B * ‖v‖ := by
    rintro ⟨v, f, rfl⟩
    have := hφ₀ f
    rw [this, ← hΛ']
    exact hB f
  let φ : StrongDual ℂ (LinearMap.range T) := φ₀.mkContinuous B hφb
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range T) φ
  set a₀ : Lp ℂ 2 ν := (InnerProductSpace.toDual ℂ (Lp ℂ 2 ν)).symm g with ha₀
  have hrep : ∀ f : S, inner ℂ a₀ (T f) = Λ f := by
    intro f
    rw [ha₀, InnerProductSpace.toDual_symm_apply]
    have := hg ⟨T f, LinearMap.mem_range_self T f⟩
    rw [this]
    simp only [φ, LinearMap.mkContinuous_apply]
    exact hφ₀ f
  have hm : Measurable (a₀ : X → ℂ) := (Lp.stronglyMeasurable a₀).measurable
  refine ⟨K.indicator (fun x => starRingEnd ℂ (a₀ x)),
    (Complex.continuous_conj.measurable.comp hm).indicator hKm, ?_, ?_, ?_⟩
  · rw [integrable_indicator_iff hKm]
    have : Integrable (a₀ : X → ℂ) ν := (Lp.memLp a₀).integrable (by norm_num)
    exact this.mono (Complex.continuous_conj.comp_aestronglyMeasurable this.1)
      (Filter.Eventually.of_forall fun x => by simp)
  · intro x hx
    exact Set.indicator_of_notMem hx _
  · intro f hf
    have key := hrep ⟨f, hf⟩
    rw [L2.inner_def] at key
    have hae : ((T ⟨f, hf⟩ : Lp ℂ 2 ν) : X → ℂ) =ᵐ[ν] f := MemLp.coeFn_toLp (hmem ⟨f, hf⟩)
    rw [← key]
    have hfun : (fun x => f x * K.indicator (fun x => starRingEnd ℂ (a₀ x)) x)
        = K.indicator (fun x => f x * starRingEnd ℂ (a₀ x)) := by
      funext x
      by_cases hx : x ∈ K <;> simp [hx]
    rw [hfun, integral_indicator hKm]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
    simp [mul_comm]

end GlobalTheory
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integrable_density_of_bound_by_integral_on_compact : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (K : Set X), IsCompact K → μ K < ⊤ → ∀ (S : Submodule ℂ (X → ℂ)), (∀ f ∈ S, Continuous f) → ∀ (Λ : (X → ℂ) → ℂ) (C : ℝ), (∀ f ∈ S, ∀ f' ∈ S, ∀ c : ℂ, Λ (c • f + f') = c * Λ f + Λ f') → (∀ f ∈ S, ‖Λ f‖ ≤ C * ∫ x in K, ‖f x‖ ∂μ) → ∃ a : X → ℂ, Measurable a ∧ Integrable a μ ∧ (∀ x ∉ K, a x = 0) ∧ ∀ f ∈ S, ∫ x, f x * a x ∂μ = Λ f := by
  atlas_forward_decl GlobalTheory.exists_integrable_density_of_bound_by_integral_compact
end

section
section
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem smFn_nil_eq_integral_smooth : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∃ α : G → ℂ, h.IsSmoothFun α ∧ HasCompactSupport α ∧ ∀ f ∈ S, ∫ y, f y * α y ∂μ = Λ [] f := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hSc hSt K hK Λ hΛ
  haveI := hμ
  haveI : LocallyCompactSpace G := h.locallyCompactSpace
  haveI : SecondCountableTopology G := h.secondCountableTopology
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_prodExp_tsupport μ b
  obtain ⟨N, Λ', κ, hκ, hsum⟩ := GlobalTheory.T.exists_dixmierMalliavin_decomp_prodExp 𝔸 G 𝔤 h d b μ hμ S hSc hSt K hK ε hε d id Λ hΛ
  choose κ' hκ'sm hκ'cs _ hκ'int using fun m => hdens (κ m) (hκ m).2.1 (hκ m).2.2
  have hKμ : μ K < ⊤ := hK.measure_lt_top
  choose C hC using fun m => (hκ m).1.bdd []
  choose a ha using fun m => GlobalTheory.T.exists_integrable_density_of_bound_by_integral_on_compact G μ K hK hKμ S hSc (Λ' m []) (C m) ((hκ m).1.lin []) (hC m)
  have hκ'is : ∀ m, h.IsSmoothFun (κ' m) := fun m => hκ'sm m
  have hκ'c : ∀ m, Continuous (κ' m) := fun m => by
    letI := h.chartedSpace; exact (hκ'sm m).continuous
  have hconv := fun m => GlobalTheory.T.smooth_hasCompactSupport_conv_of_integrable_compact 𝔸 G 𝔤 h μ hμ K hK (κ' m) (a m) (hκ'is m) (hκ'cs m) (ha m).1 (ha m).2.1 (ha m).2.2.1
  refine ⟨fun z => ∑ m, ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ, ?_, ?_, ?_⟩
  · have e : (fun z => ∑ m, ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) =
        ∑ m, (fun z => ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) := by
      ext z; simp [Finset.sum_apply]
    rw [e]
    exact h.mem_smoothFuns.1 (Submodule.sum_mem (h.smoothFuns (F := ℂ)) fun m _ => h.mem_smoothFuns.2 (hconv m).1)
  · have e : (fun z => ∑ m, ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) =
        ∑ m, (fun z => ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) := by
      ext z; simp [Finset.sum_apply]
    rw [e]
    exact Finset.sum_induction _ HasCompactSupport (fun _ _ hu hv => hu.add hv) HasCompactSupport.zero
      fun m _ => (hconv m).2
  · intro f hf
    have hcc : ∀ m, Continuous (fun z => ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) := fun m => by
      letI := h.chartedSpace; exact (hconv m).1.continuous
    have hint : ∀ m, Integrable (fun z => f z * ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) μ := fun m =>
      ((hSc f hf).mul (hcc m)).integrable_of_hasCompactSupport (hconv m).2.mul_left
    calc ∫ y, f y * (∑ m, ∫ x, κ' m x * a m (x⁻¹ * y) ∂μ) ∂μ
        = ∑ m, ∫ y, f y * ∫ x, κ' m x * a m (x⁻¹ * y) ∂μ ∂μ := by
          simp_rw [Finset.mul_sum]; exact integral_finsetSum _ fun m _ => hint m
      _ = ∑ m, ∫ x, κ' m x * Λ' m [] (fun y => f (x * y)) ∂μ := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [GlobalTheory.T.integral_mul_convolution_eq_alt G μ hμ K hK (κ' m) (a m) (hκ'c m) (hκ'cs m) (ha m).1 (ha m).2.1 (ha m).2.2.1 f (hSc f hf)]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          have hx := (ha m).2.2.2 _ (hSt f hf x)
          simp only at hx ⊢
          rw [hx]
      _ = ∑ m, ∫ t, κ m t * Λ' m [] (fun y => f (h.prodExp (fun k => b (id k)) t * y)) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          exact hκ'int m _ (GlobalTheory.T.continuous_leftTranslate_boundedDerivFunctional 𝔸 G 𝔤 h d b μ hμ S hSc hSt K hK (Λ' m) (hκ m).1 [] f hf)
      _ = Λ [] f := (hsum f hf).symm

end GlobalTheory.HCA
end

open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_functional_integral_smooth_compact : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∃ α : G → ℂ, h.IsSmoothFun α ∧ HasCompactSupport α ∧ ∀ f ∈ S, ∫ y, f y * α y ∂μ = Λ [] f := by
  atlas_forward_decl GlobalTheory.HCA.smFn_nil_eq_integral_smooth
end
