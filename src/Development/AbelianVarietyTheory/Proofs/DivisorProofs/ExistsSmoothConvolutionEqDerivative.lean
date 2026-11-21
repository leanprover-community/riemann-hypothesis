import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstFunctionalIntegralSmoothCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInteriorEstimateDerivWordPolyLaplacian
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
import BuildAid.ForwardExisting
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.LeftTranslate

section
open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace GlobalTheory.HaarRightTranslate

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

theorem map_mul_right_eq_modular (μ : Measure H) [IsHaarMeasure μ] (g : H) :
    map (· * g) μ = modularCharacterFun g • μ := by
  rw [modularCharacterFun_eq_haarScalarFactor μ g]
  exact isMulLeftInvariant_eq_smul _ μ

theorem modular_bdd_on_compact {V : Set H} (hV : IsCompact V) :
    ∃ M : ℝ≥0, ∀ v ∈ V, modularCharacterFun v ≤ M := by
  set μ : Measure H := haar
  have K : PositiveCompacts H := Classical.arbitrary _
  set A : Set H := closure (K : Set H) with hA
  have hAc : IsCompact A := K.isCompact.closure
  have hAm : MeasurableSet A := isClosed_closure.measurableSet
  have hpos : μ A ≠ 0 :=
    (measure_pos_of_nonempty_interior _
      (K.interior_nonempty.mono (interior_mono subset_closure))).ne'
  have hfin : μ A ≠ ∞ := hAc.measure_lt_top.ne
  have hB : IsCompact (A * V⁻¹) := hAc.mul hV.inv
  have hBfin : μ (A * V⁻¹) ≠ ∞ := hB.measure_lt_top.ne
  refine ⟨(μ (A * V⁻¹) / μ A).toNNReal, fun v hv => ?_⟩
  have h1 : (modularCharacterFun v : ℝ≥0∞) * μ A ≤ μ (A * V⁻¹) := by
    have h := congrArg (fun ρ : Measure H => ρ A) (map_mul_right_eq_modular μ v)
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    rw [← h, map_apply (measurable_mul_const _) hAm]
    refine measure_mono fun x hx => ?_
    exact ⟨x * v, hx, v⁻¹, by simpa using hv, by simp⟩
  have h2 : (modularCharacterFun v : ℝ≥0∞) ≤ μ (A * V⁻¹) / μ A :=
    (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin)).2 h1
  have hne : μ (A * V⁻¹) / μ A ≠ ∞ := ENNReal.div_ne_top hBfin hpos
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hne]
  exact h2

end HaarRightTranslate

theorem haar_lintegral_mul_right_le :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
      [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H),
      μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ y ∈ K, ∀ φ : H → ENNReal,
        Measurable φ → ∫⁻ x, φ (x * y) ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by
  intro H _ _ _ _ _ _ _ _ μ hμ K hK
  obtain ⟨M, hM⟩ := HaarRightTranslate.modular_bdd_on_compact hK
  refine ⟨M, fun y hy φ hφ => ?_⟩
  have e : ∫⁻ x, φ (x * y) ∂μ = ∫⁻ x, φ x ∂(map (· * y) μ) :=
    (lintegral_map hφ (measurable_mul_const y)).symm
  rw [e, HaarRightTranslate.map_mul_right_eq_modular μ y, lintegral_smul_measure, ENNReal.smul_def,
    smul_eq_mul]
  gcongr
  exact_mod_cast hM y hy

end GlobalTheory
end
end

section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_lintegral_mul_right_le_alt : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ y ∈ K, ∀ φ : H → ENNReal, Measurable φ → ∫⁻ x, φ (x * y) ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by
  atlas_forward_decl GlobalTheory.haar_lintegral_mul_right_le
end

section
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

open scoped Pointwise

theorem GlobalTheory.setIntegral_norm_prodExp_mul_le_haar : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∃ ρ > 0, ∀ K₁ : Set G, IsCompact K₁ → ∃ (C : ℝ) (K₂ : Set G), 0 ≤ C ∧ IsCompact K₂ ∧ ∀ φ : G → ℂ, Continuous φ → ∀ y ∈ K₁, ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ, ‖φ (h.prodExp b t * y)‖ ≤ C * ∫ x in K₂, ‖φ x‖ ∂μ := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ
  haveI := hμ
  haveI : LocallyCompactSpace G := h.locallyCompactSpace
  haveI : SecondCountableTopology 𝔸ˣ := Units.isOpenEmbedding_val.isInducing.secondCountableTopology
  haveI : SecondCountableTopology G := Topology.IsInducing.subtypeVal.secondCountableTopology
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_prodExp_tsupport μ b
  refine ⟨ε / 2, by positivity, fun K₁ hK₁ => ?_⟩
  let β : ContDiffBump (0 : Fin d → ℝ) := ⟨ε / 2, ε, by positivity, by linarith⟩
  set K : (Fin d → ℝ) → ℂ := fun t => ((β t : ℝ) : ℂ) with hKdef
  have hK : ContDiff ℝ ∞ K := Complex.ofRealCLM.contDiff.comp β.contDiff
  have hKs : tsupport K ⊆ Metric.closedBall 0 ε := by
    have : tsupport K ⊆ tsupport β := tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) (by simp) _
    rw [β.tsupport_eq] at this
    exact this
  obtain ⟨κ, hκs, hκc, -, hκint⟩ := hdens K hK hKs
  have hκcont : Continuous κ := by
    letI := h.chartedSpace
    exact hκs.continuous
  obtain ⟨M, hM⟩ := hκc.exists_bound_of_continuous hκcont
  have hK₂ : IsCompact (tsupport κ * K₁) := IsCompact.mul hκc hK₁
  obtain ⟨B, hB⟩ := GlobalTheory.T.haar_lintegral_mul_right_le_alt G μ hμ K₁ hK₁
  refine ⟨max M 0 * B, tsupport κ * K₁, by positivity, hK₂, fun φ hφ y hy => ?_⟩
  set K₂ := tsupport κ * K₁ with hK₂def
  set P := h.prodExp (⇑b) with hPdef
  have hPc : Continuous P := h.continuous_prodExp _
  set f : (Fin d → ℝ) → ℝ := fun t => ‖φ (P t * y)‖ with hfdef
  have hfc : Continuous f := (hφ.comp (hPc.mul continuous_const)).norm
  set ψ : G → ℂ := fun x => ((‖φ (x * y)‖ : ℝ) : ℂ) with hψdef
  have hψc : Continuous ψ := Complex.continuous_ofReal.comp (hφ.comp (continuous_id.mul continuous_const)).norm

  have h1 : ∫ t in Metric.closedBall (0 : Fin d → ℝ) (ε / 2), f t ≤ ∫ t, β t * f t := by
    have e : ∫ t in Metric.closedBall (0 : Fin d → ℝ) (ε / 2), f t
        = ∫ t in Metric.closedBall (0 : Fin d → ℝ) (ε / 2), β t * f t := by
      refine setIntegral_congr_fun measurableSet_closedBall fun t ht => ?_
      rw [β.one_of_mem_closedBall ht, one_mul]
    rw [e]
    refine setIntegral_le_integral ?_ (Filter.Eventually.of_forall fun t => mul_nonneg β.nonneg (norm_nonneg _))
    exact (β.continuous.mul hfc).integrable_of_hasCompactSupport β.hasCompactSupport.mul_right

  have h2 : ∫ t, β t * f t = (∫ x, κ x * ψ x ∂μ).re := by
    rw [hκint ψ hψc]
    have : (fun t => K t * ψ (P t)) = fun t => (((β t * f t : ℝ)) : ℂ) := by
      funext t; simp [hKdef, hψdef, hfdef]
    rw [this, integral_complex_ofReal, Complex.ofReal_re]

  have h3 : (∫ x, κ x * ψ x ∂μ).re ≤ ∫ x, ‖κ x * ψ x‖ ∂μ :=
    (Complex.re_le_norm _).trans (norm_integral_le_integral_norm _)

  set g : G → ENNReal := K₂.indicator fun z => ‖φ z‖ₑ with hgdef
  have hg : Measurable g := hφ.enorm.measurable.indicator hK₂.isClosed.measurableSet
  set L := ∫⁻ x in K₂, ‖φ x‖ₑ ∂μ with hLdef
  have hL : L < ⊤ := (hφ.continuousOn.integrableOn_compact hK₂).hasFiniteIntegral
  have hgL : ∫⁻ x, g x ∂μ = L := lintegral_indicator hK₂.isClosed.measurableSet _
  have hpt : ∀ x, ‖κ x * ψ x‖ₑ ≤ ENNReal.ofReal (max M 0) * g (x * y) := by
    intro x
    by_cases hx : x ∈ tsupport κ
    · have hxy : x * y ∈ K₂ := Set.mul_mem_mul hx hy
      rw [hgdef, Set.indicator_of_mem hxy, enorm_mul]
      gcongr
      · rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal ((hM x).trans (le_max_left _ _))
      · rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
        apply le_of_eq
        congr 1
        simp [hψdef]
    · have : κ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
  have h4l : ∫⁻ x, ‖κ x * ψ x‖ₑ ∂μ ≤ ENNReal.ofReal (max M 0) * ((B : ENNReal) * L) := by
    calc ∫⁻ x, ‖κ x * ψ x‖ₑ ∂μ ≤ ∫⁻ x, ENNReal.ofReal (max M 0) * g (x * y) ∂μ := lintegral_mono hpt
      _ = ENNReal.ofReal (max M 0) * ∫⁻ x, g (x * y) ∂μ :=
          lintegral_const_mul _ (hg.comp (measurable_id.mul_const y))
      _ ≤ ENNReal.ofReal (max M 0) * ((B : ENNReal) * L) := by
          gcongr
          rw [← hgL]
          exact hB y hy g hg
  have h4 : ∫ x, ‖κ x * ψ x‖ ∂μ ≤ max M 0 * B * ∫ x in K₂, ‖φ x‖ ∂μ := by
    rw [integral_norm_eq_lintegral_enorm (f := fun x => κ x * ψ x) (hκcont.mul hψc).aestronglyMeasurable,
      integral_norm_eq_lintegral_enorm hφ.aestronglyMeasurable]
    have hfin : ENNReal.ofReal (max M 0) * ((B : ENNReal) * L) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hL.ne)
    refine (ENNReal.toReal_mono hfin h4l).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_max_right _ _),
      ENNReal.coe_toReal, mul_assoc]
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := h3
    _ ≤ _ := h4
end

open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_setIntegral_norm_prodExp_mul_le_haar : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∃ ρ > 0, ∀ K₁ : Set G, IsCompact K₁ → ∃ (C : ℝ) (K₂ : Set G), 0 ≤ C ∧ IsCompact K₂ ∧ ∀ φ : G → ℂ, Continuous φ → ∀ y ∈ K₁, ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ, ‖φ (h.prodExp b t * y)‖ ≤ C * ∫ x in K₂, ‖φ x‖ ∂μ := by
  atlas_forward_decl GlobalTheory.setIntegral_norm_prodExp_mul_le_haar
end

section
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.LeftSmoothing

open scoped Manifold Topology
open Set Filter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem contMDiff_prodExp (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin n → 𝔤) :
    letI := h.chartedSpace; ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, 𝔤) ∞ (h.prodExp X) := by
  letI := h.chartedSpace
  intro t
  refine h.contMDiffAt_of_val ?_
  have e : (fun s => (((h.prodExp X s : G) : 𝔸ˣ) : 𝔸)) = prodExpVal (fun i => (X i : 𝔸)) :=
    funext fun s => h.val_prodExp X s
  rw [e]
  exact (contDiff_prodExpVal _).contMDiff.contMDiffAt

theorem contDiff_param (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin n → 𝔤) {f : G → ℂ}
    (hf : h.IsSmoothFun f) (g : G) :
    ContDiff ℝ ∞ (fun p : 𝔤 × (Fin n → ℝ) => f (h.prodExp X p.2 * g * h.expG p.1)) := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hm : ContMDiff 𝓘(ℝ, 𝔤 × (Fin n → ℝ)) 𝓘(ℝ, 𝔤) ∞
      (fun p : 𝔤 × (Fin n → ℝ) => h.prodExp X p.2 * g * h.expG p.1) :=
    (((contMDiff_prodExp h X).comp contDiff_snd.contMDiff).mul contMDiff_const).mul
      (h.contMDiff_expG_comp contDiff_fst)
  exact (ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf hm).contDiff

theorem continuous_iteratedFDeriv_partial {P T E' : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {Φ : P × T → E'} (hΦ : ContDiff ℝ ∞ Φ) (k : ℕ) :
    Continuous (fun p : P × T => iteratedFDeriv ℝ k (fun Y => Φ (Y, p.2)) p.1) := by
  set L := ContinuousLinearMap.inl ℝ P T
  set H : P × T → ContinuousMultilinearMap ℝ (fun _ : Fin k => P) E' :=
    fun q => ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => L) (iteratedFDeriv ℝ k Φ q)
  have hH : Continuous H :=
    (ContinuousLinearMap.continuous _).comp (hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hpart : ∀ (Z : T) (Y : P), iteratedFDeriv ℝ k (fun Y => Φ (Y, Z)) Y = H (Y, Z) := by
    intro Z Y
    have e : (fun Y => Φ (Y, Z)) = (fun w => Φ (w + (0, Z))) ∘ L := by
      funext Y; simp [L]
    have hΦZ : ContDiff ℝ ∞ (fun w : P × T => Φ (w + (0, Z))) :=
      hΦ.comp (contDiff_id.add contDiff_const)
    rw [e, L.iteratedFDeriv_comp_right hΦZ Y (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    simp [H, L]
  have e : (fun p : P × T => iteratedFDeriv ℝ k (fun Y => Φ (Y, p.2)) p.1) = H := by
    funext p; exact hpart p.2 p.1
  rw [e]; exact hH

variable (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin n → 𝔤) (κ : (Fin n → ℝ) → ℂ)

noncomputable def integrand (f : G → ℂ) (g : G) (Y : 𝔤) (t : Fin n → ℝ) : ℂ :=
  κ t * f (h.prodExp X t * g * h.expG Y)

noncomputable def conv (f : G → ℂ) (y : G) : ℂ :=
  ∫ t, κ t * f (h.prodExp X t * y)

theorem conv_mul_expG (f : G → ℂ) (g : G) (Y : 𝔤) :
    conv h X κ f (g * h.expG Y) = ∫ t, integrand h X κ f g Y t := by
  simp only [conv, integrand, mul_assoc]

variable {h X κ}

theorem contDiff_slice {f : G → ℂ} (hf : h.IsSmoothFun f) (g : G) (t : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun Y : 𝔤 => f (h.prodExp X t * g * h.expG Y)) :=
  (contDiff_param h X hf g).comp (contDiff_id.prodMk contDiff_const)

theorem iter_integrand_eq {f : G → ℂ} (hf : h.IsSmoothFun f) (g : G) (k : ℕ) (Y : 𝔤)
    (t : Fin n → ℝ) :
    ParamIntegral.iter (integrand h X κ f g) k Y t =
      (ContinuousLinearMap.mul ℝ ℂ (κ t)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (fun Y : 𝔤 => f (h.prodExp X t * g * h.expG Y)) Y) := by
  rw [ParamIntegral.iter]
  have e : (fun Y => integrand h X κ f g Y t) =
      (ContinuousLinearMap.mul ℝ ℂ (κ t)) ∘ (fun Y : 𝔤 => f (h.prodExp X t * g * h.expG Y)) := by
    funext Y; simp [integrand]
  rw [e]
  exact (ContinuousLinearMap.mul ℝ ℂ (κ t)).iteratedFDeriv_comp_left
    (contDiff_slice hf g t).contDiffAt (by exact_mod_cast le_top)

theorem integrand_contDiff {f : G → ℂ} (hf : h.IsSmoothFun f) (g : G) (t : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun Y => integrand h X κ f g Y t) := by
  have e : (fun Y => integrand h X κ f g Y t) =
      (ContinuousLinearMap.mul ℝ ℂ (κ t)) ∘ (fun Y : 𝔤 => f (h.prodExp X t * g * h.expG Y)) := by
    funext Y; simp [integrand]
  rw [e]
  exact (ContinuousLinearMap.mul ℝ ℂ (κ t)).contDiff.comp (contDiff_slice hf g t)

theorem integrand_cont (hκ : Continuous κ) {f : G → ℂ} (hf : h.IsSmoothFun f) (g : G) (k : ℕ) :
    Continuous (fun p : 𝔤 × (Fin n → ℝ) => ParamIntegral.iter (integrand h X κ f g) k p.1 p.2) := by
  simp_rw [iter_integrand_eq hf]
  have hc := continuous_iteratedFDeriv_partial (contDiff_param h X hf g) k
  have hL : Continuous (fun t => ContinuousLinearMap.mul ℝ ℂ (κ t)) :=
    (ContinuousLinearMap.mul ℝ ℂ).continuous.comp hκ
  have hB := ContinuousLinearMap.continuous₂ (𝕜 := ℝ) (E := ℂ →L[ℝ] ℂ)
    (F := ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) ℂ)
    (G := ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) ℂ)
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => 𝔤) ℂ ℂ)
  exact hB.comp ((hL.comp continuous_snd).prodMk hc)

theorem integrand_supp (hκs : HasCompactSupport κ) (f : G → ℂ) (g : G) (Y₀ : 𝔤) :
    ∃ U ∈ 𝓝 Y₀, ∃ C : Set (Fin n → ℝ), IsCompact C ∧
      ∀ Y ∈ U, ∀ t ∉ C, integrand h X κ f g Y t = 0 :=
  ⟨univ, univ_mem, tsupport κ, hκs, fun Y _ t ht => by
    simp [integrand, image_eq_zero_of_notMem_tsupport ht]⟩

theorem isSmoothFun_conv (hκ : Continuous κ) (hκs : HasCompactSupport κ) {f : G → ℂ}
    (hf : h.IsSmoothFun f) : h.IsSmoothFun (conv h X κ f) := by
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro g
  simp_rw [conv_mul_expG]
  exact contDiff_integral_of_iteratedFDeriv _ (integrand_contDiff hf g)
    (integrand_cont hκ hf g) (integrand_supp hκs f g)

theorem rightDeriv_conv (hκ : Continuous κ) (hκs : HasCompactSupport κ) {f : G → ℂ}
    (hf : h.IsSmoothFun f) (Z : 𝔤) (g : G) :
    h.rightDeriv Z (conv h X κ f) g = conv h X κ (h.rightDeriv Z f) g := by
  show fderiv ℝ (fun Y : 𝔤 => conv h X κ f (g * h.expG Y)) 0 Z = _
  simp_rw [conv_mul_expG]
  rw [← iteratedFDeriv_one_apply (fun _ : Fin 1 => Z),
    iteratedFDeriv_integral_eq _ (integrand_contDiff hf g) (integrand_cont hκ hf g)
      (integrand_supp hκs f g) 1]
  have hint : Integrable (fun t => ParamIntegral.iter (integrand h X κ f g) 1 (0 : 𝔤) t) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((integrand_cont hκ hf g 1).comp (continuous_const.prodMk continuous_id)) ?_
    refine HasCompactSupport.intro hκs fun t ht => ParamIntegral.iter_eq_zero_of_eventually ?_
    exact Eventually.of_forall fun Y => by
      simp [integrand, image_eq_zero_of_notMem_tsupport ht]
  rw [ContinuousMultilinearMap.integral_apply hint]
  simp only [conv]
  congr 1
  funext t
  rw [iter_integrand_eq hf]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.mul_apply']
  rw [iteratedFDeriv_one_apply]
  rfl

variable (h X) in

noncomputable def convEnd (hκ : Continuous κ) (hκs : HasCompactSupport κ) :
    Module.End ℂ (h.smoothFuns (F := ℂ)) where
  toFun f := ⟨conv h X κ f, isSmoothFun_conv hκ hκs f.2⟩
  map_add' f₁ f₂ := by
    apply Subtype.ext
    funext y
    have hc : ∀ f : h.smoothFuns (F := ℂ), Integrable (fun t => κ t * (f : G → ℂ) (h.prodExp X t * y)) := by
      intro f
      have hfc : Continuous (f : G → ℂ) := by
        letI := h.chartedSpace
        exact (show h.IsSmoothFun (f : G → ℂ) from f.2).continuous
      exact (hκ.mul (hfc.comp ((h.continuous_prodExp X).mul continuous_const))).integrable_of_hasCompactSupport
        (hκs.mul_right)
    show ∫ t, κ t * ((f₁ : G → ℂ) + f₂) (h.prodExp X t * y) = (∫ t, κ t * (f₁ : G → ℂ) (h.prodExp X t * y)) + ∫ t, κ t * (f₂ : G → ℂ) (h.prodExp X t * y)
    rw [← integral_add (hc f₁) (hc f₂)]
    congr 1; funext t; simp [mul_add]
  map_smul' c f := by
    apply Subtype.ext
    funext y
    show ∫ t, κ t * (c • (f : G → ℂ)) (h.prodExp X t * y) = c * ∫ t, κ t * (f : G → ℂ) (h.prodExp X t * y)
    rw [← integral_const_mul]
    congr 1; funext t; simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem commute_convEnd (hκ : Continuous κ) (hκs : HasCompactSupport κ) (Z : 𝔤) :
    h.rightDerivEnd (F := ℂ) Z * convEnd h X hκ hκs = convEnd h X hκ hκs * h.rightDerivEnd Z := by
  refine LinearMap.ext fun f => Subtype.ext (funext fun y => ?_)
  exact rightDeriv_conv hκ hκs f.2 Z y

theorem adjoin_commute_convEnd (hκ : Continuous κ) (hκs : HasCompactSupport κ)
    {T : Module.End ℂ (h.smoothFuns (F := ℂ))}
    (hT : T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ)))) :
    T * convEnd h X hκ hκs = convEnd h X hκ hκs * T := by
  have hle : Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) ≤
      Subalgebra.centralizer ℂ {convEnd h X hκ hκs} := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨Z, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro A hA
    rw [Set.mem_singleton_iff] at hA
    subst hA
    exact (commute_convEnd hκ hκs Z).symm
  have := (Subalgebra.mem_centralizer_iff ℂ).1 (hle hT) _ rfl
  exact this.symm

end GlobalTheory.LeftSmoothing

open GlobalTheory.LeftSmoothing in

theorem GlobalTheory.leftSmoothing_prodExp :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (n : ℕ) (X : Fin n → 𝔤) (κ : (Fin n → ℝ) → ℂ), Continuous κ → HasCompactSupport κ → ∀ f : h.smoothFuns (F := ℂ), ∃ v : h.smoothFuns (F := ℂ), (∀ y, (v : G → ℂ) y = ∫ t, κ t * (f : G → ℂ) (h.prodExp X t * y)) ∧ ∀ T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))), ∀ y, (T v : G → ℂ) y = ∫ t, κ t * (T f : G → ℂ) (h.prodExp X t * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h n X κ hκ hκs f
  refine ⟨convEnd h X hκ hκs f, fun y => rfl, fun T hT y => ?_⟩
  have e := LinearMap.congr_fun (adjoin_commute_convEnd (X := X) hκ hκs hT) f
  simp only [Module.End.mul_apply] at e
  rw [e]
  rfl
end

open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftSmoothing_prodExp_smooth_commute : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (n : ℕ) (X : Fin n → 𝔤) (κ : (Fin n → ℝ) → ℂ), Continuous κ → HasCompactSupport κ → ∀ f : h.smoothFuns (F := ℂ), ∃ v : h.smoothFuns (F := ℂ), (∀ y, (v : G → ℂ) y = ∫ t, κ t * (f : G → ℂ) (h.prodExp X t * y)) ∧ ∀ T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))), ∀ y, (T v : G → ℂ) y = ∫ t, κ t * (T f : G → ℂ) (h.prodExp X t * y) := by
  atlas_forward_decl GlobalTheory.leftSmoothing_prodExp
end

section
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory

theorem iteratedDeriv_expG_line_eq_rightDeriv_pow :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ (X : 𝔤) (g : G) (n : ℕ), ContDiff ℝ ∞ (fun t : ℝ => f (g * h.expG (t • X))) ∧ ∀ s : ℝ, iteratedDeriv n (fun t : ℝ => f (g * h.expG (t • X))) s = (List.replicate n X).foldr h.rightDeriv f (g * h.expG (s • X)) := by
  intro 𝔸 _ _ _ _ G 𝔤 h f hf X g n
  have hd : ∀ (f : G → ℂ), h.IsSmoothFun f → ∀ s : ℝ,
      HasDerivAt (fun t : ℝ => f (g * h.expG (t • X))) (h.rightDeriv X f (g * h.expG (s • X))) s := by
    intro f hf s
    have h1 := h.hasDerivAt_rightDeriv hf X (g * h.expG (s • X))
    have h2 : HasDerivAt (fun t : ℝ => f (g * h.expG ((s + t) • X)))
        (h.rightDeriv X f (g * h.expG (s • X))) (s - s) := by
      rw [sub_self]
      simpa only [h.expG_add_smul, mul_assoc] using h1
    have h3 := h2.comp_sub_const s s
    simpa only [add_sub_cancel] using h3
  have hi : ∀ (n : ℕ) (f : G → ℂ), h.IsSmoothFun f →
      iteratedDeriv n (fun t : ℝ => f (g * h.expG (t • X)))
        = fun s : ℝ => (List.replicate n X).foldr h.rightDeriv f (g * h.expG (s • X)) := by
    intro n
    induction n with
    | zero => intro f _; simp
    | succ n ih =>
      intro f hf
      rw [iteratedDeriv_succ']
      have hderiv : deriv (fun t : ℝ => f (g * h.expG (t • X)))
          = fun t : ℝ => h.rightDeriv X f (g * h.expG (t • X)) := by
        funext s; exact (hd f hf s).deriv
      rw [hderiv, ih _ (h.isSmoothFun_rightDeriv hf X)]
      funext s
      rw [List.replicate_succ', List.foldr_append]
      rfl
  refine ⟨?_, fun s => by rw [hi n f hf]⟩
  have hc := (h.isSmoothFun_iff).1 hf g
  exact hc.comp (contDiff_id.smul contDiff_const)

end GlobalTheory
end

open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_expG_line_eq_foldr_rightDeriv : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ (X : 𝔤) (g : G) (n : ℕ), ContDiff ℝ ∞ (fun t : ℝ => f (g * h.expG (t • X))) ∧ ∀ s : ℝ, iteratedDeriv n (fun t : ℝ => f (g * h.expG (t • X))) s = (List.replicate n X).foldr h.rightDeriv f (g * h.expG (s • X)) := by
  atlas_forward_decl GlobalTheory.iteratedDeriv_expG_line_eq_rightDeriv_pow
end

section
section
open MeasureTheory
open scoped ContDiff

namespace GlobalTheory

theorem value_at_zero_eq_sum_integral_kernel_iteratedDeriv :
    ∀ ε : ℝ, 0 < ε → ∃ κ : Fin 3 → ℝ → ℂ,
      (∀ n, Continuous (κ n) ∧ tsupport (κ n) ⊆ Set.Icc (-ε) ε) ∧
      ∀ u : ℝ → ℂ, ContDiff ℝ ∞ u → u 0 = ∑ n : Fin 3, ∫ t, κ n t * iteratedDeriv n u t := by
  intro ε hε
  set e : ℂ := (ε : ℂ) with he_def
  have he : e ≠ 0 := by
    rw [he_def]; exact_mod_cast hε.ne'
  let s : ℝ → ℝ := fun t => max 0 (min t ε)
  have hs_cont : Continuous s := by fun_prop
  have hs_eq : ∀ t ∈ Set.Icc 0 ε, s t = t := by
    intro t ht; simp only [s]; rw [min_eq_left ht.2, max_eq_right ht.1]
  let P : Fin 3 → ℂ → ℂ := ![fun x => x * (6 / e ^ 2 * (1 - x / e)),
    fun x => x * (2 * (-3 / e * (1 - x / e) ^ 2)), fun x => x * (1 - x / e) ^ 3]
  have hP_cont : ∀ n, Continuous (P n) := by
    intro n; fin_cases n <;> simp [P] <;> fun_prop
  have hP0 : ∀ n, P n 0 = 0 := by
    intro n; fin_cases n <;> simp [P]
  have hPe : ∀ n, P n e = 0 := by
    intro n; fin_cases n <;> simp [P, div_self he]
  have hzero : ∀ n t, t ∉ Set.Ioc 0 ε → P n (s t : ℂ) = 0 := by
    intro n t ht
    rcases le_or_gt t 0 with h | h
    · have : s t = 0 := by simp only [s]; exact max_eq_left (min_le_of_left_le h)
      rw [this, Complex.ofReal_zero, hP0]
    · have h' : ε < t := by
        by_contra h''; exact ht ⟨h, not_lt.mp h''⟩
      have : s t = ε := by simp only [s]; rw [min_eq_right h'.le, max_eq_right hε.le]
      rw [this, ← he_def, hPe]
  refine ⟨fun n t => P n (s t : ℂ), ?_, ?_⟩
  · intro n
    refine ⟨(hP_cont n).comp (Complex.continuous_ofReal.comp hs_cont), ?_⟩
    refine closure_minimal ?_ isClosed_Icc
    intro t ht
    by_contra h
    apply ht
    apply hzero n t
    intro h2; exact h ⟨by linarith [h2.1], h2.2⟩
  · intro u hu
    have h1 := contDiff_infty_iff_deriv.mp hu
    have h2 := contDiff_infty_iff_deriv.mp h1.2
    have hu1 : ∀ x, HasDerivAt u (deriv u x) x := fun x => (h1.1 x).hasDerivAt
    have hu2 : ∀ x, HasDerivAt (deriv u) (deriv (deriv u) x) x := fun x => (h2.1 x).hasDerivAt
    have hc0 : Continuous u := h1.1.continuous
    have hc1 : Continuous (deriv u) := h2.1.continuous
    have hc2 : Continuous (deriv (deriv u)) := h2.2.continuous
    have hd2 : iteratedDeriv 2 u = deriv (deriv u) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hI : ∀ (g : ℝ → ℂ) (n : Fin 3),
        ∫ t, P n (s t : ℂ) * g t = ∫ t in (0:ℝ)..ε, P n (s t : ℂ) * g t := by
      intro g n
      rw [intervalIntegral.integral_of_le hε.le, setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro t ht; rw [hzero n t ht, zero_mul]
    have hK : ∀ n, Continuous (fun t => P n (s t : ℂ)) := fun n =>
      (hP_cont n).comp (Complex.continuous_ofReal.comp hs_cont)
    rw [Fin.sum_univ_three]
    have e0 : iteratedDeriv ((0 : Fin 3) : ℕ) u = u := iteratedDeriv_zero
    have e1 : iteratedDeriv ((1 : Fin 3) : ℕ) u = deriv u := iteratedDeriv_one
    have e2 : iteratedDeriv ((2 : Fin 3) : ℕ) u = deriv (deriv u) := hd2
    rw [e0, e1, e2]
    rw [hI, hI, hI, ← intervalIntegral.integral_add, ← intervalIntegral.integral_add]
    all_goals try (apply Continuous.intervalIntegrable; have := hK 0; have := hK 1; have := hK 2; fun_prop)
    let F : ℝ → ℂ := fun t => (t : ℂ) * (-3 / e * (1 - (t : ℂ) / e) ^ 2 * u t
      + (1 - (t : ℂ) / e) ^ 3 * deriv u t) - (1 - (t : ℂ) / e) ^ 3 * u t
    have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F) (a := 0) (b := ε)
      (f' := fun t => P 0 (s t : ℂ) * u t + P 1 (s t : ℂ) * deriv u t
        + P 2 (s t : ℂ) * deriv (deriv u) t) ?_
      (by apply Continuous.intervalIntegrable; have := hK 0; have := hK 1; have := hK 2; fun_prop)
    · rw [key]
      simp only [F, Complex.ofReal_zero, zero_div, sub_zero, one_pow, one_mul, zero_mul,
        zero_sub, ← he_def, div_self he, sub_self]
      ring
    · intro x hx
      rw [Set.uIcc_of_le hε.le] at hx
      simp only [hs_eq x hx]
      have hx' : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
        simpa using (hasDerivAt_id x).ofReal_comp
      have hL : HasDerivAt (fun t : ℝ => (1 : ℂ) - (t : ℂ) / e) (-(1 / e)) x := by
        convert (hx'.div_const e).const_sub 1 using 1
      have hφ : HasDerivAt (fun t : ℝ => (1 - (t : ℂ) / e) ^ 3) (-3 / e * (1 - (x : ℂ) / e) ^ 2) x := by
        exact (hL.pow 3).congr_deriv (by norm_num <;> ring)
      have hφ' : HasDerivAt (fun t : ℝ => -3 / e * (1 - (t : ℂ) / e) ^ 2)
          (6 / e ^ 2 * (1 - (x : ℂ) / e)) x := by
        exact ((hL.pow 2).const_mul (-3 / e)).congr_deriv (by norm_num <;> ring)
      have hF := (hx'.mul ((hφ'.mul (hu1 x)).add (hφ.mul (hu2 x)))).sub (hφ.mul (hu1 x))
      refine hF.congr_deriv ?_
      simp only [Pi.mul_apply, Pi.add_apply, P, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring

end GlobalTheory
end

open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kernels_eval_zero_eq_sum_integral_iteratedDeriv : ∀ ε : ℝ, 0 < ε → ∃ κ : Fin 3 → ℝ → ℂ, (∀ n, Continuous (κ n) ∧ tsupport (κ n) ⊆ Set.Icc (-ε) ε) ∧ ∀ u : ℝ → ℂ, ContDiff ℝ ∞ u → u 0 = ∑ n : Fin 3, ∫ t, κ n t * iteratedDeriv n u t := by
  atlas_forward_decl GlobalTheory.value_at_zero_eq_sum_integral_kernel_iteratedDeriv
end

section
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory
namespace SobolevRep

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

theorem prodExp_succ {d : ℕ} (X : Fin (d + 1) → 𝔤) (t : Fin (d + 1) → ℝ) :
    h.prodExp X t = h.expG (t 0 • X 0) * h.prodExp (Fin.tail X) (Fin.tail t) := by
  simp [IsExpLieAlgebra.prodExp, List.ofFn_succ, Fin.tail]

theorem continuous_prodExp' {d : ℕ} (X : Fin d → 𝔤) : Continuous (h.prodExp X) := by
  have : h.prodExp X = fun t => (h.revProdExp X (-t))⁻¹ := by
    funext t; rw [h.revProdExp_inv, neg_neg]
  rw [this]
  exact ((h.continuous_revProdExp X).comp continuous_neg).inv

theorem isSmoothFun_foldr {f : G → ℂ} (hf : h.IsSmoothFun f) :
    ∀ l : List 𝔤, h.IsSmoothFun (l.foldr h.rightDeriv f)
  | [] => hf
  | X :: l => h.isSmoothFun_rightDeriv (isSmoothFun_foldr hf l) X

theorem continuous_of_isSmoothFun {f : G → ℂ} (hf : h.IsSmoothFun f) : Continuous f := by
  letI := h.chartedSpace
  exact ContMDiff.continuous hf

theorem integral_cons {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} (hε : 0 ≤ ε) {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Set.Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    ∫ t, a (t 0) * K (Fin.tail t) * F (x * h.prodExp X t) =
      ∫ s, ∫ t', a s * (K t' * F (x * h.expG (s • X 0) * h.prodExp (Fin.tail X) t')) := by
  have hint : Integrable
      (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t) * F (x * h.prodExp X t)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((ha.comp (continuous_apply 0)).mul
        (hK.comp (continuous_pi fun j => continuous_apply j.succ))).mul
        (hF.comp (continuous_const.mul (continuous_prodExp' h X)))
    · exact HasCompactSupport.mul_right (f := fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t))
        ((isCompact_closedBall 0 ε).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_cons_kernel hε has hKs))
  rw [integral_fin_succ_cons hint]
  congr 1; funext s; congr 1; funext t'
  simp only [Fin.cons_zero, Fin.tail_cons, prodExp_succ h, mul_assoc]

theorem integrable_integral_cons {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Set.Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    Integrable (fun s : ℝ =>
      ∫ t', a s * (K t' * F (x * h.expG (s • X 0) * h.prodExp (Fin.tail X) t'))) := by
  have hc : Continuous (fun p : ℝ × (Fin d → ℝ) =>
      a p.1 * (K p.2 * F (x * h.expG (p.1 • X 0) * h.prodExp (Fin.tail X) p.2))) :=
    (ha.comp continuous_fst).mul ((hK.comp continuous_snd).mul (hF.comp
      ((continuous_const.mul (h.continuous_expG.comp (continuous_fst.smul continuous_const))).mul
        ((continuous_prodExp' h (Fin.tail X)).comp continuous_snd))))
  have hs : HasCompactSupport (fun p : ℝ × (Fin d → ℝ) =>
      a p.1 * (K p.2 * F (x * h.expG (p.1 • X 0) * h.prodExp (Fin.tail X) p.2))) := by
    refine HasCompactSupport.intro
      ((isCompact_Icc (a := -ε) (b := ε)).prod (isCompact_closedBall (0 : Fin d → ℝ) ε)) ?_
    intro p hp
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (has h')), zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (hKs h')), zero_mul, mul_zero]
  exact (hc.integrable_of_hasCompactSupport hs).integral_prod_left

theorem sum_integral_cons {d m : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} (hε : 0 ≤ ε)
    {a : ℝ → ℂ} (ha : Continuous a) (has : tsupport a ⊆ Set.Icc (-ε) ε)
    {K : Fin m → (Fin d → ℝ) → ℂ} (hK : ∀ i, Continuous (K i))
    (hKs : ∀ i, tsupport (K i) ⊆ Metric.closedBall 0 ε) {F : Fin m → G → ℂ}
    (hF : ∀ i, Continuous (F i)) {f₁ : G → ℂ}
    (hd : ∀ y, f₁ y = ∑ i, ∫ t', K i t' * F i (y * h.prodExp (Fin.tail X) t')) (x : G) :
    ∑ i, ∫ t, a (t 0) * K i (Fin.tail t) * F i (x * h.prodExp X t) =
      ∫ s, a s * f₁ (x * h.expG (s • X 0)) := by
  rw [Finset.sum_congr rfl fun i _ => integral_cons h X hε ha has (hK i) (hKs i) (hF i) x,
    ← integral_finsetSum _ fun i _ =>
      integrable_integral_cons h X ha has (hK i) (hKs i) (hF i) x]
  congr 1; funext s
  rw [hd, Finset.mul_sum]
  congr 1; funext i
  rw [← integral_const_mul]

theorem exists_rep {ε : ℝ} (hε : 0 < ε) : ∀ (n : ℕ) (X : Fin n → 𝔤),
    ∃ (N : ℕ) (l : Fin N → List 𝔤) (κ : Fin N → (Fin n → ℝ) → ℂ),
      (∀ i, Continuous (κ i) ∧ tsupport (κ i) ⊆ Metric.closedBall 0 ε) ∧
      ∀ f : G → ℂ, h.IsSmoothFun f → ∀ g,
        f g = ∑ i, ∫ t, κ i t * (l i).foldr h.rightDeriv f (g * h.prodExp X t)
  | 0, X => by
    refine ⟨1, fun _ => [], fun _ _ => 1, fun _ => ⟨continuous_const, ?_⟩, fun f _ g => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      simp [IsExpLieAlgebra.prodExp, hv]
  | d + 1, X => by
    obtain ⟨N, l, K, hK, hrep⟩ := exists_rep hε d (Fin.tail X)
    obtain ⟨a, ha, hu⟩ := GlobalTheory.T.exists_kernels_eval_zero_eq_sum_integral_iteratedDeriv ε hε
    refine ⟨3 * N,
      fun j => l (finProdFinEquiv.symm j).2 ++ List.replicate (finProdFinEquiv.symm j).1 (X 0),
      fun j t => a (finProdFinEquiv.symm j).1 (t 0) * K (finProdFinEquiv.symm j).2 (Fin.tail t),
      fun j => ⟨?_, tsupport_cons_kernel hε.le (ha _).2 (hK _).2⟩, fun f hf g => ?_⟩
    · exact ((ha _).1.comp (continuous_apply 0)).mul
        ((hK _).1.comp (continuous_pi fun j => continuous_apply j.succ))
    · rw [← finProdFinEquiv.sum_comp]
      simp only [Equiv.symm_apply_apply, List.foldr_append]
      rw [Fintype.sum_prod_type]
      have h0 := hu _ (GlobalTheory.T.iteratedDeriv_expG_line_eq_foldr_rightDeriv 𝔸 G 𝔤 h f hf (X 0) g 0).1
      simp only [zero_smul, h.expG_zero, mul_one] at h0
      rw [h0]
      refine Finset.sum_congr rfl fun p _ => ?_
      have hp := isSmoothFun_foldr h hf (List.replicate p (X 0))
      rw [sum_integral_cons h X hε.le (ha p).1 (ha p).2 (fun i => (hK i).1) (fun i => (hK i).2)
        (fun i => continuous_of_isSmoothFun h (isSmoothFun_foldr h hp (l i))) (hrep _ hp) g]
      congr 1; funext s
      rw [(GlobalTheory.T.iteratedDeriv_expG_line_eq_foldr_rightDeriv 𝔸 G 𝔤 h f hf (X 0) g p).2 s]

end SobolevRep

theorem exists_sobolev_representation_prodExp :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
      (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (ε : ℝ), 0 < ε →
      ∀ (n : ℕ) (X : Fin n → 𝔤),
      ∃ (N : ℕ) (l : Fin N → List 𝔤) (κ : Fin N → (Fin n → ℝ) → ℂ),
        (∀ i, Continuous (κ i) ∧ tsupport (κ i) ⊆ Metric.closedBall 0 ε) ∧
        ∀ f : G → ℂ, h.IsSmoothFun f → ∀ g,
          f g = ∑ i, ∫ t, κ i t * (l i).foldr h.rightDeriv f (g * h.prodExp X t) :=
  fun _ _ _ _ _ _ _ h _ hε n X => SobolevRep.exists_rep h hε n X

end GlobalTheory
end

open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sobolev_representation_prodExp' : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (ε : ℝ), 0 < ε → ∀ (n : ℕ) (X : Fin n → 𝔤), ∃ (N : ℕ) (l : Fin N → List 𝔤) (κ : Fin N → (Fin n → ℝ) → ℂ), (∀ i, Continuous (κ i) ∧ tsupport (κ i) ⊆ Metric.closedBall 0 ε) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ g, f g = ∑ i, ∫ t, κ i t * (l i).foldr h.rightDeriv f (g * h.prodExp X t) := by
  atlas_forward_decl GlobalTheory.exists_sobolev_representation_prodExp
end

section
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.DerivBoundIntegral

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

noncomputable def wordEnd (w : List 𝔤) : Module.End ℂ (h.smoothFuns (F := ℂ)) :=
  (w.map (h.rightDerivEnd (F := ℂ))).prod

theorem coe_wordEnd (w : List 𝔤) (f : h.smoothFuns (F := ℂ)) :
    ((wordEnd h w f : h.smoothFuns (F := ℂ)) : G → ℂ) = w.foldr h.rightDeriv (f : G → ℂ) := by
  induction w with
  | nil => simp [wordEnd]
  | cons X w ih =>
    simp only [wordEnd, List.map_cons, List.prod_cons, Module.End.mul_apply, IsExpLieAlgebra.coe_rightDerivEnd,
      List.foldr_cons] at ih ⊢
    rw [ih]

theorem wordEnd_mem (w : List 𝔤) :
    wordEnd h w ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) := by
  apply Subalgebra.list_prod_mem
  intro x hx
  obtain ⟨X, -, rfl⟩ := List.mem_map.1 hx
  exact Algebra.subset_adjoin ⟨X, rfl⟩

end GlobalTheory.DerivBoundIntegral

namespace GlobalTheory

open GlobalTheory.DerivBoundIntegral in

theorem derivWord_le_integral_of_aeval_casimir_eq_zero :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∃ K : Set G, IsCompact K ∧ ∀ l : List 𝔤, ∃ C : ℝ, ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ‖l.foldr h.rightDeriv (f : G → ℂ) 1‖ ≤ C * ∫ x in K, ‖(f : G → ℂ) x‖ ∂μ := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b P hP _ _ μ hμ
  obtain ⟨Kc, hKc, hD⟩ := GlobalTheory.T.exists_interior_estimate_deriv_word_polyLaplacian 𝔸 G 𝔤 h d b P hP
  obtain ⟨ρ, hρ, hH⟩ := GlobalTheory.T.exists_setIntegral_norm_prodExp_mul_le_haar 𝔸 G 𝔤 h d b μ hμ
  obtain ⟨C₀, K, hC₀, hK, hHK⟩ := hH Kc hKc
  obtain ⟨N, lw, κ, hκ, hrep⟩ := GlobalTheory.T.exists_sobolev_representation_prodExp' 𝔸 G 𝔤 h ρ hρ d (⇑b)
  refine ⟨K, hK, fun l => ?_⟩
  have hS : ∀ i, ∃ S : ℝ, 0 ≤ S ∧ ∀ t, ‖κ i t‖ ≤ S := by
    intro i
    have hcs : HasCompactSupport (κ i) :=
      (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hκ i).2
    obtain ⟨S, hS⟩ := (hκ i).1.bounded_above_of_compact_support hcs
    exact ⟨max S 0, le_max_right _ _, fun t => (hS t).trans (le_max_left _ _)⟩
  choose S hS0 hS using hS
  choose C hC0 hC using fun i => hD (lw i ++ l)
  set Δ := ∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i) with hΔ
  set A := Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) with hA
  have hΔmem : Δ ∈ A := Subalgebra.sum_mem _ fun i _ =>
    Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨b i, rfl⟩) (Algebra.subset_adjoin ⟨b i, rfl⟩)
  have hPmem : Polynomial.aeval Δ P ∈ A := by
    have := Polynomial.aeval_algHom_apply A.val (⟨Δ, hΔmem⟩ : A) P
    simp only [Subalgebra.coe_val] at this
    rw [this]
    exact (Polynomial.aeval (⟨Δ, hΔmem⟩ : A) P).2
  refine ⟨∑ i, C i * (S i * C₀), fun f hf => ?_⟩
  set I := ∫ x in K, ‖(f : G → ℂ) x‖ ∂μ with hI
  have hfc : Continuous (f : G → ℂ) := by
    letI := h.chartedSpace
    exact ContMDiff.continuous f.2

  have hFs : h.IsSmoothFun ((wordEnd h l f : h.smoothFuns (F := ℂ)) : G → ℂ) := (wordEnd h l f).2
  have hrep1 := hrep _ hFs 1
  simp only [coe_wordEnd] at hrep1
  rw [hrep1]
  have hterm : ∀ i, ‖∫ t, κ i t * (lw i).foldr h.rightDeriv (l.foldr h.rightDeriv (f : G → ℂ))
      (1 * h.prodExp (⇑b) t)‖ ≤ C i * (S i * C₀) * I := by
    intro i
    obtain ⟨v, hv, hTv⟩ := GlobalTheory.T.leftSmoothing_prodExp_smooth_commute 𝔸 G 𝔤 h d (⇑b) (κ i) (hκ i).1
      ((isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hκ i).2) f
    have hkill : Polynomial.aeval Δ P v = 0 := by
      apply Subtype.ext
      funext y
      rw [hTv _ hPmem y, hf]
      simp
    have heq : ∫ t, κ i t * (lw i).foldr h.rightDeriv (l.foldr h.rightDeriv (f : G → ℂ))
        (1 * h.prodExp (⇑b) t) = (lw i ++ l).foldr h.rightDeriv (v : G → ℂ) 1 := by
      have e1 := hTv _ (wordEnd_mem h (lw i ++ l)) 1
      simp only [coe_wordEnd] at e1
      rw [e1]
      simp [List.foldr_append]
    rw [heq]
    have hvb : ∀ y ∈ Kc, ‖(v : G → ℂ) (1 * y)‖ ≤ S i * C₀ * I := by
      intro y hy
      rw [one_mul, hv y]
      have hcont : Continuous fun t : Fin d → ℝ => ‖(f : G → ℂ) (h.prodExp (⇑b) t * y)‖ :=
        (hfc.comp ((h.continuous_prodExp (⇑b)).mul continuous_const)).norm
      calc ‖∫ t, κ i t * (f : G → ℂ) (h.prodExp (⇑b) t * y)‖
          ≤ ∫ t, ‖κ i t * (f : G → ℂ) (h.prodExp (⇑b) t * y)‖ := norm_integral_le_integral_norm _
        _ = ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ,
              ‖κ i t * (f : G → ℂ) (h.prodExp (⇑b) t * y)‖ := by
            symm
            apply setIntegral_eq_integral_of_forall_compl_eq_zero
            intro t ht
            have : κ i t = 0 := image_eq_zero_of_notMem_tsupport fun h' => ht ((hκ i).2 h')
            simp [this]
        _ ≤ ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ,
              S i * ‖(f : G → ℂ) (h.prodExp (⇑b) t * y)‖ := by
            apply integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall fun t => norm_nonneg _
            · exact (continuous_const.mul hcont).continuousOn.integrableOn_compact
                (isCompact_closedBall _ _)
            · refine Filter.Eventually.of_forall fun t => ?_
              simp only [norm_mul]
              exact mul_le_mul_of_nonneg_right (hS i t) (norm_nonneg _)
        _ = S i * ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ,
              ‖(f : G → ℂ) (h.prodExp (⇑b) t * y)‖ := integral_const_mul _ _
        _ ≤ S i * (C₀ * I) := mul_le_mul_of_nonneg_left (hHK _ hfc y hy) (hS0 i)
        _ = S i * C₀ * I := by ring
    have := hC i v hkill 1 (S i * C₀ * I) hvb
    calc _ ≤ C i * (S i * C₀ * I) := this
      _ = _ := by ring
  calc ‖∑ i, ∫ t, κ i t * (lw i).foldr h.rightDeriv (l.foldr h.rightDeriv (f : G → ℂ))
        (1 * h.prodExp (⇑b) t)‖
      ≤ ∑ i, ‖∫ t, κ i t * (lw i).foldr h.rightDeriv (l.foldr h.rightDeriv (f : G → ℂ))
        (1 * h.prodExp (⇑b) t)‖ := norm_sum_le _ _
    _ ≤ ∑ i, C i * (S i * C₀) * I := Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, C i * (S i * C₀)) * I := (Finset.sum_mul _ _ _).symm

end GlobalTheory
end

open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_derivWord_bound_of_aeval_casimir : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∃ K : Set G, IsCompact K ∧ ∀ l : List 𝔤, ∃ C : ℝ, ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ‖l.foldr h.rightDeriv (f : G → ℂ) 1‖ ≤ C * ∫ x in K, ‖(f : G → ℂ) x‖ ∂μ := by
  atlas_forward_decl GlobalTheory.derivWord_le_integral_of_aeval_casimir_eq_zero
end

section
section
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

theorem solGFam_foldr_rightDeriv_leftTranslate (l : List 𝔤) (f : G → ℂ) (x : G) :
    l.foldr h.rightDeriv (fun y => f (x * y)) = fun y => l.foldr h.rightDeriv f (x * y) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    funext g
    simp only [List.foldr_cons, ih]
    simp only [IsExpLieAlgebra.rightDeriv, mul_assoc]

theorem solGFam_isSmoothFun_foldr_rightDeriv (l : List 𝔤) {f : G → ℂ} (hf : h.IsSmoothFun f) :
    h.IsSmoothFun (l.foldr h.rightDeriv f) := by
  induction l with
  | nil => exact hf
  | cons X l ih => exact h.isSmoothFun_rightDeriv ih X

theorem solGFam_foldr_rightDeriv_smul_add (l : List 𝔤) {f f' : G → ℂ} (hf : h.IsSmoothFun f)
    (hf' : h.IsSmoothFun f') (c : ℂ) :
    l.foldr h.rightDeriv (c • f + f') = c • l.foldr h.rightDeriv f + l.foldr h.rightDeriv f' := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    simp only [List.foldr_cons, ih]
    have h1 := GlobalTheory.HCA.solGFam_isSmoothFun_foldr_rightDeriv h l hf
    have h2 := GlobalTheory.HCA.solGFam_isSmoothFun_foldr_rightDeriv h l hf'
    have h3 : h.IsSmoothFun (c • l.foldr h.rightDeriv f) := (h.smoothFuns (F := ℂ)).smul_mem c h1
    rw [h.rightDeriv_add h3 h2, h.rightDeriv_smul h1]

end GlobalTheory.HCA

theorem GlobalTheory.HCA.solG_smFn : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → (∀ f ∈ solG h b P, Continuous f) ∧ (∀ f ∈ solG h b P, ∀ g, (fun y => f (g * y)) ∈ solG h b P) ∧ ∃ K : Set G, IsCompact K ∧ ∀ l₀ : List 𝔤, SmFn h b μ (solG h b P) K fun l f => (l.map b ++ l₀).foldr h.rightDeriv f 1 := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b P hP _ _ μ hμ
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨hs, -⟩ := (mem_solG h b).1 hf
    letI := h.chartedSpace
    exact ContMDiff.continuous hs
  · intro f hf g
    obtain ⟨hs, h0⟩ := (mem_solG h b).1 hf
    obtain ⟨f', hf'1, hf'2⟩ := GlobalTheory.T.leftTranslate_smooth_commute_leftInvariantOps 𝔸 G 𝔤 h ⟨f, hs⟩ g
    have hΔ : (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) ∈
        Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) :=
      Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _
        (Algebra.subset_adjoin ⟨b i, rfl⟩) (Algebra.subset_adjoin ⟨b i, rfl⟩)
    have hT : Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P ∈
        Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 hΔ) (Polynomial.aeval_mem_adjoin_singleton ℂ _)
    have e : (f' : G → ℂ) = fun y => f (g * y) := funext hf'1
    rw [mem_solG]
    refine ⟨e ▸ f'.2, ?_⟩
    have hf'eq : (⟨fun y => f (g * y), e ▸ f'.2⟩ : h.smoothFuns (F := ℂ)) = f' := Subtype.ext e.symm
    rw [hf'eq]
    ext y
    rw [hf'2 _ hT y, h0]
    rfl
  · obtain ⟨K, hK, hC⟩ := GlobalTheory.T.exists_compact_derivWord_bound_of_aeval_casimir 𝔸 G 𝔤 h d b P hP μ hμ
    refine ⟨K, hK, fun l₀ => ⟨?_, ?_, ?_⟩⟩
    · intro l f hf f' hf' c
      obtain ⟨hs, -⟩ := (mem_solG h b).1 hf
      obtain ⟨hs', -⟩ := (mem_solG h b).1 hf'
      simp only [GlobalTheory.HCA.solGFam_foldr_rightDeriv_smul_add h _ hs hs' c, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · intro l
      obtain ⟨C, hC'⟩ := hC (l.map b ++ l₀)
      refine ⟨C, fun f hf => ?_⟩
      obtain ⟨hs, h0⟩ := (mem_solG h b).1 hf
      exact hC' ⟨f, hs⟩ h0
    · intro l i f hf
      obtain ⟨hs, -⟩ := (mem_solG h b).1 hf
      have hL := GlobalTheory.HCA.solGFam_isSmoothFun_foldr_rightDeriv h (l.map b ++ l₀) hs
      have hd := h.hasDerivAt_rightDeriv hL (b i) 1
      simp only [List.map_cons, List.cons_append, List.foldr_cons]
      refine hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [GlobalTheory.HCA.solGFam_foldr_rightDeriv_leftTranslate h, mul_one, one_mul]
end

open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laplacePolynomialKernel_derivativeWords_family : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → (∀ f ∈ solG h b P, Continuous f) ∧ (∀ f ∈ solG h b P, ∀ g, (fun y => f (g * y)) ∈ solG h b P) ∧ ∃ K : Set G, IsCompact K ∧ ∀ l₀ : List 𝔤, SmFn h b μ (solG h b P) K fun l f => (l.map b ++ l₀).foldr h.rightDeriv f 1 := by
  atlas_forward_decl GlobalTheory.HCA.solG_smFn
end

section
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem foldr_rightDeriv_leftTranslate {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
    (l : List 𝔤) (f : G → ℂ) (g : G) :
    l.foldr h.rightDeriv (fun y => f (g * y)) = fun x => l.foldr h.rightDeriv f (g * x) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    simp only [List.foldr_cons, ih]
    exact h.rightDeriv_leftTranslate X (l.foldr h.rightDeriv f) g

theorem exists_alpha_convolution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ l : List 𝔤, ∃ α : G → ℂ, h.IsSmoothFun α ∧ Continuous α ∧ HasCompactSupport α ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ g, ∫ y, (f : G → ℂ) (g * y) * α y ∂μ = l.foldr h.rightDeriv (f : G → ℂ) g := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b P hP _ _ μ hμ l
  obtain ⟨hcont, hinv, K, hK, hfam⟩ := GlobalTheory.T.laplacePolynomialKernel_derivativeWords_family 𝔸 G 𝔤 h d b P hP μ hμ
  obtain ⟨α, hαs, hαc, hα⟩ := GlobalTheory.T.first_functional_integral_smooth_compact 𝔸 G 𝔤 h d b μ hμ (solG h b P) hcont hinv K hK _ (hfam l)
  refine ⟨α, hαs, ?_, hαc, ?_⟩
  · letI := h.chartedSpace
    exact hαs.continuous
  · intro f hf g
    have hmem : (f : G → ℂ) ∈ solG h b P := (mem_solG h b).2 ⟨f.2, hf⟩
    have h1 := hα _ (hinv _ hmem g)
    simp only [List.map_nil, List.nil_append] at h1
    rw [h1, foldr_rightDeriv_leftTranslate h l (f : G → ℂ) g]
    simp only [mul_one]

end GlobalTheory.HCA
end

open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_convolution_eq_derivative : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ l : List 𝔤, ∃ α : G → ℂ, h.IsSmoothFun α ∧ Continuous α ∧ HasCompactSupport α ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ g, ∫ y, (f : G → ℂ) (g * y) * α y ∂μ = l.foldr h.rightDeriv (f : G → ℂ) g := by
  atlas_forward_decl GlobalTheory.HCA.exists_alpha_convolution
end
