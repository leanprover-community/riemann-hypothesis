import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormulaStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalProperties
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreserving
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapVanishing
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionalSideGrowth
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsKTypeNonzeroBessel

section
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselAdjoint

theorem integral_comp_involution {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} {T : X → X} (hT : MeasurePreserving T μ μ) (hTT : ∀ᵐ p ∂μ, T (T p) = p) (f : X → E) :
    ∫ p, f (T p) ∂μ = ∫ p, f p ∂μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · have h1 : AEStronglyMeasurable f (μ.map T) := by rw [hT.map_eq]; exact hf
    rw [← integral_map hT.measurable.aemeasurable h1, hT.map_eq]
  · have hg : ¬ AEStronglyMeasurable (fun p => f (T p)) μ := by
      intro hg
      apply hf
      refine (hg.comp_measurePreserving hT).congr ?_
      filter_upwards [hTT] with p hp
      simp [hp]
    rw [integral_non_aestronglyMeasurable hf, integral_non_aestronglyMeasurable hg]

def adjR (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] :
    (W →L[ℂ] W) →ₗᵢ[ℝ] (W →L[ℂ] W) where
  toFun A := ContinuousLinearMap.adjoint A
  map_add' A B := map_add _ A B
  map_smul' c A := by
    have e : ∀ B : W →L[ℂ] W, c • B = (c : ℂ) • B := fun B => by
      ext x; simp
    rw [RingHom.id_apply, e, e, map_smulₛₗ]; simp
  norm_map' A := ContinuousLinearMap.adjoint.norm_map A

theorem adjoint_integral {X W : Type*} [MeasurableSpace X] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] (μ : Measure X) (f : X → (W →L[ℂ] W)) :
    ContinuousLinearMap.adjoint (∫ p, f p ∂μ) = ∫ p, ContinuousLinearMap.adjoint (f p) ∂μ :=
  ((adjR W).integral_comp_comm f).symm

theorem adjoint_be : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.TK, ContinuousLinearMap.adjoint (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v w := by
  intro _ k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS _ hOK hS v _ w _
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, -, -⟩ := hS
  obtain ⟨-, hinv, -, -, -, hae⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r z μW μN hOK.1 hz hT hW hN
  obtain ⟨-, -, hψi, hψc, hUW, hNG⟩ := GlobalTheory.BesselPsi.psi_character k r z Formalism.QuantumDeterminants.cStd hz
  unfold be
  rw [adjoint_integral, ← integral_comp_involution hinv ?_ (beInt z Formalism.QuantumDeterminants.cStd π R.σ v w)]
  · refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hi, hhi, hih⟩ := P.MatrixMultiplicationContinuity.uw_inv hp1
    have hg1 : Matrix.of p.1 ∈ GG k r := hp1.1
    have hg2 : Matrix.of p.2 ∈ GG k r := hp2.1
    have hg : Matrix.of p.1 * Matrix.of p.2 ∈ GG k r := by
      have a1 : (Matrix.of p.1)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of p.1 = Formalism.QuantumDeterminants.Hpk k r := hg1
      have a2 : (Matrix.of p.2)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of p.2 = Formalism.QuantumDeterminants.Hpk k r := hg2
      show (Matrix.of p.1 * Matrix.of p.2)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p.1 * Matrix.of p.2) = Formalism.QuantumDeterminants.Hpk k r
      calc _ = (Matrix.of p.2)ᴴ * ((Matrix.of p.1)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of p.1) * Matrix.of p.2 := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [a1, a2]
    have hii : ((Matrix.of p.1)⁻¹)⁻¹ = (Matrix.of p.1 : Mx k r) := Matrix.inv_eq_left_inv hhi
    have e1 : (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) =
        ((Matrix.of p.1 * Matrix.of p.2)⁻¹ : Mx k r) := by
      rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hih, Matrix.one_mul]
    have e2 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) =
        star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2)) := by
      rw [(hψc _ hp1 _ (hψi _ hp2).1).2.2.1, (hψi _ hp2).2]
    have e3 : ContinuousLinearMap.adjoint (π (Matrix.of p.1)⁻¹) = π (Matrix.of p.1) := by
      symm
      rw [ContinuousLinearMap.eq_adjoint_iff]
      intro x y
      rw [P.MatrixMultiplicationContinuity.piW_inner hT hπ hi, hii]
    show ContinuousLinearMap.adjoint ((⟪v, R.σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ *
        star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹) =
      (⟪w, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹)) v⟫_ℂ *
        star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹))) •
        π ((Matrix.of p.1)⁻¹)⁻¹
    rw [e1, e2, hii, map_smulₛₗ, e3, P.MatrixMultiplicationContinuity.sigma_inner hDS.2 hg v w, map_mul, inner_conj_symm]
    rfl
  · filter_upwards [hae] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hi, hhi, hih⟩ := P.MatrixMultiplicationContinuity.uw_inv hp1
    obtain ⟨-, hni, hin⟩ := P.MatrixMultiplicationContinuity.uh_inv hp2.1
    have hii : ((Matrix.of p.1)⁻¹)⁻¹ = (Matrix.of p.1 : Mx k r) := Matrix.inv_eq_left_inv hhi
    have hnn : ((Matrix.of p.2)⁻¹)⁻¹ = (Matrix.of p.2 : Mx k r) := Matrix.inv_eq_left_inv hni
    have e : (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹)⁻¹ * ((Matrix.of p.1)⁻¹)⁻¹ =
        (Matrix.of p.2 : Mx k r) := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hii, hnn, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hih,
        Matrix.one_mul, Matrix.mul_assoc, hih, Matrix.mul_one]
    exact Prod.ext hii e

end GlobalTheory.BesselAdjoint
end
end

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_besselIntegral_eq_swap_of_gap : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.TK, ContinuousLinearMap.adjoint (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v w := by
  atlas_forward_decl GlobalTheory.BesselAdjoint.adjoint_be
end

section
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem hermitian_rankOne_kernel_shape : ∀ (T W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] (l₀ La : T → W), (∀ v w, ContinuousLinearMap.adjoint ((innerSL ℂ (La v)).smulRight (l₀ w)) = (innerSL ℂ (La w)).smulRight (l₀ v)) → (∀ v ξ, (⟪ξ, ((innerSL ℂ (La v)).smulRight (l₀ v)) ξ⟫_ℂ).im = 0 ∧ 0 ≤ (⟪ξ, ((innerSL ℂ (La v)).smulRight (l₀ v)) ξ⟫_ℂ).re) → (∃ v, l₀ v ≠ 0) → ∃ c : ℝ, 0 ≤ c ∧ ∀ v, La v = (c : ℂ) • l₀ v := by
  intro T W _ _ _ l₀ La hadj hpos ⟨v₀, hv₀⟩
  set a : ℂ := ⟪La v₀, l₀ v₀⟫_ℂ with ha
  set n : ℝ := ‖l₀ v₀‖ ^ 2 with hn
  have hnpos : 0 < n := by rw [hn]; exact pow_pos (norm_pos_iff.mpr hv₀) 2
  have hnn : ⟪l₀ v₀, l₀ v₀⟫_ℂ = (n : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hn]; simp
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  obtain ⟨him, hre⟩ := hpos v₀ (l₀ v₀)
  have e : ⟪l₀ v₀, ((innerSL ℂ (La v₀)).smulRight (l₀ v₀)) (l₀ v₀)⟫_ℂ = a * (n : ℂ) := by
    rw [ContinuousLinearMap.smulRight_apply, inner_smul_right, hnn, innerSL_apply_apply]
  rw [e] at him hre
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_add, sub_zero] at him hre
  have haim : a.im = 0 := (mul_eq_zero.mp him).resolve_right hnpos.ne'
  have hare : 0 ≤ a.re := nonneg_of_mul_nonneg_left hre hnpos
  have hareal : a = (a.re : ℂ) := Complex.ext (by simp) (by simp [haim])
  refine ⟨a.re / n, div_nonneg hare hnpos.le, fun v => ?_⟩
  have key : (n : ℂ) • La v = a • l₀ v := by
    apply ext_inner_right ℂ
    intro y
    have h := ContinuousLinearMap.adjoint_inner_left
      ((innerSL ℂ (La v)).smulRight (l₀ v₀)) y (l₀ v₀)
    rw [hadj v v₀, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, innerSL_apply_apply, inner_smul_right, hnn, ← ha] at h
    rw [h, inner_smul_left, Complex.conj_ofReal, mul_comm]
  have : La v = (n : ℂ)⁻¹ • ((n : ℂ) • La v) := by rw [smul_smul, inv_mul_cancel₀ hnc, one_smul]
  rw [this, key, smul_smul]
  congr 1
  rw [Complex.ofReal_div, ← hareal, div_eq_inv_mul]

end GlobalTheory
end

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_rank_one_proportional : ∀ (T W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] (l₀ La : T → W), (∀ v w, ContinuousLinearMap.adjoint ((innerSL ℂ (La v)).smulRight (l₀ w)) = (innerSL ℂ (La w)).smulRight (l₀ v)) → (∀ v ξ, (⟪ξ, ((innerSL ℂ (La v)).smulRight (l₀ v)) ξ⟫_ℂ).im = 0 ∧ 0 ≤ (⟪ξ, ((innerSL ℂ (La v)).smulRight (l₀ v)) ξ⟫_ℂ).re) → (∃ v, l₀ v ≠ 0) → ∃ c : ℝ, 0 ≤ c ∧ ∀ v, La v = (c : ℂ) • l₀ v := by
  atlas_forward_decl GlobalTheory.hermitian_rankOne_kernel_shape
end

section
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besselIntegral_sesquilinear : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (w + w') v = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w' v ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (a • w) v = a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, ∀ v' ∈ R.TK, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (v + v') = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v' ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (a • v) = star a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v := by
  intro H k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq h1 h2 h3 h4
  have hc := GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap H k r ε mu h R Wp z π u μW μN μG νq h1 h2 h3 h4
  refine ⟨fun v hv w hw w' hw' a => ⟨?_, ?_⟩, fun w hw v hv v' hv' a => ⟨?_, ?_⟩⟩
  · unfold be
    rw [← integral_add ((hc v hv).1 w hw) ((hc v hv).1 w' hw')]
    congr 1
    funext p
    simp only [beInt, map_add, inner_add_right, add_smul, mul_add, add_mul, smul_add]
  · unfold be
    rw [← integral_smul]
    congr 1
    funext p
    simp only [beInt, map_smul, inner_smul_right, smul_smul, mul_assoc, mul_left_comm]
  · unfold be
    rw [← integral_add ((hc v hv).1 w hw) ((hc v' hv').1 w hw)]
    congr 1
    funext p
    simp only [beInt, inner_add_left, add_smul, mul_add, add_mul, smul_add]
  · unfold be
    rw [← integral_smul]
    congr 1
    funext p
    simp only [beInt, inner_smul_left, smul_smul, mul_assoc, mul_left_comm, RCLike.star_def]

end GlobalTheory
end

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_gap_pairing : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (w + w') v = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w' v ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (a • w) v = a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, ∀ v' ∈ R.TK, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (v + v') = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v' ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (a • v) = star a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v := by
  atlas_forward_decl GlobalTheory.besselIntegral_sesquilinear
end

section
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselEquiv

theorem integral_smul_comp_of_measurePreserving {X Wp : Type} [MeasurableSpace X] [NormedAddCommGroup Wp]
    [NormedSpace ℂ Wp] [CompleteSpace Wp] {μ : Measure X} {T : X → X} (hT : MeasurePreserving T μ μ)
    {F F' : X → (Wp →L[ℂ] Wp)} (hF : Integrable F μ) (c : ℂ) (A : Wp →L[ℂ] Wp)
    (h : ∀ᵐ p ∂μ, F' p = c • A.comp (F (T p))) :
    ∫ p, F' p ∂μ = c • A.comp (∫ p, F p ∂μ) := by
  have hFT : Integrable (fun p => F (T p)) μ := hT.integrable_comp_of_integrable hF
  have e1 : ∫ p, F (T p) ∂μ = ∫ p, F p ∂μ := by
    have := integral_map (μ := μ) (φ := T) (f := F) hT.measurable.aemeasurable
      (by rw [hT.map_eq]; exact hF.aestronglyMeasurable)
    rw [hT.map_eq] at this
    exact this.symm
  rw [integral_congr_ae h, integral_smul, ← e1]
  congr 1
  exact (ContinuousLinearMap.compL ℂ Wp Wp Wp A).integral_comp_comm hFT

theorem be_equivariant : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (g * m) w) v = Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m • (π g).comp (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hS v hv w hw g hg m hm
  have hint := (GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS v hv).1 w hw
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, -, -⟩ := hS
  obtain ⟨hψ1, hψm, -, hψc, hUW, hNG⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r z Formalism.QuantumDeterminants.cStd hz
  obtain ⟨hmp, -, -, -, -, hae⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r z μW μN hok.1 hz hT hW hN
  have hσ := (GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS).1
  have hπm := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ).2.1
  have hGm : ∀ a ∈ GG k r, ∀ b ∈ GG k r, a * b ∈ GG k r := by
    intro a ha b hb
    have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
    have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
    show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
    calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [ha', hb']
  unfold be
  refine integral_smul_comp_of_measurePreserving (hmp g hg m hm).1 hint _ _ ?_
  filter_upwards [hae] with p hp
  obtain ⟨ha, hn⟩ := hp
  have key : ∀ a ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r,
      (⟪v, R.σ (a * n) (R.σ (g * m) w)⟫_ℂ * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd n)) • π a⁻¹ =
      Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m • (π g).comp
        ((⟪v, R.σ (a * g * (g⁻¹ * n * g * m)) w⟫_ℂ *
          star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (g⁻¹ * n * g * m))) • π (a * g)⁻¹) := by
    intro a ha n hn
    obtain ⟨hag, -, haG⟩ := hUW a ha g hg
    have hgG := (hUW g hg g hg).2.2
    obtain ⟨-, hgg, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hg
    obtain ⟨hagi, -, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hag
    obtain ⟨-, hc, -, hcψ⟩ := hψc g hg n hn
    have e1 : a * g * (g⁻¹ * n * g * m) = a * n * (g * m) := by
      calc a * g * (g⁻¹ * n * g * m) = a * (g * g⁻¹) * n * (g * m) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hgg, Matrix.mul_one]
    have e2 : g * (a * g)⁻¹ = a⁻¹ := by
      rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, hgg, Matrix.one_mul]
    have e3 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ1 m]; simp
    rw [e1, hσ _ (hGm a haG n (hNG n hn)) _ (hGm g hgG m (hNG m hm)), (hψm _ hc m hm).2, hcψ,
      ContinuousLinearMap.comp_smul, ← hπm g hg _ hagi, e2, smul_smul, star_mul']
    congr 1
    linear_combination (-(⟪v, R.σ (a * n) (R.σ (g * m) w)⟫_ℂ * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd n))) * e3
  exact key _ ha _ hn

end GlobalTheory.BesselEquiv
end

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_integral_equivariant_of_gap : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (g * m) w) v = Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m • (π g).comp (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  atlas_forward_decl GlobalTheory.BesselEquiv.be_equivariant
end

section
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem be_apply_isBes : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ ξ : Wp, IsBes R z π (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hS v hv ξ
  obtain ⟨-, C, Ws, hWs, hC⟩ := GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS v hv
  obtain ⟨hlin, -⟩ := GlobalTheory.T.bessel_gap_pairing hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS
  have heq := GlobalTheory.T.bessel_integral_equivariant_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS v hv
  refine ⟨fun w hw w' hw' => ?_, fun a w hw => ?_, fun g hg m hm w hw => ?_, ‖ξ‖ * C, Ws, hWs, fun w hw => ?_⟩
  · simp only [(hlin v hv w hw w' hw' 0).1, ContinuousLinearMap.add_apply]
  · simp only [(hlin v hv w hw w hw a).2, ContinuousLinearMap.smul_apply]
  · simp only [heq w hw g hg m hm, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [mul_comm, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC w hw) (norm_nonneg _)

end GlobalTheory
end

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBes_bessel_integral_of_gap : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ ξ : Wp, IsBes R z π (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ) := by
  atlas_forward_decl GlobalTheory.be_apply_isBes
end

section
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselShape

theorem bessel_shape : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∃ w ∈ R.sm, ∃ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ≠ 0) → ∃ (l₀ La : R.H → Wp), IsBes R z π l₀ ∧ NzOn R l₀ ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v = (innerSL ℂ (La v)).smulRight (l₀ w) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hG hOK hS hne
  obtain ⟨w₀, hw₀, v₀, hv₀, hne⟩ := hne
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w₀ v₀ ξ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (ContinuousLinearMap.ext hcon)
  have hB := GlobalTheory.T.isBes_bessel_integral_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hG hOK hS
  have hnz : NzOn R (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v₀ ξ₀) := ⟨w₀, hw₀, hξ₀⟩
  set y₀ := be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w₀ v₀ ξ₀ with hy₀
  have hyy : ⟪y₀, y₀⟫_ℂ ≠ 0 := fun h0 => hξ₀ (inner_self_eq_zero.mp h0)
  refine ⟨fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v₀ ξ₀,
    fun v => (starRingEnd ℂ (⟪y₀, y₀⟫_ℂ)⁻¹) •
      ContinuousLinearMap.adjoint (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w₀ v) y₀,
    hB v₀ hv₀ ξ₀, hnz, ?_⟩
  intro w hw v hv
  ext ξ
  obtain ⟨c, hc⟩ := GlobalTheory.BesselLine.bessel_line hH k r ε mu R Wp z π u μW μN μG νq _ _ hDS hS
    (hB v₀ hv₀ ξ₀) hnz (hB v hv ξ)
  have h1 := hc w hw
  have h2 := hc w₀ hw₀
  rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left, h2, h1, ← hy₀, inner_smul_right, Complex.conj_conj]
  congr 1
  field_simp

end GlobalTheory.BesselShape
end

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_gap_exists_nonzero : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∃ w ∈ R.sm, ∃ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ≠ 0) → ∃ (l₀ La : R.H → Wp), IsBes R z π l₀ ∧ NzOn R l₀ ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v = (innerSL ℂ (La v)).smulRight (l₀ w) := by
  atlas_forward_decl GlobalTheory.BesselShape.bessel_shape
end

section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_normalised_bessel_map : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∃ l, IsBeL R z π μW μN l := by
  intro H k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hside
  have hconv := GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap H k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside
  by_cases hz : ∃ w ∈ R.sm, ∃ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ≠ 0
  · obtain ⟨l₀, La, hB, hnz, hshape⟩ :=
      GlobalTheory.T.bessel_gap_exists_nonzero H k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside hz
    have hTK : ∀ v ∈ R.TK, v ∈ R.sm :=
      (GlobalTheory.rep_basic_of_isDS H.1.2.2.1 k r ε mu R hDS).2.2.2.2.1
    obtain ⟨v₀, hv₀, hl₀⟩ := GlobalTheory.bessel_nonzero_on_translates H k r ε mu R Wp z π l₀ hDS hB hnz
    obtain ⟨c₀, -, hc₀⟩ := GlobalTheory.BesselDegree.schur_fdeg H k r ε μG hside.2.2.2.2.2.2.1
    have hP := GlobalTheory.T.bessel_integral_l2_norm_eq_div_formal_degree H k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside _ (hc₀ mu R hDS).1
    have hadj := GlobalTheory.T.adjoint_besselIntegral_eq_swap_of_gap H k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside
    obtain ⟨c, hc, hLa⟩ := GlobalTheory.T.positive_rank_one_proportional R.TK Wp (fun v => l₀ v) (fun v => La v)
      (fun v w => by
        have := hadj v v.2 w w.2
        rwa [hshape w (hTK _ w.2) v v.2, hshape v (hTK _ v.2) w w.2] at this)
      (fun v ξ => by
        have := hP v v.2 ξ
        rw [hshape v (hTK _ v.2) v v.2] at this
        exact ⟨this.1, this.2.1⟩)
      ⟨⟨v₀, hv₀⟩, hl₀⟩
    refine ⟨fun w => ((Real.sqrt c : ℝ) : ℂ) • l₀ w, Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul hB _, ?_⟩
    intro w hw v hv
    refine ⟨(hconv v hv).1 w hw, ?_⟩
    have hv' : La v = (c : ℂ) • l₀ v := hLa ⟨v, hv⟩
    rw [hshape w hw v hv, hv']
    ext ξ
    have hs : ((Real.sqrt c : ℝ) : ℂ) * ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, Complex.conj_ofReal,
      smul_smul]
    congr 1
    rw [← hs]; ring
  · push Not at hz
    refine ⟨fun _ => 0, Formalism.FourierDecayAlt.P.DDSmoothness.bessel_zero, ?_⟩
    intro w hw v hv
    refine ⟨(hconv v hv).1 w hw, ?_⟩
    rw [hz w hw v hv]
    ext ξ
    simp

end GlobalTheory
end
