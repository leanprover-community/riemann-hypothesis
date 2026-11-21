import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordHolomorphicAndUniform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateEisensteinHolomorphicDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixOneParameterGroupEqExpOfContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdOfFnEqSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinResidueHolomorphicRegion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSettingHeightContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite

section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory

theorem eval_center_eq_circleIntegral_shifted_order : ∀ {X : Type} (s₀ : ℂ) (k k₀ : ℕ) (r : ℝ) (V : Set ℂ) (Eis H H₀ : ℂ → X → ℂ), 0 < r → IsOpen V →
    Metric.closedBall s₀ r ⊆ V → (∀ g, DifferentiableOn ℂ (H · g) V) → (∀ g, DifferentiableOn ℂ (H₀ · g) V) →
    (∀ s ∈ V, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Eis s g) →
    (∀ s ∈ V, s ≠ s₀ → ∀ g, H₀ s g = (s - s₀) ^ k₀ * Eis s g) →
    ∀ g, H s₀ g = (2 * ↑Real.pi * Complex.I)⁻¹ * circleIntegral (fun z => (z - s₀) ^ ((k : ℤ) - k₀ - 1) * H₀ z g) s₀ r := by
  intro X s₀ k k₀ r V Eis H H₀ hr hV hball hH hH₀ hHE hH₀E g
  have hdc : DiffContOnCl ℂ (H · g) (Metric.ball s₀ r) :=
    ((hH g).mono (by
      intro z hz; exact hball (Metric.closure_ball_subset_closedBall hz))).diffContOnCl
  have hc := hdc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (Metric.mem_ball_self hr)
  simp only [smul_eq_mul] at hc
  rw [← hc]
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro z hz
  have hzV : z ∈ V := hball (Metric.sphere_subset_closedBall hz)
  have hne : z - s₀ ≠ 0 := by
    intro h0
    rw [Metric.mem_sphere, dist_eq_norm, h0, norm_zero] at hz
    exact hr.ne' hz.symm
  have hz' : z ≠ s₀ := sub_ne_zero.mp hne
  simp only
  rw [hHE z hzV hz' g, hH₀E z hzV hz' g]
  rw [← mul_assoc, ← mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_neg_one, ← zpow_add₀ hne, ← zpow_add₀ hne]
  congr 2
  ring

end GlobalTheory
end

section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
namespace GlobalTheory

theorem circleIntegral_zpow_mul_holo_sum {X : Type} (s₀ : ℂ) (r : ℝ) (V : Set ℂ)
    (Φ : ℂ → X → ℂ) (hr : 0 < r) (hV : IsOpen V) (hball : Metric.closedBall s₀ r ⊆ V)
    (hΦ : ∀ g, DifferentiableOn ℂ (Φ · g) V) :
    ∀ n : ℕ, ∀ (χ : ℂ → ℂ) (j : ℤ), DifferentiableOn ℂ χ V → (-j).toNat = n →
    ∃ c : ℕ → ℂ, ∀ g, circleIntegral (fun z => (z - s₀) ^ j * (χ z * Φ z g)) s₀ r =
      ∑ i ∈ Finset.range (-j).toNat, c i * circleIntegral (fun z => (z - s₀) ^ (j + i) * Φ z g) s₀ r := by
  have hs₀V : V ∈ 𝓝 s₀ := hV.mem_nhds (hball (Metric.mem_closedBall_self hr.le))
  have hsph : ∀ z ∈ Metric.sphere s₀ r, z - s₀ ≠ 0 := by
    intro z hz h
    rw [Metric.mem_sphere, dist_eq_norm, h, norm_zero] at hz
    exact hr.ne hz
  have hzpow : ∀ k : ℤ, ContinuousOn (fun z : ℂ => (z - s₀) ^ k) (Metric.sphere s₀ r) := by
    intro k
    exact ((continuousOn_id.sub continuousOn_const)).zpow₀ k (fun z hz => Or.inl (hsph z hz))
  have hsphV : Metric.sphere s₀ r ⊆ V := Metric.sphere_subset_closedBall.trans hball
  intro n
  induction n with
  | zero =>
    intro χ j hχ hn
    refine ⟨0, fun g => ?_⟩
    rw [hn, Finset.sum_range_zero]
    have hj : 0 ≤ j := by omega
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    simp only [zpow_natCast]
    apply DiffContOnCl.circleIntegral_eq_zero hr.le
    have hd : DifferentiableOn ℂ (fun z => (z - s₀) ^ m * (χ z * Φ z g)) V :=
      (((differentiableOn_id.sub_const s₀).pow m)).mul (hχ.mul (hΦ g))
    exact (hd.mono (Metric.closure_ball_subset_closedBall.trans hball)).diffContOnCl
  | succ n ih =>
    intro χ j hχ hn
    have hχ' : DifferentiableOn ℂ (dslope χ s₀) V := (Complex.differentiableOn_dslope hs₀V).2 hχ
    have hn' : (-(j + 1)).toNat = n := by omega
    obtain ⟨c', hc'⟩ := ih (dslope χ s₀) (j + 1) hχ' hn'
    refine ⟨fun i => Nat.casesOn i (χ s₀) c', fun g => ?_⟩
    have hcont : ContinuousOn (Φ · g) (Metric.sphere s₀ r) := (hΦ g).continuousOn.mono hsphV
    have hcontχ' : ContinuousOn (dslope χ s₀) (Metric.sphere s₀ r) := hχ'.continuousOn.mono hsphV
    have hsplit : circleIntegral (fun z => (z - s₀) ^ j * (χ z * Φ z g)) s₀ r =
        circleIntegral (fun z => χ s₀ * ((z - s₀) ^ j * Φ z g) +
          (z - s₀) ^ (j + 1) * (dslope χ s₀ z * Φ z g)) s₀ r := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      have h0 := hsph z hz
      have hχz : χ z = χ s₀ + (z - s₀) * dslope χ s₀ z := by
        have := sub_smul_dslope χ s₀ z
        rw [smul_eq_mul] at this
        rw [this]; ring
      simp only
      rw [hχz, zpow_add_one₀ h0]
      ring
    rw [hsplit, circleIntegral.integral_add, circleIntegral.integral_const_mul, hc' g, hn, hn',
      Finset.sum_range_succ']
    · rw [add_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        simp only [Nat.cast_succ]
        congr 2
        funext z
        congr 2
        ring
      · simp
    · exact ContinuousOn.circleIntegrable hr.le
        (continuousOn_const.mul ((hzpow j).mul hcont))
    · exact ContinuousOn.circleIntegrable hr.le
        ((hzpow (j + 1)).mul (hcontχ'.mul hcont))

theorem circleIntegral_zpow_mul_holo_mul_eq_sum {X : Type} (s₀ : ℂ) (r : ℝ) (V : Set ℂ)
    (χ : ℂ → ℂ) (Φ : ℂ → X → ℂ) : 0 < r → IsOpen V →
    Metric.closedBall s₀ r ⊆ V → DifferentiableOn ℂ χ V → (∀ g, DifferentiableOn ℂ (Φ · g) V) →
    ∀ j : ℤ, ∃ c : ℕ → ℂ, ∀ g, circleIntegral (fun z => (z - s₀) ^ j * (χ z * Φ z g)) s₀ r =
      ∑ i ∈ Finset.range (-j).toNat, c i * circleIntegral (fun z => (z - s₀) ^ (j + i) * Φ z g) s₀ r :=
  fun hr hV hball hχ hΦ j =>
    circleIntegral_zpow_mul_holo_sum s₀ r V Φ hr hV hball hΦ _ χ j hχ rfl

end GlobalTheory
end

section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.CircleCont

theorem continuous_circleIntegral_family : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (H₀ : ℂ → GAd σ J → ℂ) (s₀ : ℂ) (r : ℝ) (V : Set ℂ),
    IsOpen V → 0 < r → Metric.closedBall s₀ r ⊆ V → (∀ s ∈ V, IsSmoothModerate σ J (H₀ s)) →
    (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) V) → ∀ j : ℤ,
    Continuous fun g => circleIntegral (fun z => (z - s₀) ^ j * H₀ z g) s₀ r := by
  intro F E _ _ _ _ _ σ hσ n J hJ H₀ s₀ r V hV hr hsub hH hμ j
  have hsph : Metric.sphere s₀ r ⊆ V := Metric.sphere_subset_closedBall.trans hsub
  obtain ⟨-, N, C, hC⟩ := GlobalTheory.WeakHolFamily.word_holomorphic_and_uniform F E σ n J H₀ V (Metric.sphere s₀ r) hV
    (isCompact_sphere s₀ r) hsph hH hμ [] (by simp)
  have hhol : ∀ g, DifferentiableOn ℂ (fun s => H₀ s g) V := fun g =>
    (hμ _ (GlobalTheory.EisLine.isModerateForm_proj σ J g)).congr fun s _ => rfl
  have hcm : ∀ θ, circleMap s₀ r θ ∈ Metric.sphere s₀ r := fun θ => circleMap_mem_sphere s₀ hr.le θ
  have hht : Continuous fun g : GAd σ J => (height σ J g : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  rw [continuous_iff_continuousAt]
  intro g₀
  unfold circleIntegral
  have hne : ∀ θ, circleMap s₀ r θ - s₀ ≠ 0 := fun θ => sub_ne_zero.2 (circleMap_ne_center hr.ne')
  have hn1 : ∀ θ, ‖circleMap s₀ r θ - s₀‖ = r := fun θ => by rw [← dist_eq_norm]; exact hcm θ
  have hev : ∀ᶠ g in 𝓝 g₀, (height σ J g : ℝ) < height σ J g₀ + 1 :=
    hht.continuousAt.eventually (Iio_mem_nhds (lt_add_one _))
  simp_rw [deriv_circleMap]
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => r * (r ^ j * (|C| * ((height σ J g₀ : ℝ) + 1) ^ N))) ?_ ?_ intervalIntegrable_const ?_
  · refine Eventually.of_forall fun g => Continuous.aestronglyMeasurable ?_
    exact ((continuous_circleMap 0 r).mul continuous_const).smul
      ((((continuous_circleMap s₀ r).sub continuous_const).zpow₀ j (fun θ => Or.inl (hne θ))).mul
        ((hhol g).continuousOn.comp_continuous (continuous_circleMap s₀ r) (fun θ => hsph (hcm θ))))
  · filter_upwards [hev] with g hg
    refine ae_of_all _ fun θ _ => ?_
    rw [← circleMap_sub_center, norm_smul, norm_mul, norm_mul, norm_zpow, hn1, Complex.norm_I, mul_one]
    have h0 : (0 : ℝ) ≤ (height σ J g : ℝ) := NNReal.coe_nonneg _
    have h1 : ‖H₀ (circleMap s₀ r θ) g‖ ≤ |C| * ((height σ J g₀ : ℝ) + 1) ^ N :=
      calc ‖H₀ (circleMap s₀ r θ) g‖ ≤ C * (height σ J g : ℝ) ^ N := hC _ (hcm θ) g
        _ ≤ |C| * (height σ J g : ℝ) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| * ((height σ J g₀ : ℝ) + 1) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hg.le N) (abs_nonneg C)
    have h2 : (0 : ℝ) < r ^ j := zpow_pos hr j
    gcongr
  · refine ae_of_all _ fun θ _ => ?_
    exact ((continuous_const.mul (hH _ (hsph (hcm θ))).cont).const_smul (circleMap 0 r θ * Complex.I)).continuousAt
end GlobalTheory.CircleCont
end
end

section
section
open scoped TensorProduct NNReal Matrix ContDiff
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.CircleSmooth

section Banach

open GlobalTheory.ClosedMatGroup

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem exists_coords_deriv [FiniteDimensional ℝ 𝔸] {S : Set 𝔸} (hc : IsClosed S)
    (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S) :
    ∃ (d : ℕ) (Z : Fin d → 𝔸) (s : 𝔸 → Fin d → ℝ) (c : 𝔸 →L[ℝ] (Fin d → ℝ)), (∀ i, Z i ∈ lieSub S hc h1 hm) ∧
      s 1 = 0 ∧ HasFDerivAt s c 1 ∧
      ∀ᶠ X in 𝓝 (1 : 𝔸), X ∈ S → X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  obtain ⟨W, hW⟩ := (lieSub S hc h1 hm).exists_isCompl
  let L := lieSub S hc h1 hm
  let d := Module.finrank ℝ L
  let bL := Module.finBasis ℝ L
  let Z : Fin d → 𝔸 := fun i => (bL i : 𝔸)
  have hZ : ∀ i, ∀ t : ℝ, NormedSpace.exp (t • Z i) ∈ S := fun i t => (bL i).2 t
  let c : 𝔸 →L[ℝ] (Fin d → ℝ) :=
    LinearMap.toContinuousLinearMap (bL.equivFun.toLinearMap ∘ₗ L.projectionOnto W hW)
  let p : 𝔸 →L[ℝ] 𝔸 := LinearMap.toContinuousLinearMap (L.projection W hW)
  have hpc : ∀ z, ∑ i, c z i • Z i = p z := by
    intro z
    show ∑ i, (bL.equivFun (L.projectionOnto W hW z)) i • (bL i : 𝔸) = ((L.projectionOnto W hW z : L) : 𝔸)
    conv_rhs => rw [← bL.sum_equivFun (L.projectionOnto W hW z)]
    rw [Submodule.coe_sum]
    rfl
  have hqW : ∀ z, z - p z ∈ W := fun z => by
    have h := Submodule.projection_add_projection_eq_self hW z
    have e : z - p z = W.projection _ hW.symm z := by
      rw [sub_eq_iff_eq_add']; exact h.symm
    rw [e]; exact Submodule.projection_apply_mem hW.symm z
  let P : 𝔸 → 𝔸 := fun z => (List.ofFn fun i => NormedSpace.exp (c z i • Z i)).prod
  let Φ : 𝔸 → 𝔸 := fun z => P z * NormedSpace.exp (z - p z)
  have hexp : HasStrictFDerivAt NormedSpace.exp (1 : 𝔸 →L[ℝ] 𝔸) (0 : 𝔸) := hasStrictFDerivAt_exp_zero
  have hf : ∀ i, HasStrictFDerivAt (fun z => NormedSpace.exp (c z i • Z i))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (((ContinuousLinearMap.proj i).comp c).smulRight (Z i))) 0 := fun i =>
    HasStrictFDerivAt.comp (0 : 𝔸) (g := NormedSpace.exp) (by rw [map_zero, Pi.zero_apply, zero_smul]; exact hexp)
      (((ContinuousLinearMap.proj i).comp c).smulRight (Z i)).hasStrictFDerivAt
  have hP := hasStrictFDerivAt_ofFn_prod d (fun i z => NormedSpace.exp (c z i • Z i)) _ 0
    (fun i => by simp) hf
  have h2 : HasStrictFDerivAt (fun z => NormedSpace.exp (z - p z))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (ContinuousLinearMap.id ℝ 𝔸 - p)) 0 :=
    HasStrictFDerivAt.comp (0 : 𝔸) (f := fun z => z - p z) (by rw [map_zero, sub_zero]; exact hexp)
      (ContinuousLinearMap.id ℝ 𝔸 - p).hasStrictFDerivAt
  have hP0 : P 0 = 1 := by simp [P]
  have h4 : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := by
    refine (hP.mul' h2).congr_fderiv ?_
    ext1 z
    have e1 : (List.ofFn fun i => NormedSpace.exp ((0 : Fin d → ℝ) i • Z i)).prod = 1 := by simp
    simp [e1, hpc]
  have hΦ0 : Φ 0 = 1 := by
    show P 0 * NormedSpace.exp (0 - p 0) = 1
    rw [hP0, map_zero, sub_zero, NormedSpace.exp_zero, one_mul]
  let Ψ := h4.localInverse Φ _ 0
  have hΨ : Tendsto Ψ (𝓝 1) (𝓝 0) := by
    have h := h4.localInverse_tendsto
    rw [hΦ0] at h
    exact h
  have hΨ1 : Ψ 1 = 0 := by
    have h := h4.localInverse_apply_image
    rw [hΦ0] at h
    exact h
  have hΨd : HasFDerivAt Ψ (ContinuousLinearMap.id ℝ 𝔸) 1 := by
    have h := h4.to_localInverse.hasFDerivAt
    rw [hΦ0] at h
    exact h
  have hR : ∀ᶠ X in 𝓝 (1 : 𝔸), Φ (Ψ X) = X := by
    have h := h4.eventually_right_inverse
    rw [hΦ0] at h
    exact h
  have hp0 : Tendsto p (𝓝 0) (𝓝 0) := by simpa using p.continuous.tendsto 0
  have hq0 : Tendsto (fun z => z - p z) (𝓝 0) (𝓝 (0 : 𝔸)) := by
    simpa using (tendsto_id (x := 𝓝 (0 : 𝔸))).sub hp0
  refine ⟨d, Z, fun X => c (Ψ X), c, fun i => (bL i).2, ?_, ?_, ?_⟩
  · simp only [hΨ1, map_zero]
  · exact c.hasFDerivAt.comp 1 hΨd
  · filter_upwards [hR, hΨ.eventually (hq0.eventually (eventually_eq_zero hc h1 hm hi hW.disjoint))]
      with X hX1 hX2 hXS
    obtain ⟨Q, hQ, hQe⟩ := exists_left_inv_ofFn_prod h1 hm d (fun i => c (Ψ X) i • Z i)
      (fun i => by rw [← neg_smul]; exact hZ i _)
    have hE : NormedSpace.exp (Ψ X - p (Ψ X)) = Q * X := by
      conv_rhs => rw [← hX1]
      show _ = Q * ((List.ofFn fun i => NormedSpace.exp (c (Ψ X) i • Z i)).prod * NormedSpace.exp (Ψ X - p (Ψ X)))
      rw [← mul_assoc, hQe, one_mul]
    have hw := hX2 (hqW _) (by rw [hE]; exact hm _ hQ _ hXS)
    calc X = Φ (Ψ X) := hX1.symm
      _ = _ := by
        show (List.ofFn fun i => NormedSpace.exp (c (Ψ X) i • Z i)).prod * NormedSpace.exp (Ψ X - p (Ψ X)) = _
        rw [hw, NormedSpace.exp_zero, mul_one]

omit [CompleteSpace 𝔸] in

theorem contDiff_ofFn_prod {G X : Type} [Group G] [NormedAddCommGroup X] [NormedSpace ℝ X] (φ : G →* 𝔸) :
    ∀ (k : ℕ) (x : Fin k → X → G), (∀ i, ContDiff ℝ ∞ (fun t => φ (x i t)) ∧ ContDiff ℝ ∞ fun t => φ (x i t)⁻¹) →
      ContDiff ℝ ∞ (fun t => φ (List.ofFn fun i => x i t).prod) ∧
        ContDiff ℝ ∞ fun t => φ (List.ofFn fun i => x i t).prod⁻¹ := by
  intro k
  induction k with
  | zero => intro x _; simp only [List.ofFn_zero, List.prod_nil]; exact ⟨contDiff_const, contDiff_const⟩
  | succ k ih =>
    intro x hx
    obtain ⟨h1, h2⟩ := ih (fun i => x i.succ) fun i => hx _
    simp only [List.ofFn_succ, List.prod_cons, mul_inv_rev, map_mul]
    exact ⟨(hx 0).1.mul h1, h2.mul (hx 0).2⟩

end Banach

theorem prod_ofFn_single {M : Type*} [Monoid M] : ∀ {d : ℕ} (g : Fin d → M) (j : Fin d),
    (∀ i, i ≠ j → g i = 1) → (List.ofFn g).prod = g j := by
  first
  | exact @_root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single
  | exact _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single
  | (apply _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single ..)

theorem clm_expand {k : ℕ} (L : (Fin k → ℝ) →L[ℝ] ℂ) (v : Fin k → ℝ) :
    L v = ∑ i, (v i : ℂ) * L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Pi.single i (v i) = v i • (Pi.single i 1 : Fin k → ℝ) by rw [← Pi.single_smul', smul_eq_mul, mul_one],
    map_smul, Complex.real_smul]

theorem hasDerivAt_dir {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {Φ : X → Y} {L : X →L[ℝ] Y} {t : X} (h : HasFDerivAt Φ L t) (v : X) :
    HasDerivAt (fun u : ℝ => Φ (t + u • v)) (L v) 0 := by
  have hl : HasDerivAt (fun u : ℝ => t + u • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add t
  exact HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h hl (by simp)

theorem contDiff_integral_of_closed {k : ℕ} {Λ ι : Type} [Fintype ι] (nxt : ι → Λ → Λ)
    (φ : Λ → (Fin k → ℝ) → ℝ → ℂ) (a : ι → (Fin k → ℝ) → ((Fin k → ℝ) →L[ℝ] ℂ)) (ha : ∀ j, ContDiff ℝ ∞ (a j))
    (hc : ∀ l x, Continuous (φ l x))
    (hb : ∀ l x₀, ∃ C, ∀ x ∈ Metric.closedBall x₀ 1, ∀ θ, ‖φ l x θ‖ ≤ C)
    (hd : ∀ l x θ, HasFDerivAt (fun x => φ l x θ) (∑ j, φ (nxt j l) x θ • a j x) x) (p q : ℝ) (l : Λ) :
    ContDiff ℝ ∞ fun x => ∫ θ in p..q, φ l x θ := by
  have key : ∀ l x₀, HasFDerivAt (fun x => ∫ θ in p..q, φ l x θ)
      (∑ j, (∫ θ in p..q, φ (nxt j l) x₀ θ) • a j x₀) x₀ := by
    intro l x₀
    choose C hC using fun j => hb (nxt j l) x₀
    choose A hA using fun j => (isCompact_closedBall x₀ 1).exists_bound_of_continuousOn (ha j).continuous.continuousOn
    have hc' : ∀ x, Continuous fun θ => ∑ j, φ (nxt j l) x θ • a j x := fun x =>
      continuous_finset_sum _ fun j _ => (hc _ x).smul continuous_const
    have h := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (a := p) (b := q)
      (F := φ l) (F' := fun x θ => ∑ j, φ (nxt j l) x θ • a j x) (x₀ := x₀) (bound := fun _ => ∑ j, C j * A j)
      (Metric.closedBall_mem_nhds x₀ one_pos) (Eventually.of_forall fun x => (hc l x).aestronglyMeasurable)
      ((hc l x₀).intervalIntegrable _ _) (hc' x₀).aestronglyMeasurable
      (ae_of_all _ fun θ _ x hx => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
        rw [norm_smul]
        exact mul_le_mul (hC j x hx θ) (hA j x hx) (norm_nonneg _) ((norm_nonneg _).trans (hC j x hx θ))))
      intervalIntegrable_const (ae_of_all _ fun θ _ x _ => hd l x θ)
    rw [intervalIntegral.integral_finset_sum (f := fun j θ => φ (nxt j l) x₀ θ • a j x₀) fun j _ => ((hc _ x₀).smul continuous_const).intervalIntegrable _ _] at h
    simpa only [intervalIntegral.integral_smul_const] using h
  have ind : ∀ m : ℕ, ∀ l, ContDiff ℝ m fun x => ∫ θ in p..q, φ l x θ := by
    intro m
    induction m with
    | zero => intro l; exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x => (key l x).continuousAt)
    | succ m ih =>
      intro l
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
      refine ⟨fun x => (key l x).differentiableAt, by simp, ?_⟩
      rw [show fderiv ℝ (fun x => ∫ θ in p..q, φ l x θ) = fun x₀ => ∑ j, (∫ θ in p..q, φ (nxt j l) x₀ θ) • a j x₀ from
        funext fun x => (key l x).fderiv]
      exact ContDiff.sum fun j _ => (ih _).smul ((ha j).of_le (by exact_mod_cast le_top))
  exact contDiff_infty.2 fun m => ind m l

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem coords_unitary {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : ∃ (d : ℕ)
    (Z : Fin d → Matrix (Fin m) (Fin m) ℂ) (s : Matrix (Fin m) (Fin m) ℂ → Fin d → ℝ)
    (c : Matrix (Fin m) (Fin m) ℂ →L[ℝ] (Fin d → ℝ)),
    (∀ i, (Z i)ᴴ * A + A * Z i = 0) ∧ s 1 = 0 ∧ HasFDerivAt s c 1 ∧
    ∀ᶠ X in 𝓝 (1 : Matrix (Fin m) (Fin m) ℂ), Xᴴ * A * X = A →
      X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  let S := {X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}
  have hc : IsClosed S :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have h1 : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ S := by simp [S]
  have hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := by
    intro a ha b hb
    simp only [S, Set.mem_setOf_eq] at ha hb ⊢
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * A * (a * b) = bᴴ * (aᴴ * A * a) * b := by simp only [Matrix.mul_assoc]
      _ = A := by rw [ha, hb]
  have hi : ∀ Z : Matrix (Fin m) (Fin m) ℂ, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S := by
    intro Z hZ
    simp only [S, Set.mem_setOf_eq] at hZ ⊢
    have hXY : NormedSpace.exp Z * NormedSpace.exp (-Z) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_right, add_neg_cancel,
        NormedSpace.exp_zero]
    calc (NormedSpace.exp (-Z))ᴴ * A * NormedSpace.exp (-Z)
        = (NormedSpace.exp (-Z))ᴴ * ((NormedSpace.exp Z)ᴴ * A * NormedSpace.exp Z) * NormedSpace.exp (-Z) := by
          rw [hZ]
      _ = (NormedSpace.exp Z * NormedSpace.exp (-Z))ᴴ * A * (NormedSpace.exp Z * NormedSpace.exp (-Z)) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = A := by rw [hXY]; simp
  have _ : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  obtain ⟨d, Z, s, c, hZ, hs, hd, hev⟩ := exists_coords_deriv hc h1 hm hi
  exact ⟨d, Z, s, c, fun i => GlobalTheory.ClosedMatGroup.skew_of_exp_smul_mem A (Z i) (hZ i), hs, hd, hev⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

open GlobalTheory.Orb (archMat)
open GlobalTheory.UAut (IsSm)

theorem realLine_zero (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : γ 0 = 1 := by
  have := (GlobalTheory.CircleDop.realLine_hom h hγ).1 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem exists_lines_curve (h : IsCMExt F E σ) (hJ : IsHermND σ J) (w : InfinitePlace F) (τ : EmbOver E w) :
    ∃ (d : ℕ) (η : Fin d → ℝ → GAd σ J) (c : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin d → ℝ)),
      (∀ i, IsRealLine σ J (η i)) ∧ ∀ f, IsSm σ J f → ∀ (g : GAd σ J) (y : ℝ → GArch σ J w)
        (M : Matrix (Fin n) (Fin n) ℂ), y 0 = 1 → HasDerivAt (fun u => archMat σ J τ (y u)) M 0 →
        HasDerivAt (fun u => f (g * embArch σ J w (y u))) (∑ i, (c M i : ℂ) * lineDer (η i) f g) 0 := by
  set A : Matrix (Fin n) (Fin n) ℂ := J.map τ.1 with hA
  obtain ⟨d, Z, s, c, hZ, hs, hsd, hev⟩ := coords_unitary A
  have hd : IsUnit A.det := by
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hx : ∀ (i : Fin d) (t : ℝ), ∃ y : GArch σ J w, archMat σ J τ y = NormedSpace.exp (t • Z i) := by
    intro i t
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp (t • Z i)
    have h1 := GlobalTheory.SmoothForms.exp_mem_UH (X := t • Z i) hd (by
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hZ i, smul_zero])
    refine ⟨(archEquiv J h τ).symm ⟨u, show _ * _ * _ = _ from hu ▸ h1⟩, ?_⟩
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]
    exact hu
  choose x hx using hx
  have hS : ∀ g : GArch σ J w, (archMat σ J τ g)ᴴ * A * archMat σ J τ g = A := fun g => (archEquiv J h τ g).2
  have hinj : Function.Injective (archMat σ J τ) := fun a b e =>
    (GlobalTheory.Orb.isEmbedding_archMat J h τ).injective (by
      show (fun i j => archMat σ J τ a i j) = fun i j => archMat σ J τ b i j
      rw [e])
  let η : Fin d → ℝ → GAd σ J := fun i t => embArch σ J w (x i t)
  have hη : ∀ i, IsRealLine σ J (η i) := fun i => ⟨w, τ, Z i, hZ i, fun t => ⟨x i t, rfl, hx i t⟩⟩
  refine ⟨d, η, c, hη, fun f hf g y M hy0 hy => ?_⟩
  have hy1 : archMat σ J τ (y 0) = 1 := by rw [hy0, map_one]
  let Φ : (Fin d → ℝ) → ℂ := fun t => f (g * (List.ofFn fun i => η i (t i)).prod)
  have hΦ : HasFDerivAt Φ (fderiv ℝ Φ 0) 0 := ((hf d η hη g).differentiable (by simp) 0).hasFDerivAt
  have h1 : HasDerivAt (fun u => s (archMat σ J τ (y u))) (c M) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hsd hy hy1.symm
  have h2 : HasDerivAt (fun u => Φ (s (archMat σ J τ (y u)))) (fderiv ℝ Φ 0 (c M)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hΦ h1 (by rw [hy1, hs])
  have h3 : ∀ i, fderiv ℝ Φ 0 (Pi.single i 1) = lineDer (η i) f g := fun i => by
    rw [← (hasDerivAt_dir hΦ (Pi.single i 1)).deriv]
    unfold lineDer
    congr 1
    funext u
    simp only [Φ]
    rw [prod_ofFn_single _ i fun j hj => by simp [Pi.single_eq_of_ne hj, realLine_zero h (hη j)]]
    simp
  rw [clm_expand] at h2
  simp only [h3] at h2
  refine h2.congr_of_eventuallyEq ?_
  have ht : Tendsto (fun u => archMat σ J τ (y u)) (𝓝 0) (𝓝 1) := hy1 ▸ hy.continuousAt.tendsto
  filter_upwards [ht.eventually hev] with u hu
  have e1 : (List.ofFn fun i => η i (s (archMat σ J τ (y u)) i)).prod =
      embArch σ J w (List.ofFn fun i => x i (s (archMat σ J τ (y u)) i)).prod := by
    rw [map_list_prod, List.map_ofFn]; rfl
  simp only [Φ]
  rw [e1]
  congr 3
  apply hinj
  rw [map_list_prod, List.map_ofFn]
  refine (hu (hS _)).trans ?_
  congr 1
  exact List.ofFn_inj.2 (funext fun i => (hx i _).symm)

theorem contDiff_archMat_line (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) {w : InfinitePlace F}
    (τ : EmbOver E w) : ContDiff ℝ ∞ fun t => archMat σ J τ (projArch σ J w (γ t)) := by
  obtain ⟨hadd, hc⟩ := GlobalTheory.CircleDop.realLine_hom h hγ
  obtain ⟨Z, hZ⟩ := GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter
    (fun t => archMat σ J τ (projArch σ J w (γ t)))
    ((GlobalTheory.Orb.continuous_archMat σ J τ).comp ((continuous_projArch σ J w).comp hc))
    (by simp only [realLine_zero h hγ, map_one]) (fun s t => by simp only [hadd, map_mul])
  simp only [hZ]
  have _ : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have he : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact he.comp (contDiff_id.smul contDiff_const)

theorem exists_lines_partial (h : IsCMExt F E σ) (hJ : IsHermND σ J) {k : ℕ} {γ : Fin k → ℝ → GAd σ J}
    (hγ : ∀ i, IsRealLine σ J (γ i)) (i : Fin k) :
    ∃ (d : ℕ) (η : Fin d → ℝ → GAd σ J) (b : Fin d → (Fin k → ℝ) → ℝ),
      (∀ a, IsRealLine σ J (η a)) ∧ (∀ a, ContDiff ℝ ∞ (b a)) ∧ ∀ f, IsSm σ J f → ∀ (g : GAd σ J) (t : Fin k → ℝ),
        HasDerivAt (fun u : ℝ => f (g * (List.ofFn fun j => γ j ((t + u • (Pi.single i 1 : Fin k → ℝ)) j)).prod))
          (∑ a, (b a t : ℂ) * lineDer (η a) f (g * (List.ofFn fun j => γ j (t j)).prod)) 0 := by
  obtain ⟨w, τ, Z, -, hw⟩ := hγ i
  obtain ⟨d, η, c, hη, hc⟩ := exists_lines_curve h hJ w τ
  let P : (Fin k → ℝ) → GAd σ J := fun t => (List.ofFn fun j => γ j (t j)).prod
  let φ : GAd σ J →* Matrix (Fin n) (Fin n) ℂ := (archMat σ J τ).comp (projArch σ J w)
  obtain ⟨hm, hm'⟩ := contDiff_ofFn_prod φ k (fun j (t : Fin k → ℝ) => γ j (t j)) fun j =>
    ⟨(contDiff_archMat_line h (hγ j) τ).comp (contDiff_apply ℝ ℝ j), by
      have e : ∀ u, (γ j u)⁻¹ = γ j (-u) := fun u => inv_eq_of_mul_eq_one_right (by
        rw [← (GlobalTheory.CircleDop.realLine_hom h (hγ j)).1, add_neg_cancel, realLine_zero h (hγ j)])
      simp only [e]
      exact (contDiff_archMat_line h (hγ j) τ).comp (contDiff_apply ℝ ℝ j).neg⟩
  let e : Fin k → ℝ := Pi.single i 1
  let M : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun t => φ (P t)⁻¹ * fderiv ℝ (fun t => φ (P t)) t e
  have hM : ContDiff ℝ ∞ M := hm'.mul ((hm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  refine ⟨d, η, fun a t => c (M t) a, hη, fun a => (contDiff_apply ℝ ℝ a).comp (c.contDiff.comp hM), fun f hf g t => ?_⟩
  have key := hc f hf (g * P t) (fun u => projArch σ J w ((P t)⁻¹ * P (t + u • e))) (M t) (by simp) (by
    have := (hasDerivAt_dir ((hm.differentiable (by simp)) t).hasFDerivAt e).const_mul (φ (P t)⁻¹)
    simp only [← map_mul] at this
    exact this)
  convert key using 3 with u
  have aux : ∀ {H : Type} [Group H] (ψ : GAd σ J →* H), (∀ y, ψ (embArch σ J w y) = 1) →
      ψ ((P t)⁻¹ * P (t + u • e)) = 1 := fun ψ hψ => by
    rw [map_mul, map_inv, inv_mul_eq_one]
    simp only [P, map_list_prod, List.map_ofFn]
    congr 2
    funext j
    by_cases hj : j = i
    · subst hj
      obtain ⟨y1, e1, -⟩ := hw (t j)
      obtain ⟨y2, e2, -⟩ := hw ((t + u • e) j)
      simp only [Function.comp_apply, e1, e2, hψ]
    · simp [e, Pi.single_eq_of_ne hj]
  have e2 : embArch σ J w (projArch σ J w ((P t)⁻¹ * P (t + u • e))) = (P t)⁻¹ * P (t + u • e) := by
    refine GAd_ext σ J (fun v => ?_) fun v => ?_
    · by_cases hv : v = w
      · subst hv; rw [projArch_embArch_self]
      · rw [projArch_embArch_ne σ J hv, aux _ (projArch_embArch_ne σ J hv)]
    · rw [aux (proj σ J v) (by simp)]; simp
  rw [e2, mul_assoc, mul_inv_cancel_left]

theorem exists_lines_fderiv (h : IsCMExt F E σ) (hJ : IsHermND σ J) {k : ℕ} {γ : Fin k → ℝ → GAd σ J}
    (hγ : ∀ i, IsRealLine σ J (γ i)) :
    ∃ (ι : Type) (_ : Fintype ι) (δ : ι → ℝ → GAd σ J) (a : ι → (Fin k → ℝ) → ((Fin k → ℝ) →L[ℝ] ℂ)),
      (∀ j, IsRealLine σ J (δ j)) ∧ (∀ j, ContDiff ℝ ∞ (a j)) ∧ ∀ f, IsSm σ J f → ∀ (g : GAd σ J) (t : Fin k → ℝ),
        HasFDerivAt (fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod))
          (∑ j, lineDer (δ j) f (g * (List.ofFn fun i => γ i (t i)).prod) • a j t) t := by
  choose d η b hη hb hd using exists_lines_partial h hJ hγ
  refine ⟨Σ i, Fin (d i), inferInstance, fun j => η j.1 j.2,
    fun j t => b j.1 j.2 t • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj j.1)), fun j => hη _ _,
    fun j => (hb _ _).smul contDiff_const, fun f hf g t => ?_⟩
  have hD := ((hf k γ hγ g).differentiable (by simp) t).hasFDerivAt
  refine hD.congr_fderiv (Eq.symm (ContinuousLinearMap.ext fun v => ?_))
  rw [clm_expand (fderiv ℝ _ t), ContinuousLinearMap.sum_apply, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hasDerivAt_dir hD (Pi.single i 1)).unique (hd i f hf g t), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp
  ring

theorem isSm_circleIntegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (H₀ : ℂ → GAd σ J → ℂ) (s₀ : ℂ) (r : ℝ) (V : Set ℂ),
    IsOpen V → 0 < r → Metric.closedBall s₀ r ⊆ V → (∀ s ∈ V, IsSmoothModerate σ J (H₀ s)) →
    (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) V) → ∀ j : ℤ,
    GlobalTheory.UAut.IsSm σ J fun g => circleIntegral (fun z => (z - s₀) ^ j * H₀ z g) s₀ r := by
  intro F E _ _ _ _ _ σ h n J hJ H₀ s₀ r V hV hr hsub hH hμ j k γ hγ g
  obtain ⟨ι, _, δ, a, hδ, ha, hd⟩ := exists_lines_fderiv h hJ hγ
  have hS : Metric.sphere s₀ r ⊆ V := Metric.sphere_subset_closedBall.trans hsub
  have hmem : ∀ θ, circleMap s₀ r θ ∈ Metric.sphere s₀ r := fun θ => circleMap_mem_sphere s₀ hr.le θ
  let P : (Fin k → ℝ) → GAd σ J := fun t => (List.ofFn fun i => γ i (t i)).prod
  have hP : Continuous P := by
    simp only [P, List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ => (GlobalTheory.CircleDop.realLine_hom h (hγ i)).2.comp (continuous_apply i)
  let c : ℝ → ℂ := fun θ => deriv (circleMap s₀ r) θ * (circleMap s₀ r θ - s₀) ^ j
  have hc : Continuous c := by
    have h1 : Continuous fun θ => deriv (circleMap s₀ r) θ := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 r).mul continuous_const
    exact h1.mul (((continuous_circleMap s₀ r).sub continuous_const).zpow₀ j fun θ =>
      Or.inl (sub_ne_zero.2 (Metric.ne_of_mem_sphere (hmem θ) hr.ne')))
  have hcb : ∀ θ, ‖c θ‖ = |r| * |r| ^ j := fun θ => by
    simp only [c, deriv_circleMap, norm_mul, norm_zpow, circleMap_sub_center, norm_circleMap_zero, Complex.norm_I,
      mul_one]
  have W := fun l : {l : List (ℝ → GAd σ J) // ∀ γ ∈ l, IsRealLine σ J γ} =>
    GlobalTheory.WeakHolFamily.word_holomorphic_and_uniform F E σ n J H₀ V (Metric.sphere s₀ r) hV
      (isCompact_sphere s₀ r) hS hH hμ l.1 l.2
  have key := contDiff_integral_of_closed (Λ := {l : List (ℝ → GAd σ J) // ∀ γ ∈ l, IsRealLine σ J γ})
    (fun i l => ⟨δ i :: l.1, List.forall_mem_cons.2 ⟨hδ i, l.2⟩⟩)
    (fun l t θ => c θ * l.1.foldr lineDer (H₀ (circleMap s₀ r θ)) (g * P t)) a ha
    (fun l t => hc.mul ((((W l).1 (g * P t)).continuousOn.mono hS).comp_continuous (continuous_circleMap s₀ r) hmem))
    (fun l t₀ => by
      obtain ⟨N, C, hC⟩ := (W l).2
      have hh : Continuous fun t => C * (height σ J (g * P t) : ℝ) ^ N :=
        continuous_const.mul ((NNReal.continuous_coe.comp ((continuous_height_GAd σ J).comp
          (continuous_const.mul hP))).pow N)
      obtain ⟨B, hB⟩ := (isCompact_closedBall t₀ 1).exists_bound_of_continuousOn hh.continuousOn
      refine ⟨|r| * |r| ^ j * B, fun t ht θ => ?_⟩
      rw [norm_mul, hcb]
      exact mul_le_mul_of_nonneg_left ((hC _ (hmem θ) _).trans ((le_abs_self _).trans (hB t ht))) (by positivity))
    (fun l t θ => by
      have h1 := (hd _ (GlobalTheory.WeakHolFamily.smoothLines_foldr (hH _ (hS (hmem θ))).smooth l.1 l.2) g t).const_mul (c θ)
      rw [Finset.smul_sum] at h1
      simp only [smul_smul] at h1
      exact h1)
    0 (2 * Real.pi) ⟨[], by simp⟩
  simp only [c, mul_assoc] at key
  exact key

end GlobalTheory.CircleSmooth
end
end

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderate_eisenstein_holomorphic_ball : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (H₀ : ℂ → GAd σ J → ℂ) (s₀ : ℂ) (r : ℝ) (V : Set ℂ),
    IsOpen V → 0 < r → Metric.closedBall s₀ r ⊆ V → (∀ s ∈ V, IsSmoothModerate σ J (H₀ s)) →
    (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) V) → ∀ j : ℤ,
    GlobalTheory.UAut.IsSm σ J fun g => circleIntegral (fun z => (z - s₀) ^ j * H₀ z g) s₀ r := by
  atlas_forward_decl GlobalTheory.CircleSmooth.isSm_circleIntegral
end

section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderate_eisenstein_holomorphic_derivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (H₀ : ℂ → GAd σ J → ℂ) (s₀ : ℂ) (r : ℝ) (V : Set ℂ),
    IsOpen V → 0 < r → Metric.closedBall s₀ r ⊆ V → (∀ s ∈ V, IsSmoothModerate σ J (H₀ s)) →
    (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) V) → ∀ j : ℤ,
    ∀ z : List (ℝ → GAd σ J) →₀ ℂ, (∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) → ∀ g,
      GlobalTheory.UAut.dop z (fun g => circleIntegral (fun w => (w - s₀) ^ j * H₀ w g) s₀ r) g =
        circleIntegral (fun w => (w - s₀) ^ j * GlobalTheory.UAut.dop z (H₀ w) g) s₀ r := by
  first | exact @GlobalTheory.CircleDop.dop_circleIntegral | exact GlobalTheory.CircleDop.dop_circleIntegral | (intros; apply GlobalTheory.CircleDop.dop_circleIntegral <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_residue_holomorphic_region : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c →
    ∀ (k₀ : ℕ) (U₀ : Set ℂ) (H₀ : ℂ → GAd σ J → ℂ), U₀ ∈ 𝓝 (((n : ℂ) - 1) / 2) →
      (∀ s ∈ U₀, s ≠ (((n : ℂ) - 1) / 2) → ∀ g, H₀ s g = (s - (((n : ℂ) - 1) / 2)) ^ k₀ * Eis s g) →
      (∀ s ∈ U₀, IsSmoothModerate σ J (H₀ s)) →
      (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) U₀) →
      ∃ V ∈ 𝓝 (((n : ℂ) - 1) / 2), ∀ s ∈ V, ∀ k ∈ levelAll σ J L a, ∀ g, H₀ s (g * k) = H₀ s g := by
  first | exact @GlobalTheory.EisRes.levelAll_inv_near_rho | exact GlobalTheory.EisRes.levelAll_inv_near_rho | (intros; apply GlobalTheory.EisRes.levelAll_inv_near_rho <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_setting_height_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h → Continuous h := by
  first | exact @GlobalTheory.EisRes.HtCont.continuous_iwaHt | exact GlobalTheory.EisRes.HtCont.continuous_iwaHt | (intros; apply GlobalTheory.EisRes.HtCont.continuous_iwaHt <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisRes

open scoped Pointwise

theorem iwaHt_mul_le_of_isCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∀ C : Set (GAd σ J), IsCompact C → ∃ K : ℝ, 0 ≤ K ∧ ∀ γ g, g ∈ C → h (γ * g) ≤ K * h γ := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS C hC
  have hcont : Continuous h := GlobalTheory.T.eisenstein_setting_height_continuous F E σ n J r X Y L a h hS
  obtain ⟨hCM, -, -, -, -, hAd, hI⟩ := hS
  haveI := hAd.lat
  have hK : IsCompact ((levelAll σ J L a : Set (GAd σ J)) * C) :=
    (GlobalTheory.Doubling.isCompact_levelAll hCM J L a).mul hC
  obtain ⟨K0, hK0⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max K0 0, le_max_right _ _, fun γ g hg => ?_⟩
  obtain ⟨p, l, hp, k, hk, rfl⟩ := hI.1 γ
  obtain ⟨p', l', hp', k', hk', hkg⟩ := hI.1 (k * g)
  have e1 : p * k * g = (p * p') * k' := by rw [mul_assoc, hkg, mul_assoc]
  have hpp : (matHom _ σ J (p * p')).1 * adMat F (col0 X) = (l * l').1 • adMat F (col0 X) := by
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hp', Matrix.mul_smul, hp, smul_smul, Units.val_mul, mul_comm (l' : AF F ⊗[F] E)]
  have h1 : h (p * k * g) = absE F E (l * l') := by rw [e1]; exact hI.2 _ _ hpp _ hk'
  have h2 : h (p * k) = absE F E l := hI.2 _ _ hp _ hk
  have h3 : h (k * g) = absE F E l' := by rw [hkg]; exact hI.2 _ _ hp' _ hk'
  have hb : h (k * g) ≤ max K0 0 :=
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hK0 _ (Set.mul_mem_mul hk hg))).trans (le_max_left _ _)
  rw [h1, h2, map_mul, NNReal.coe_mul, mul_comm (absE F E l : ℝ)]
  exact mul_le_mul_of_nonneg_right (h3 ▸ hb) (NNReal.coe_nonneg _)

end GlobalTheory.EisRes
end

section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EisRes.CentralEig

open GlobalTheory.UAut GlobalTheory.WeakHolFamily
open scoped ContDiff

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

section General

theorem line_zero (hCM : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : γ 0 = 1 := by
  have := isRealLine_add F E σ hCM n J γ hγ 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem isSm_lineDer {φ : GAd σ J → ℂ} (hφ : IsSm σ J φ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    IsSm σ J (lineDer γ φ) := smoothLines_lineDer hφ hγ

theorem isSm_foldr {φ : GAd σ J → ℂ} (hφ : IsSm σ J φ) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → IsSm σ J (l.foldr lineDer φ)
  | [], _ => hφ
  | γ :: l, hl => isSm_lineDer (isSm_foldr hφ l fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)) (hl γ List.mem_cons_self)

theorem diff_line {φ : GAd σ J → ℂ} (hφ : IsSm σ J φ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (g : GAd σ J) :
    Differentiable ℝ fun t => φ (g * γ t) := by
  have h1 := hφ 1 (fun _ => γ) (fun _ => hγ) g
  have h2 : ContDiff ℝ ∞ fun t : ℝ => (fun _ : Fin 1 => t) := contDiff_pi.2 fun _ => contDiff_id
  have h3 := (h1.comp h2).differentiable (by simp)
  simpa [Function.comp_def] using h3

theorem hasDerivAt_line (hCM : IsCMExt F E σ) {φ : GAd σ J → ℂ} (hφ : IsSm σ J φ) {γ : ℝ → GAd σ J}
    (hγ : IsRealLine σ J γ) (g : GAd σ J) (u : ℝ) :
    HasDerivAt (fun t => φ (g * γ t)) (lineDer γ φ (g * γ u)) u := by
  have e : lineDer γ φ (g * γ u) = deriv (fun t => φ (g * γ t)) u := by
    have := deriv_comp_const_add (fun t => φ (g * γ t)) u 0
    rw [add_zero] at this
    rw [← this]
    simp only [lineDer, isRealLine_add F E σ hCM n J γ hγ, mul_assoc]
  rw [e]
  exact (diff_line hφ hγ g u).hasDerivAt

omit [NumberField E] in

theorem foldr_left {φ : GAd σ J → ℂ} {p : GAd σ J} {c : ℂ} (hφ : ∀ g, φ (p * g) = c * φ g) :
    ∀ (l : List (ℝ → GAd σ J)) (g : GAd σ J), l.foldr lineDer φ (p * g) = c * l.foldr lineDer φ g
  | [], g => hφ g
  | γ :: l, g => by
    simp only [List.foldr_cons, lineDer, mul_assoc, foldr_left hφ l, deriv_const_mul_field']

theorem hasSum_foldr (hCM : IsCMExt F E σ) {ι : Type} (t : ι → GAd σ J) {f Φ : GAd σ J → ℂ} {w : GAd σ J → ℝ}
    (hf : IsSm σ J f)
    (hb : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖l.foldr lineDer f g‖ ≤ C * w g)
    (hw : ∀ C : Set (GAd σ J), IsCompact C → ∃ K : ℝ, ∀ γ g, g ∈ C → w (γ * g) ≤ K * w γ)
    (hs : ∀ g, Summable fun i => w (t i * g)) (hΦ : ∀ g, HasSum (fun i => f (t i * g)) (Φ g)) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∀ g,
      HasSum (fun i => l.foldr lineDer f (t i * g)) (l.foldr lineDer Φ g)
  | [], _, g => hΦ g
  | γ :: l, hl, g => by
    have hl' : ∀ δ ∈ l, IsRealLine σ J δ := fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
    have hγ := hl γ List.mem_cons_self
    have ih := hasSum_foldr hCM t hf hb hw hs hΦ l hl'
    obtain ⟨C, hC0, hC⟩ := hb _ hl
    obtain ⟨K, hK⟩ := hw _ ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).image
      (GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ hCM n J γ hγ))
    have hu : Summable fun i => C * (K * w (t i * g)) := ((hs g).mul_left K).mul_left C
    have hbd : ∀ i, ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
        ‖lineDer γ (l.foldr lineDer f) (t i * g * γ u)‖ ≤ C * (K * w (t i * g)) := fun i u hu' =>
      (hC _).trans (mul_le_mul_of_nonneg_left (hK _ _ ⟨u, Set.Ioo_subset_Icc_self hu', rfl⟩) hC0)
    have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have key := hasDerivAt_tsum_of_isPreconnected (g := fun i u => l.foldr lineDer f (t i * g * γ u))
      (g' := fun i u => lineDer γ (l.foldr lineDer f) (t i * g * γ u)) hu isOpen_Ioo isPreconnected_Ioo
      (fun i u _ => hasDerivAt_line hCM (isSm_foldr hf l hl') hγ _ u) hbd h0
      (by simpa only [mul_assoc] using (ih (g * γ 0)).summable) h0
    have e : (fun u => ∑' i, l.foldr lineDer f (t i * g * γ u)) = fun u => l.foldr lineDer Φ (g * γ u) :=
      funext fun u => by simpa only [mul_assoc] using (ih (g * γ u)).tsum_eq
    rw [e] at key
    have hsum : Summable fun i => lineDer γ (l.foldr lineDer f) (t i * g * γ 0) :=
      .of_norm_bounded hu fun i => hbd i 0 h0
    have := hsum.hasSum
    rw [← key.deriv, line_zero hCM hγ] at this
    simp only [mul_one] at this
    exact this

theorem differentiable_foldr_exp (hCM : IsCMExt F E σ) {lam : GAd σ J → ℂ} (hlam : IsSm σ J lam)
    (l : List (ℝ → GAd σ J)) (hl : ∀ γ ∈ l, IsRealLine σ J γ) (g : GAd σ J) :
    Differentiable ℂ fun s : ℂ => l.foldr lineDer (fun y => Complex.exp (lam y * s)) g := by
  let S : AddSubmonoid (ℂ → GAd σ J → ℂ) := AddSubmonoid.closure
    {Φ | ∃ (e : ℂ → ℂ) (a : GAd σ J → ℂ), Differentiable ℂ e ∧ IsSm σ J a ∧
      Φ = fun s y => e s * (a y * Complex.exp (lam y * s))}
  have h1 : ∀ Φ ∈ S, (∀ s, IsSm σ J (Φ s)) ∧ ∀ y, Differentiable ℂ fun s => Φ s y := by
    intro Φ hΦ
    induction hΦ using AddSubmonoid.closure_induction with
    | mem Φ hΦ =>
      obtain ⟨e, a, he, ha, rfl⟩ := hΦ
      refine ⟨fun s k γ hγ y => contDiff_const.mul ((ha k γ hγ y).mul ((hlam k γ hγ y).mul contDiff_const).cexp),
        fun y => ?_⟩
      fun_prop
    | zero => exact ⟨fun s k γ hγ y => contDiff_const, fun y => differentiable_const _⟩
    | add Φ Ψ _ _ hΦ hΨ =>
      exact ⟨fun s k γ hγ y => (hΦ.1 s k γ hγ y).add (hΨ.1 s k γ hγ y), fun y => (hΦ.2 y).add (hΨ.2 y)⟩
  have h2 : ∀ γ, IsRealLine σ J γ → ∀ Φ ∈ S, (fun s => lineDer γ (Φ s)) ∈ S := by
    intro γ hγ Φ hΦ
    induction hΦ using AddSubmonoid.closure_induction with
    | mem Φ hΦ =>
      obtain ⟨e, a, he, ha, rfl⟩ := hΦ
      have e1 : (fun s => lineDer γ fun y => e s * (a y * Complex.exp (lam y * s))) =
          (fun s y => e s * (lineDer γ a y * Complex.exp (lam y * s))) +
            fun s y => (e s * s) * ((a y * lineDer γ lam y) * Complex.exp (lam y * s)) := by
        funext s y
        have d1 := hasDerivAt_line hCM ha hγ y 0
        have d2 := hasDerivAt_line hCM hlam hγ y 0
        have d3 := (d1.mul (d2.mul_const s).cexp).const_mul (e s)
        have d4 := d3.deriv
        simp only [line_zero hCM hγ, mul_one] at d4
        refine Eq.trans d4 ?_
        simp only [Pi.add_apply]
        ring
      rw [e1]
      exact add_mem (AddSubmonoid.subset_closure ⟨e, _, he, isSm_lineDer ha hγ, rfl⟩)
        (AddSubmonoid.subset_closure ⟨fun s => e s * s, fun y => a y * lineDer γ lam y, he.mul differentiable_id,
          fun k δ hδ y => (ha k δ hδ y).mul (isSm_lineDer hlam hγ k δ hδ y), rfl⟩)
    | zero =>
      have e1 : (fun s => lineDer γ ((0 : ℂ → GAd σ J → ℂ) s)) = 0 := by
        funext s y; simp [lineDer]
      rw [e1]; exact zero_mem _
    | add Φ Ψ hΦ' hΨ' hΦ hΨ =>
      have e1 : (fun s => lineDer γ ((Φ + Ψ) s)) = (fun s => lineDer γ (Φ s)) + fun s => lineDer γ (Ψ s) := by
        funext s y
        exact deriv_add (diff_line ((h1 Φ hΦ').1 s) hγ y 0) (diff_line ((h1 Ψ hΨ').1 s) hγ y 0)
      rw [e1]; exact add_mem hΦ hΨ
  have h3 : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      (fun s : ℂ => l.foldr lineDer (fun y => Complex.exp (lam y * s))) ∈ S := by
    intro l hl
    induction l with
    | nil =>
      exact AddSubmonoid.subset_closure ⟨fun _ => 1, fun _ => 1, differentiable_const _,
        fun k γ hγ y => contDiff_const, by funext s y; simp⟩
    | cons γ l ih =>
      exact h2 γ (hl γ List.mem_cons_self) _ (ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ))
  exact (h1 _ (h3 l hl)).2 g

end General

section Height

variable {x : Matrix (Fin n) (Fin 1) E} {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}
  {h : GAd σ J → ℝ}

variable (σ J x) in

def adLineStab : Subgroup (GAd σ J) where
  carrier := {p | ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro p q ⟨l, hp⟩ ⟨l', hq⟩
    exact ⟨l * l', by rw [map_mul, Units.val_mul, Matrix.mul_assoc, hq, Matrix.mul_smul, hp, smul_smul, Units.val_mul,
      mul_comm (l' : AF F ⊗[F] E)]⟩
  inv_mem' := by rintro p ⟨l, hl⟩; exact ⟨l⁻¹, HtCont.inv_eigen hl⟩

variable (hI : IsIwaHtG σ J x L a h)
include hI

theorem ht_level {k : GAd σ J} (hk : k ∈ levelAll σ J L a) : h k = 1 := by
  simpa using hI.2 1 1 (by simp) k hk

theorem ht_pos (g : GAd σ J) : 0 < h g := by
  obtain ⟨p, l, hp, k, hk, rfl⟩ := hI.1 g
  rw [hI.2 p l hp k hk]
  exact_mod_cast GlobalTheory.Doubling.hom_pos _ l

theorem ht_left {p : GAd σ J} (hp : p ∈ adLineStab σ J x) (g : GAd σ J) : h (p * g) = h p * h g := by
  obtain ⟨l, hl⟩ := hp
  obtain ⟨q, l', hq, k, hk, rfl⟩ := hI.1 g
  have e := hI.2 p l hl 1 (one_mem _)
  rw [mul_one] at e
  have hpq : (matHom _ σ J (p * q)).1 * adMat F x = (l * l').1 • adMat F x := by
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hq, Matrix.mul_smul, hl, smul_smul, Units.val_mul,
      mul_comm (l' : AF F ⊗[F] E)]
  rw [← mul_assoc, hI.2 (p * q) (l * l') hpq k hk, e, hI.2 q l' hq k hk, map_mul, NNReal.coe_mul]

theorem ht_right (g : GAd σ J) {k : GAd σ J} (hk : k ∈ levelAll σ J L a) : h (g * k) = h g := by
  obtain ⟨p, l, hpl, k', hk', rfl⟩ := hI.1 g
  rw [mul_assoc, hI.2 p l hpl _ (Subgroup.mul_mem _ hk' hk), hI.2 p l hpl k' hk']

theorem exists_iwa (g : GAd σ J) : ∃ p : adLineStab σ J x, ∃ k ∈ levelAll σ J L a, g = p * k :=
  let ⟨p, l, hp, k, hk, e⟩ := hI.1 g
  ⟨⟨p, l, hp⟩, k, hk, e⟩

theorem pow_left {p : GAd σ J} (hp : p ∈ adLineStab σ J x) (t : ℂ) (g : GAd σ J) :
    (h (p * g) : ℂ) ^ t = (h p : ℂ) ^ t * (h g : ℂ) ^ t := by
  rw [ht_left hI hp, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (ht_pos hI p).le (ht_pos hI g).le]

def htHom : adLineStab σ J x →* ℝ≥0 where
  toFun p := ⟨h p, (ht_pos hI p).le⟩
  map_one' := Subtype.ext (ht_level hI (one_mem _))
  map_mul' p q := Subtype.ext (ht_left hI p.2 q)

theorem isSm_pow (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hc : Continuous h) (t : ℂ) :
    IsSm σ J (fun g => (h g : ℂ) ^ t) ∧ ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      Continuous (l.foldr lineDer fun g => (h g : ℂ) ^ t) := by
  refine GlobalTheory.EisCont.Smooth.isSm_of_mem hCM hJ (δ := htHom hI) (χ := 1) (t := t) (exists_iwa hI)
    ⟨fun p g => ?_, ?_, .of_invariant fun g k hk => by simp only [ht_right hI g hk]⟩
  · exact (pow_left hI p.2 t g).trans (congrArg (· * (h g : ℂ) ^ t) (one_mul ((h p : ℂ) ^ t)).symm)
  · exact (Complex.continuous_ofReal.comp hc).cpow continuous_const fun g => Or.inl (by simpa using ht_pos hI g)

theorem norm_foldr_le (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hc : Continuous h)
    (hK : IsCompact (levelAll σ J L a : Set (GAd σ J))) (t : ℂ) (l : List (ℝ → GAd σ J))
    (hl : ∀ γ ∈ l, IsRealLine σ J γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖l.foldr lineDer (fun g => (h g : ℂ) ^ t) g‖ ≤ C * ‖(h g : ℂ) ^ t‖ := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn ((isSm_pow hI hCM hJ hc t).2 l hl).continuousOn
  refine ⟨B, (norm_nonneg _).trans (hB 1 (one_mem _)), fun g => ?_⟩
  obtain ⟨p, k, hk, rfl⟩ := exists_iwa hI g
  rw [foldr_left (φ := fun g => (h g : ℂ) ^ t) (pow_left hI p.2 t), norm_mul, ht_right hI _ hk, mul_comm]
  exact mul_le_mul_of_nonneg_right (hB k hk) (norm_nonneg _)

theorem dop_pow (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hc : Continuous h) {z : List (ℝ → GAd σ J) →₀ ℂ}
    (hz : IsCentral σ J z) : ∃ χ : ℂ → ℂ, Differentiable ℂ χ ∧
      ∀ t g, dop z (fun g => (h g : ℂ) ^ t) g = χ t * (h g : ℂ) ^ t := by
  refine ⟨fun t => dop z (fun g => (h g : ℂ) ^ t) 1, ?_, fun t g => ?_⟩
  · have hlam : IsSm σ J fun g => ((Real.log (h g) : ℝ) : ℂ) := fun k γ hγ g => by
      have h1 := Complex.reCLM.contDiff.comp ((isSm_pow hI hCM hJ hc 1).1 k γ hγ g)
      have h2 : ContDiff ℝ ∞ fun t : Fin k → ℝ => h (g * (List.ofFn fun i => γ i (t i)).prod) := by
        simpa [Function.comp_def] using h1
      exact Complex.ofRealCLM.contDiff.comp (h2.log fun t => (ht_pos hI _).ne')
    have e : ∀ t : ℂ, (fun g => (h g : ℂ) ^ t) = fun g => Complex.exp (((Real.log (h g) : ℝ) : ℂ) * t) := fun t =>
      funext fun g => by
        rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ht_pos hI g).ne'), Complex.ofReal_log (ht_pos hI g).le]
    simp only [e, dop, Finsupp.sum]
    exact Differentiable.fun_sum fun l hl => (differentiable_foldr_exp hCM hlam l (hz.1 l hl) 1).const_mul _
  · obtain ⟨p, k, hk, rfl⟩ := exists_iwa hI g
    have e1 : dop z (fun g => (h g : ℂ) ^ t) (p * k) = (h p : ℂ) ^ t * dop z (fun g => (h g : ℂ) ^ t) k := by
      simp only [dop, Finsupp.sum, foldr_left (φ := fun g => (h g : ℂ) ^ t) (pow_left hI p.2 t), Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have e2 := GlobalTheory.EisCont.CentreFinite.dop_mul_right hCM hz (isSm_pow hI hCM hJ hc t).1 k 1
    simp only [one_mul, ht_right hI _ hk] at e2
    rw [e1, e2, ht_right hI _ hk, mul_comm]

end Height

theorem dop_eigen_near_rho : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c →
    ∀ (k₀ : ℕ) (U₀ : Set ℂ) (H₀ : ℂ → GAd σ J → ℂ), U₀ ∈ 𝓝 (((n : ℂ) - 1) / 2) →
      (∀ s ∈ U₀, s ≠ (((n : ℂ) - 1) / 2) → ∀ g, H₀ s g = (s - (((n : ℂ) - 1) / 2)) ^ k₀ * Eis s g) →
      (∀ s ∈ U₀, IsSmoothModerate σ J (H₀ s)) →
      (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) U₀) →
      ∃ V ∈ 𝓝 (((n : ℂ) - 1) / 2), ∀ z, GlobalTheory.UAut.IsCentral σ J z → ∃ χ : ℂ → ℂ, DifferentiableOn ℂ χ (interior V) ∧
        ∀ s ∈ V, GlobalTheory.UAut.dop z (H₀ s) = χ s • H₀ s := by
  intro F E _ _ _ _ _ σ n J r X Y L a h Eis c hS hP k₀ U₀ H₀ hU₀ hH hsm hhol
  set ρ : ℂ := ((n : ℂ) - 1) / 2 with hρ
  have hρre : ρ.re = ((n : ℝ) - 1) / 2 := by simp [hρ]
  have hc : Continuous h := HtCont.continuous_iwaHt F E σ n J r X Y L a h hS
  have hcmp := iwaHt_mul_le_of_isCompact F E σ n J r X Y L a h hS
  obtain ⟨hCM, -, hJ, hn, -, hA, hI⟩ := hS
  haveI := hA.lat
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := GlobalTheory.Doubling.isCompact_levelAll hCM J L a
  obtain ⟨T, hT⟩ := exists_reps σ J (col0 X)
  have heig : ∀ z, GlobalTheory.UAut.IsCentral σ J z → ∃ χ : ℂ → ℂ, Differentiable ℂ χ ∧
      ∀ s : ℂ, ρ.re < s.re → GlobalTheory.UAut.dop z (Eis s) = χ s • Eis s := by
    intro z hz
    obtain ⟨χ, hχd, hχ⟩ := dop_pow hI hCM hJ hc hz
    refine ⟨fun s => χ (s + ρ), hχd.comp (differentiable_id.add_const ρ), fun s hs => funext fun g => ?_⟩
    have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hre : 0 ≤ (s + ρ).re := by rw [Complex.add_re]; rw [hρre] at hs ⊢; linarith
    rw [hρre] at hs
    have hcmp' : ∀ C : Set (GAd σ J), IsCompact C → ∃ K : ℝ, ∀ γ g, g ∈ C →
        ‖(h (γ * g) : ℂ) ^ (s + ρ)‖ ≤ K * ‖(h γ : ℂ) ^ (s + ρ)‖ := fun C hC => by
      obtain ⟨K, hK0, hK⟩ := hcmp C hC
      refine ⟨K ^ (s + ρ).re, fun γ g hg => ?_⟩
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (ht_pos hI _), Complex.norm_cpow_eq_rpow_re_of_pos (ht_pos hI _),
        ← Real.mul_rpow hK0 (ht_pos hI _).le]
      exact Real.rpow_le_rpow (ht_pos hI _).le (hK γ g hg) hre
    have hw : ∀ l ∈ z.support, HasSum
        (fun t : T => z l * l.foldr lineDer (fun y => (h y : ℂ) ^ (s + ρ)) (t.1.1 * g))
        (z l * l.foldr lineDer (Eis s) g) := fun l hl =>
      (hasSum_foldr hCM (fun t : T => t.1.1) (w := fun y => ‖(h y : ℂ) ^ (s + ρ)‖) (isSm_pow hI hCM hJ hc _).1
        (norm_foldr_le hI hCM hJ hc hK _) hcmp' (fun g => summable_norm_iff.2 (hP.1 T hT s hs g).summable)
        (hP.1 T hT s hs) l (hz.1 l hl) g).mul_left (z l)
    have h1 := hasSum_sum hw
    have h2 : HasSum (fun t : T => χ (s + ρ) * (h (t.1.1 * g) : ℂ) ^ (s + ρ)) (χ (s + ρ) * Eis s g) :=
      (hP.1 T hT s hs g).mul_left _
    have e : (fun t : T => ∑ l ∈ z.support, z l * l.foldr lineDer (fun y => (h y : ℂ) ^ (s + ρ)) (t.1.1 * g)) =
        fun t : T => χ (s + ρ) * (h (t.1.1 * g) : ℂ) ^ (s + ρ) := funext fun t => hχ (s + ρ) (t.1.1 * g)
    rw [e] at h1
    exact h1.unique h2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU₀
  refine ⟨Metric.ball ρ ε, Metric.ball_mem_nhds ρ hε, fun z hz => ?_⟩
  obtain ⟨χ, hχd, hχ⟩ := heig z hz
  refine ⟨χ, hχd.differentiableOn, fun s hs => funext fun g => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul]
  have hwd : ∀ l ∈ z.support, DifferentiableOn ℂ (fun s => z l * l.foldr lineDer (H₀ s) g) (Metric.ball ρ ε) :=
    fun l hl => ((GlobalTheory.WeakHolFamily.word_holomorphic_and_uniform F E σ n J H₀ (Metric.ball ρ ε) ∅
      Metric.isOpen_ball isCompact_empty (Set.empty_subset _) (fun s hs => hsm s (hball hs))
      (fun μ hμ => (hhol μ hμ).mono hball) l (hz.1 l hl)).1 g).const_mul _
  have hA : DifferentiableOn ℂ (fun s => GlobalTheory.UAut.dop z (H₀ s) g) (Metric.ball ρ ε) :=
    DifferentiableOn.fun_sum hwd
  have hd : DifferentiableOn ℂ (fun s => H₀ s g) (Metric.ball ρ ε) :=
    (hhol _ (GlobalTheory.EisLine.isModerateForm_proj σ J g)).mono hball
  have hB : DifferentiableOn ℂ (fun s => χ s * H₀ s g) (Metric.ball ρ ε) := hχd.differentiableOn.mul hd
  have a1 := hA.analyticOnNhd Metric.isOpen_ball
  have a2 := hB.analyticOnNhd Metric.isOpen_ball
  set z₀ : ℂ := ρ + ((ε / 2 : ℝ) : ℂ) with hz₀
  have hz₀b : z₀ ∈ Metric.ball ρ ε := by
    rw [Metric.mem_ball, hz₀, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    linarith
  have hz₀re : ρ.re < z₀.re := by simp [hz₀, hε]
  have hopen : IsOpen (Metric.ball ρ ε ∩ {s : ℂ | ρ.re < s.re}) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hev : (fun s => GlobalTheory.UAut.dop z (H₀ s) g) =ᶠ[𝓝 z₀] fun s => χ s * H₀ s g := by
    filter_upwards [hopen.mem_nhds ⟨hz₀b, hz₀re⟩] with s hs'
    have hsU : s ∈ U₀ := hball hs'.1
    have hne : s ≠ ρ := by rintro rfl; exact lt_irrefl ρ.re hs'.2
    have eH : H₀ s = (s - ρ) ^ k₀ • Eis s := funext fun g' => by rw [hH s hsU hne g', Pi.smul_apply, smul_eq_mul]
    rw [eH, GlobalTheory.UAut.dop_smul, hχ s hs'.2]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  exact a1.eqOn_of_preconnected_of_eventuallyEq a2 (convex_ball ρ ε).isPreconnected hz₀b hev hs

end GlobalTheory.EisRes.CentralEig

end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_dop_central_eq_holomorphic_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c →
    ∀ (k₀ : ℕ) (U₀ : Set ℂ) (H₀ : ℂ → GAd σ J → ℂ), U₀ ∈ 𝓝 (((n : ℂ) - 1) / 2) →
      (∀ s ∈ U₀, s ≠ (((n : ℂ) - 1) / 2) → ∀ g, H₀ s g = (s - (((n : ℂ) - 1) / 2)) ^ k₀ * Eis s g) →
      (∀ s ∈ U₀, IsSmoothModerate σ J (H₀ s)) →
      (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) U₀) →
      ∃ V ∈ 𝓝 (((n : ℂ) - 1) / 2), ∀ z, GlobalTheory.UAut.IsCentral σ J z → ∃ χ : ℂ → ℂ, DifferentiableOn ℂ χ (interior V) ∧
        ∀ s ∈ V, GlobalTheory.UAut.dop z (H₀ s) = χ s • H₀ s := by
  first | exact @GlobalTheory.EisRes.CentralEig.dop_eigen_near_rho | exact GlobalTheory.EisRes.CentralEig.dop_eigen_near_rho | (intros; apply GlobalTheory.EisRes.CentralEig.dop_eigen_near_rho <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LaurentAut

open GlobalTheory.EisCont.Smooth
open scoped ContDiff

theorem hasDerivAt_integral_cpt {𝕜 : Type} [RCLike 𝕜] [NormedSpace 𝕜 ℂ] [ProperSpace 𝕜] {H : Type} [TopologicalSpace H] [T2Space H]
    [MeasurableSpace H] [OpensMeasurableSpace H] (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {Φ Φ' : 𝕜 → H → ℂ} {x₀ : 𝕜}
    {C : Set H} (hC : IsCompact C) (hc : ∀ t, Continuous (Φ t)) (hc' : Continuous fun p : 𝕜 × H => Φ' p.1 p.2)
    (h0 : ∀ t ∈ Metric.closedBall x₀ 1, ∀ y ∉ C, Φ t y = 0 ∧ Φ' t y = 0)
    (hd : ∀ t y, HasDerivAt (Φ · y) (Φ' t y) t) :
    HasDerivAt (fun t => ∫ y, Φ t y ∂μ) (∫ y, Φ' x₀ y ∂μ) x₀ := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall x₀ 1).prod hC).exists_bound_of_continuousOn hc'.continuousOn
  have hx : x₀ ∈ Metric.closedBall x₀ 1 := Metric.mem_closedBall_self zero_le_one
  have hc0 : Continuous (Φ' x₀) := hc'.comp (continuous_const.prodMk continuous_id)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := C.indicator fun _ => B)
    (Metric.closedBall_mem_nhds x₀ one_pos) ?_
    ((hc x₀).integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 x₀ hx y hy).1))
    (hc0.integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 x₀ hx y hy).2)).aestronglyMeasurable
    (.of_forall fun y t ht => ?_) ?_ (.of_forall fun y t _ => hd t y)).2
  · filter_upwards [Metric.closedBall_mem_nhds x₀ one_pos] with t ht
    exact ((hc t).integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 t ht y hy).1)).aestronglyMeasurable
  · by_cases hy : y ∈ C
    · rw [Set.indicator_of_mem hy]; exact hB (t, y) ⟨ht, hy⟩
    · rw [Set.indicator_of_notMem hy, (h0 t ht y hy).2, norm_zero]
  · exact (integrable_indicator_iff hC.measurableSet).2 (integrableOn_const hC.measure_lt_top.ne)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Abstract

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] {N : ℕ}
  {j : H →* G} {ι : H →* Matrix (Fin N) (Fin N) ℂ}

def IsWt (f : Matrix (Fin N) (Fin N) ℂ → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∃ S, IsCompact S ∧ (∀ B ∈ S, B.det ≠ 0) ∧ ∀ y, f y ≠ 0 → y ∈ S

theorem isWt_of_isBump {f : Matrix (Fin N) (Fin N) ℂ → ℝ} (hf : IsBump f) : IsWt f := ⟨hf.smooth, hf.supp⟩

theorem fderiv_supp {f : Matrix (Fin N) (Fin N) ℂ → ℝ} {S : Set (Matrix (Fin N) (Fin N) ℂ)} (hS : IsCompact S)
    (hfS : ∀ y, f y ≠ 0 → y ∈ S) {y : Matrix (Fin N) (Fin N) ℂ} (hy : y ∉ S) : fderiv ℝ f y = 0 := by
  by_contra h
  exact hy (closure_minimal (fun z hz => hfS z hz) hS.isClosed (support_fderiv_subset ℝ (f := f) h))

theorem IsWt.der {f : Matrix (Fin N) (Fin N) ℂ → ℝ} (hf : IsWt f) (M : Matrix (Fin N) (Fin N) ℂ) :
    IsWt fun X => fderiv ℝ f X (X * M) := by
  obtain ⟨h1, S, hS, hd, hfS⟩ := hf
  refine ⟨(h1.fderiv_right (m := ∞) le_rfl).clm_apply
    (CompanionTheory.D.gk.admitted.Gard.contDiff_mul.comp (contDiff_id.prodMk contDiff_const)), S, hS, hd, fun y hy => ?_⟩
  by_contra h
  exact hy (by simp only [fderiv_supp hS hfS h, ContinuousLinearMap.zero_apply])

variable [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  (hι : IsEmbedding ι) (h1 : ∀ y, ‖(ι y).det‖ = 1)
include hι h1

theorem exists_cpt {S T : Set (Matrix (Fin N) (Fin N) ℂ)} (hS : IsCompact S) (hd : ∀ B ∈ S, B.det ≠ 0)
    (hT : IsCompact T) : ∃ C : Set H, IsCompact C ∧ ∀ X ∈ T, ∀ y ∉ C, ι y⁻¹ * X ∉ S := by
  refine ⟨_, isCompact_preimage hι h1 (CompanionTheory.D.gk.admitted.Gard.isCompact_mul_inv hT hS hd), fun g hg x hx hB => ?_⟩
  refine hx ⟨(g, ι x⁻¹ * g), ⟨hg, hB⟩, ?_⟩
  have e : g = ι x * (ι x⁻¹ * g) := by rw [← Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mul]
  show g * (ι x⁻¹ * g)⁻¹ = ι x
  nth_rewrite 1 [e]
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hd _ hB).isUnit, Matrix.mul_one]

theorem IsWt.cpt {f : Matrix (Fin N) (Fin N) ℂ → ℝ} (hf : IsWt f) :
    (Continuous fun y => f (ι y⁻¹ * 1)) ∧ ∃ C : Set H, IsCompact C ∧ ∀ y ∉ C, f (ι y⁻¹ * 1) = 0 := by
  obtain ⟨hs, S, hS, hd, hfS⟩ := hf
  obtain ⟨C, hC, h⟩ := exists_cpt hι h1 hS hd (isCompact_singleton (x := 1))
  exact ⟨hs.continuous.comp ((hι.continuous.comp continuous_inv).mul continuous_const), C, hC,
    fun y hy => by_contra fun e => h 1 rfl y hy (hfS _ e)⟩

variable [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem IsWt.bound {f : Matrix (Fin N) (Fin N) ℂ → ℝ} (hf : IsWt f) : ∃ (C : Set H) (I : ℝ), IsCompact C ∧ 0 ≤ I ∧
    ∀ (ψ : G → ℂ) (g : G) (M : ℝ), (∀ y ∈ C, ‖ψ (g * j y)‖ ≤ M) → ∫ y, ‖f (ι y⁻¹ * 1) • ψ (g * j y)‖ ∂μ ≤ I * M := by
  obtain ⟨hw, C, hC, h0⟩ := hf.cpt hι h1
  have hI : Integrable (fun y => ‖f (ι y⁻¹ * 1)‖) μ := (hw.integrable_of_hasCompactSupport (.intro hC h0)).norm
  refine ⟨C, ∫ y, ‖f (ι y⁻¹ * 1)‖ ∂μ, hC, integral_nonneg fun _ => norm_nonneg _, fun ψ g M hM => ?_⟩
  rw [← integral_mul_const]
  refine integral_mono_of_nonneg (.of_forall fun _ => norm_nonneg _) (hI.mul_const M) (.of_forall fun y => ?_)
  by_cases hy : y ∈ C
  · simp only [norm_smul]; exact mul_le_mul_of_nonneg_left (hM y hy) (norm_nonneg _)
  · simp only [h0 y hy, zero_smul, norm_zero, zero_mul, le_rfl]

theorem deriv_avg (hj : Continuous j) {f : Matrix (Fin N) (Fin N) ℂ → ℝ} (hf : IsWt f) {ψ : G → ℂ} (hψ : Continuous ψ)
    {x : ℝ → H} (hx : ContDiff ℝ ∞ fun t => ι (x t)) (hx0 : x 0 = 1) (g : G) :
    deriv (fun t => avg j ι μ f ψ (g * j (x t))) 0 =
      avg j ι μ (fun X => fderiv ℝ f X (X * deriv (fun t => ι (x t)) 0)) ψ g := by
  obtain ⟨hs, S, hS, hd, hfS⟩ := hf
  obtain ⟨C, hC, h⟩ := exists_cpt hι h1 hS hd ((isCompact_closedBall (0 : ℝ) 1).image hx.continuous)
  have e : (fun t => avg j ι μ f ψ (g * j (x t))) = fun t => ∫ y, f (ι y⁻¹ * ι (x t)) • ψ (g * j y) ∂μ := by
    funext t
    rw [← integral_mul_left_eq_self _ (x t)]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp [← map_mul, mul_assoc]
  have hi : Continuous fun y : H => ι y⁻¹ := hι.continuous.comp continuous_inv
  have hψ' : Continuous fun y => ψ (g * j y) := by fun_prop
  have hx' : Continuous (deriv fun t => ι (x t)) := hx.continuous_deriv (by simp)
  have key := hasDerivAt_integral_cpt μ (x₀ := (0 : ℝ)) (Φ := fun t y => f (ι y⁻¹ * ι (x t)) • ψ (g * j y))
    (Φ' := fun t y => fderiv ℝ f (ι y⁻¹ * ι (x t)) (ι y⁻¹ * deriv (fun t => ι (x t)) t) • ψ (g * j y)) hC
    (fun t => (hs.continuous.comp (hi.mul continuous_const)).smul hψ')
    ((((hs.continuous_fderiv (by simp)).comp ((hi.comp continuous_snd).mul (hx.continuous.comp continuous_fst))).clm_apply
      ((hi.comp continuous_snd).mul (hx'.comp continuous_fst))).smul (hψ'.comp continuous_snd))
    (fun t ht y hy => by
      have hn := h _ ⟨t, ht, rfl⟩ y hy
      have h2 : f (ι y⁻¹ * ι (x t)) = 0 := by_contra fun e => hn (hfS _ e)
      simp only [h2, fderiv_supp hS hfS hn, ContinuousLinearMap.zero_apply, zero_smul, and_self])
    (fun t y => by
      have d1 := (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (ι y⁻¹))).hasFDerivAt.comp_hasDerivAt t
        (hx.differentiable (by simp) t).hasDerivAt
      exact ((hs.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t d1).smul_const _)
  rw [e, key.deriv]
  simp only [avg, hx0, map_one, Matrix.mul_one]

end Abstract

section Unitary

open GlobalTheory.EisRes.CentralEig

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {N : ℕ} {ι : GInf σ J →* Matrix (Fin N) (Fin N) ℂ}
  (hι : IsEmbedding ι) (h1 : ∀ y, ‖(ι y).det‖ = 1) {f : Matrix (Fin N) (Fin N) ℂ → ℝ}
include hι h1

theorem foldr_avg (hCM : IsCMExt F E σ)
    (hx : ∀ γ, IsRealLine σ J γ → ∃ x : ℝ → GInf σ J, (∀ t, γ t = ofInf σ J (x t)) ∧ ContDiff ℝ ∞ fun t => ι (x t))
    (hf : IsWt f) : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∃ f', IsWt f' ∧ ∀ ψ, Continuous ψ →
      l.foldr lineDer (avg (ofInf σ J) ι Measure.haar f ψ) = avg (ofInf σ J) ι Measure.haar f' ψ
  | [], _ => ⟨f, hf, fun _ _ => rfl⟩
  | γ :: l, hl => by
    obtain ⟨f', hf', e⟩ := foldr_avg hCM hx hf l fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
    obtain ⟨x, ex, hxs⟩ := hx γ (hl γ List.mem_cons_self)
    have hx0 : x 0 = 1 := by
      simpa using (congrArg (projInf σ J) ((ex 0).symm.trans (line_zero hCM (hl γ List.mem_cons_self))))
    refine ⟨_, hf'.der (deriv (fun t => ι (x t)) 0), fun ψ hψ => funext fun g => ?_⟩
    rw [List.foldr_cons, e ψ hψ, ← deriv_avg hι h1 Measure.haar (continuous_ofInf σ J) hf' hψ hxs hx0 g]
    simp only [lineDer, ex]

theorem avg_growth (hf : IsWt f) (m : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (ψ : GAd σ J → ℂ) (A : ℝ),
    (∀ g, ‖ψ g‖ ≤ A * (height σ J g : ℝ) ^ m) →
      ∀ g, ‖avg (ofInf σ J) ι Measure.haar f ψ g‖ ≤ K * A * (height σ J g : ℝ) ^ m := by
  obtain ⟨C, I, hC, hI, hb⟩ := hf.bound (j := ofInf σ J) hι h1 Measure.haar
  obtain ⟨c, hc⟩ := height_bddAbove_of_isCompact σ J (hC.image (continuous_ofInf σ J))
  refine ⟨I * (c : ℝ) ^ m, by positivity, fun ψ A hA g => ?_⟩
  have hA0 : 0 ≤ A := by simpa using (norm_nonneg _).trans (hA 1)
  refine (norm_integral_le_integral_norm _).trans ((hb ψ g (A * ((height σ J g : ℝ) * c) ^ m) fun y hy => ?_).trans
    (le_of_eq (by ring)))
  refine (hA _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) ?_ m) hA0)
  exact_mod_cast (height_mul_le σ J g _).trans (mul_le_mul_right (hc _ ⟨y, hy, rfl⟩) _)

theorem avg_holo (hf : IsBump f) {H₀ : ℂ → GAd σ J → ℂ} {U : Set ℂ} (hsm : ∀ s ∈ U, IsSmoothModerate σ J (H₀ s))
    (hhol : ∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) U) (g : GAd σ J) :
    DifferentiableOn ℂ (fun s => avg (ofInf σ J) ι Measure.haar f (H₀ s) g) U := by
  let W : Submodule ℂ (GAd σ J → ℂ) :=
    { carrier := {ψ | Continuous ψ}
      zero_mem' := continuous_zero
      add_mem' := fun h h' => h.add h'
      smul_mem' := fun a ψ h => h.const_smul a }
  let T : W →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => avg (ofInf σ J) ι Measure.haar f ψ g
      map_add' := fun a b => by
        simpa only [avg, Submodule.coe_add, Pi.add_apply, smul_add] using
          integral_add (integrable_avg hι h1 Measure.haar (continuous_ofInf σ J) hf a.2 g)
            (integrable_avg hι h1 Measure.haar (continuous_ofInf σ J) hf b.2 g)
      map_smul' := fun c a => by
        simp only [avg, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, ← integral_smul, smul_comm c] }
  obtain ⟨μ, hμ⟩ := T.exists_extend
  have e : ∀ ψ, Continuous ψ → μ ψ = avg (ofInf σ J) ι Measure.haar f ψ g := fun ψ hψ =>
    LinearMap.congr_fun hμ ⟨ψ, hψ⟩
  refine (hhol μ fun m => ?_).congr fun s hs => (e _ (hsm s hs).cont).symm
  obtain ⟨K, -, hK⟩ := avg_growth hι h1 (isWt_of_isBump hf) m
  refine ⟨[[]], K * 1 * (height σ J g : ℝ) ^ m, by simp, fun ψ hψ _ hb => ?_⟩
  rw [e ψ hψ.cont]
  exact hK ψ 1 (fun g => by simpa using hb [] (by simp) g) g

variable {x : Matrix (Fin n) (Fin 1) E} {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}
  {h : GAd σ J → ℝ}

theorem avg_pow (hf : IsBump f)
    (hu : ∀ κ, (∀ w, projInfArch σ J w κ ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a)) →
      ι κ ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hI : IsIwaHtG σ J x L a h) (hc : Continuous h) : ∃ b : ℂ → ℂ, Differentiable ℂ b ∧ (∀ t : ℝ, b t ≠ 0) ∧
      ∀ t g, avg (ofInf σ J) ι Measure.haar f (fun g => (h g : ℂ) ^ t) g = b t * (h g : ℂ) ^ t := by
  obtain ⟨hw, C, hC, h0⟩ := (isWt_of_isBump hf).cpt hι h1
  have hj : Continuous fun y => h (1 * ofInf σ J y) := hc.comp (continuous_const.mul (continuous_ofInf σ J))
  have hne : ∀ g, (h g : ℂ) ≠ 0 := fun g => by exact_mod_cast (ht_pos hI g).ne'
  have hsl : ∀ g, (h g : ℂ) ∈ Complex.slitPlane := fun g => Or.inl (by simpa using ht_pos hI g)
  refine ⟨fun t => avg (ofInf σ J) ι Measure.haar f (fun g => (h g : ℂ) ^ t) 1, fun t => ?_, fun t => ?_, fun t g => ?_⟩
  · have hj' := Complex.continuous_ofReal.comp hj
    exact (hasDerivAt_integral_cpt Measure.haar (x₀ := t) (Φ := fun t y => f (ι y⁻¹ * 1) • (h (1 * ofInf σ J y) : ℂ) ^ t)
      (Φ' := fun t y => f (ι y⁻¹ * 1) • ((h (1 * ofInf σ J y) : ℂ) ^ t * Complex.log (h (1 * ofInf σ J y)))) hC
      (fun t => hw.smul (hj'.cpow continuous_const fun y => hsl _))
      ((hw.comp continuous_snd).smul (((hj'.comp continuous_snd).cpow continuous_fst fun y => hsl _).mul
        ((hj'.comp continuous_snd).clog fun y => hsl _)))
      (fun t _ y hy => by simp only [h0 y hy, zero_smul, and_self])
      (fun t y => ((Complex.hasStrictDerivAt_const_cpow (Or.inl (hne _))).hasDerivAt).const_smul
        (f (ι y⁻¹ * 1)))).differentiableAt
  · have e : avg (ofInf σ J) ι Measure.haar f (fun g => (h g : ℂ) ^ (t : ℂ)) 1 =
        ((∫ y, f (ι y⁻¹ * 1) * h (1 * ofInf σ J y) ^ t ∂Measure.haar : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (.of_forall fun y => ?_)
      simp only [Complex.ofReal_mul, Complex.real_smul, Complex.ofReal_cpow (ht_pos hI _).le]
    have hpos := (hw.mul (hj.rpow_const fun y => Or.inl (ht_pos hI _).ne')).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (μ := Measure.haar) (x := 1) (HasCompactSupport.mul_right (.intro hC h0) (f' := fun y => h (1 * ofInf σ J y) ^ t))
      (fun y => mul_nonneg (hf.nonneg _) (Real.rpow_pos_of_pos (ht_pos hI _) t).le)
      (mul_ne_zero (by simpa using hf.one) (Real.rpow_pos_of_pos (ht_pos hI _) t).ne')
    show avg (ofInf σ J) ι Measure.haar f (fun g => (h g : ℂ) ^ (t : ℂ)) 1 ≠ 0
    rw [e]
    exact_mod_cast hpos.ne'
  · obtain ⟨p, k, hk, rfl⟩ := exists_iwa hI g
    rw [avg_mul hι h1 Measure.haar hf (κ := projInf σ J k) (hu _ fun w => by simpa using (mem_levelAll.1 hk).2 w)
      (fun y => ext_inf_fin σ J (by simp) (by simp))]
    simp only [avg, ht_right hI _ hk, pow_left hI p.2, one_mul, ← integral_mul_const, smul_mul_assoc, mul_comm ((h p : ℂ) ^ t)]

end Unitary

open GlobalTheory.EisRes.CentralEig in

theorem uniform_growth_near_rho {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E}
    {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)} {h : GAd σ J → ℝ} {Eis : ℂ → GAd σ J → ℂ}
    (hS : HidaSetting σ J X Y L a h) (hP : IsSerG σ J (col0 X) h Eis) {k₀ : ℕ} {U₀ : Set ℂ} {H₀ : ℂ → GAd σ J → ℂ}
    (hU₀ : U₀ ∈ 𝓝 (((n : ℂ) - 1) / 2))
    (hH : ∀ s ∈ U₀, s ≠ (((n : ℂ) - 1) / 2) → ∀ g, H₀ s g = (s - (((n : ℂ) - 1) / 2)) ^ k₀ * Eis s g)
    (hsm : ∀ s ∈ U₀, IsSmoothModerate σ J (H₀ s))
    (hhol : ∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) U₀) :
    ∃ V ∈ 𝓝 (((n : ℂ) - 1) / 2), ∃ m : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∃ C : ℝ, ∀ s ∈ V, ∀ g, ‖l.foldr lineDer (H₀ s) g‖ ≤ C * (height σ J g : ℝ) ^ m := by
  set ρ : ℂ := ((n : ℂ) - 1) / 2 with hρ
  have hρre : ρ.re = ((n : ℝ) - 1) / 2 := by simp [hρ]
  have hc : Continuous h := HtCont.continuous_iwaHt F E σ n J r X Y L a h hS
  have hcmp := iwaHt_mul_le_of_isCompact F E σ n J r X Y L a h hS
  obtain ⟨hCM, -, hJ, hn, -, hA, hI⟩ := hS
  obtain ⟨N, ι, hι, h1, hu, hx⟩ := exists_mat hCM hJ fun w => Formalism.UG.bc (compInf F E w) a
  obtain ⟨f, hf, -, -⟩ := exists_bump hι h1 Measure.haar (V := Set.univ) univ_mem
  obtain ⟨b, hbd, hb0, hb⟩ := avg_pow hι h1 hf hu hI hc
  obtain ⟨T, hT⟩ := exists_reps σ J (col0 X)
  have heig : ∀ s : ℂ, ρ.re < s.re → ∀ g, avg (ofInf σ J) ι Measure.haar f (Eis s) g = b (s + ρ) * Eis s g := by
    intro s hs g
    have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hre : 0 ≤ (s + ρ).re := by rw [Complex.add_re]; rw [hρre] at hs ⊢; linarith
    rw [hρre] at hs
    have hsum := hP T hT s hs
    haveI : Countable T := by
      have := (hsum g).summable.countable_support
      rw [Function.support_eq_univ fun t => by
        simp only [ne_eq, Complex.cpow_eq_zero_iff, Complex.ofReal_eq_zero, (ht_pos hI _).ne', false_and,
          not_false_eq_true]] at this
      exact Set.countable_univ_iff.1 this
    obtain ⟨C, I, hC, hI0, hbd⟩ := (isWt_of_isBump hf).bound (j := ofInf σ J) hι h1 Measure.haar
    obtain ⟨K, hK0, hK⟩ := hcmp _ (hC.image (continuous_ofInf σ J))
    have hcp : Continuous fun g => (h g : ℂ) ^ (s + ρ) :=
      (Complex.continuous_ofReal.comp hc).cpow continuous_const fun g => Or.inl (by simpa using ht_pos hI g)
    have key := hasSum_integral_of_summable_integral_norm (μ := Measure.haar)
      (F := fun (t : T) y => f (ι y⁻¹ * 1) • (h (t.1.1 * g * ofInf σ J y) : ℂ) ^ (s + ρ))
      (fun t => integrable_avg hι h1 Measure.haar (continuous_ofInf σ J) hf hcp _)
      (.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _)
        (fun t => hbd (fun g => (h g : ℂ) ^ (s + ρ)) (t.1.1 * g) (K ^ (s + ρ).re * ‖(h (t.1.1 * g) : ℂ) ^ (s + ρ)‖)
          fun y hy => by
            rw [Complex.norm_cpow_eq_rpow_re_of_pos (ht_pos hI _), Complex.norm_cpow_eq_rpow_re_of_pos (ht_pos hI _),
              ← Real.mul_rpow hK0 (ht_pos hI _).le]
            exact Real.rpow_le_rpow (ht_pos hI _).le (hK _ _ ⟨y, hy, rfl⟩) hre)
        (((summable_norm_iff.2 (hsum g).summable).mul_left _).mul_left _))
    have e1 : (fun t : T => ∫ y, f (ι y⁻¹ * 1) • (h (t.1.1 * g * ofInf σ J y) : ℂ) ^ (s + ρ) ∂Measure.haar) =
        fun t : T => b (s + ρ) * (h (t.1.1 * g) : ℂ) ^ (s + ρ) := funext fun t => hb (s + ρ) (t.1.1 * g)
    have e2 : (fun y => ∑' t : T, f (ι y⁻¹ * 1) • (h (t.1.1 * g * ofInf σ J y) : ℂ) ^ (s + ρ)) =
        fun y => f (ι y⁻¹ * 1) • Eis s (g * ofInf σ J y) := funext fun y => by
      simpa only [mul_assoc] using ((hsum (g * ofInf σ J y)).const_smul (f (ι y⁻¹ * 1))).tsum_eq
    rw [e1, e2] at key
    exact key.unique ((hsum g).mul_left _)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU₀
  have hbd' : Differentiable ℂ fun s => b (s + ρ) := hbd.comp (differentiable_id.add_const ρ)
  have hall : ∀ g, ∀ s ∈ Metric.ball ρ ε, avg (ofInf σ J) ι Measure.haar f (H₀ s) g = b (s + ρ) * H₀ s g := by
    intro g
    have a1 := ((avg_holo hι h1 hf hsm hhol g).mono hball).analyticOnNhd Metric.isOpen_ball
    have hd : DifferentiableOn ℂ (fun s => H₀ s g) (Metric.ball ρ ε) :=
      (hhol _ (GlobalTheory.EisLine.isModerateForm_proj σ J g)).mono hball
    have a2 := (hbd'.differentiableOn.fun_mul hd).analyticOnNhd Metric.isOpen_ball
    set z₀ : ℂ := ρ + ((ε / 2 : ℝ) : ℂ) with hz₀
    have hz₀b : z₀ ∈ Metric.ball ρ ε := by
      rw [Metric.mem_ball, hz₀, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      linarith
    have hz₀re : ρ.re < z₀.re := by simp [hz₀, hε]
    have hopen : IsOpen (Metric.ball ρ ε ∩ {s : ℂ | ρ.re < s.re}) :=
      Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
    refine a1.eqOn_of_preconnected_of_eventuallyEq a2 (convex_ball ρ ε).isPreconnected hz₀b ?_
    filter_upwards [hopen.mem_nhds ⟨hz₀b, hz₀re⟩] with s hs'
    have hne : s ≠ ρ := by rintro rfl; exact lt_irrefl ρ.re hs'.2
    rw [hH s (hball hs'.1) hne, mul_left_comm, ← heig s hs'.2 g]
    simp only [avg, hH s (hball hs'.1) hne, ← integral_const_mul, mul_smul_comm]
  have hρ0 : b (ρ + ρ) ≠ 0 := by
    have : ρ + ρ = (((n : ℝ) - 1 : ℝ) : ℂ) := by rw [hρ]; push_cast; ring
    rw [this]; exact hb0 _
  have hV : ∀ᶠ s in 𝓝 ρ, b (s + ρ) ≠ 0 ∧ ‖(b (s + ρ))⁻¹‖ < ‖(b (ρ + ρ))⁻¹‖ + 1 :=
    (hbd'.continuous.continuousAt.eventually_ne hρ0).and
      ((hbd'.continuous.continuousAt.inv₀ hρ0).norm.eventually (gt_mem_nhds (lt_add_one _)))
  obtain ⟨-, m, A, hmA⟩ := GlobalTheory.WeakHolFamily.word_holomorphic_and_uniform F E σ n J H₀ (Metric.ball ρ ε)
    (Metric.closedBall ρ (ε / 2)) Metric.isOpen_ball (isCompact_closedBall _ _)
    (Metric.closedBall_subset_ball (half_lt_self hε)) (fun s hs => hsm s (hball hs))
    (fun μ hμ => (hhol μ hμ).mono hball) [] (by simp)
  refine ⟨_, inter_mem hV (Metric.closedBall_mem_nhds ρ (half_pos hε)), m, fun l hl => ?_⟩
  obtain ⟨f', hf', e⟩ := foldr_avg hι h1 hCM hx (isWt_of_isBump hf) l hl
  obtain ⟨K, hK0, hK⟩ := avg_growth hι h1 hf' m
  refine ⟨(‖(b (ρ + ρ))⁻¹‖ + 1) * (K * A), fun s hs g => ?_⟩
  have hsb : s ∈ Metric.ball ρ ε := Metric.closedBall_subset_ball (half_lt_self hε) hs.2
  have e1 : avg (ofInf σ J) ι Measure.haar f (H₀ s) = b (s + ρ) • H₀ s := funext fun g => hall g s hsb
  have e2 : l.foldr lineDer (b (s + ρ) • H₀ s) g = b (s + ρ) * l.foldr lineDer (H₀ s) g := by
    have := congrFun (GlobalTheory.UAut.dop_smul (Finsupp.single l 1) (b (s + ρ)) (H₀ s)) g
    simpa [GlobalTheory.UAut.dop] using this
  have e3 : l.foldr lineDer (H₀ s) g = (b (s + ρ))⁻¹ * avg (ofInf σ J) ι Measure.haar f' (H₀ s) g := by
    rw [← e _ (hsm s (hball hsb)).cont, e1, e2, inv_mul_cancel_left₀ hs.1.1]
  rw [e3, norm_mul, mul_assoc]
  exact mul_le_mul hs.1.2.le (hK _ A (hmA s hs.2) g) (norm_nonneg _) (by positivity)

set_option maxHeartbeats 1000000 in

theorem isAut_laurentCoeff_sub_const : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c →
    ∀ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 (((n : ℂ) - 1) / 2) → (∀ g, DifferentiableOn ℂ (H · g) U) →
      (∀ s ∈ U, s ≠ (((n : ℂ) - 1) / 2) → ∀ g, H s g = (s - (((n : ℂ) - 1) / 2)) ^ k * Eis s g) →
      ∀ c₀ : ℂ, GlobalTheory.UAut.IsAut σ J (levelAll σ J L a ⊓ infPts σ J) (fun g => H (((n : ℂ) - 1) / 2) g - c₀) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h Eis c hS hP k U H hU hHd hHe c₀
  obtain ⟨k₀, U₀, H₀, hU₀, hH₀e, hH₀sm, hH₀hol⟩ := hP.2.2.2.1 (((n : ℂ) - 1) / 2)
  obtain ⟨V₁, hV₁, hE1⟩ := GlobalTheory.T.eisenstein_residue_holomorphic_region F E σ n J r X Y L a h Eis c hS hP k₀ U₀ H₀ hU₀ hH₀e hH₀sm hH₀hol
  obtain ⟨V₂, hV₂, hE2⟩ := GlobalTheory.T.exists_nhds_dop_central_eq_holomorphic_smul F E σ n J r X Y L a h Eis c hS hP k₀ U₀ H₀ hU₀ hH₀e hH₀sm hH₀hol
  obtain ⟨V₃, hV₃, m, hE3⟩ := uniform_growth_near_rho hS hP.1 hU₀ hH₀e hH₀sm hH₀hol
  obtain ⟨hCM, -, hJ, -, -, hA, -⟩ := hS
  haveI := hA.lat
  set ρ : ℂ := ((n : ℂ) - 1) / 2 with hρ
  set W : Set ℂ := interior (U ∩ U₀ ∩ (V₁ ∩ V₃) ∩ V₂) with hWdef
  have hWo : IsOpen W := isOpen_interior
  have hWn : W ∈ 𝓝 ρ := interior_mem_nhds.2 (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hU hU₀) (Filter.inter_mem hV₁ hV₃)) hV₂)
  have hWU : W ⊆ U := fun x hx => (interior_subset hx).1.1.1
  have hWU₀ : W ⊆ U₀ := fun x hx => (interior_subset hx).1.1.2
  have hWV₁ : W ⊆ V₁ := fun x hx => (interior_subset hx).1.2.1
  have hWV₃ : W ⊆ V₃ := fun x hx => (interior_subset hx).1.2.2
  have hWV₂ : W ⊆ interior V₂ := interior_mono fun x hx => hx.2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hWn
  have hr : (0 : ℝ) < ε / 2 := by linarith
  have hcb : Metric.closedBall ρ (ε / 2) ⊆ W := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hsph : Metric.sphere ρ (ε / 2) ⊆ W := Metric.sphere_subset_closedBall.trans hcb
  have hsmW : ∀ s ∈ W, IsSmoothModerate σ J (H₀ s) := fun s hs => hH₀sm s (hWU₀ hs)
  have hholW : ∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) W :=
    fun μ hμ => (hH₀hol μ hμ).mono hWU₀
  have hH₀d : ∀ g, DifferentiableOn ℂ (H₀ · g) W := fun g => hholW _ (GlobalTheory.EisLine.isModerateForm_proj σ J g)
  let Rj : ℤ → GAd σ J → ℂ := fun j g => circleIntegral (fun z => (z - ρ) ^ j * H₀ z g) ρ (ε / 2)
  have hHR : ∀ g, H ρ g = (2 * ↑Real.pi * Complex.I)⁻¹ * Rj ((k : ℤ) - k₀ - 1) g :=
    GlobalTheory.eval_center_eq_circleIntegral_shifted_order ρ k k₀ (ε / 2) W Eis H H₀ hr hWo hcb (fun g => (hHd g).mono hWU) hH₀d
      (fun s hs hne g => hHe s (hWU hs) hne g) (fun s hs hne g => hH₀e s (hWU₀ hs) hne g)
  have hinv : ∀ j g, ∀ k ∈ levelAll σ J L a, Rj j (g * k) = Rj j g := fun j g k hk =>
    circleIntegral.integral_congr hr.le fun z hz => by
      simp only [hE1 z (hWV₁ (hsph hz)) k hk g]
  have hzfin : ∀ j, FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, GlobalTheory.UAut.IsCentral σ J z ∧ f = GlobalTheory.UAut.dop z (Rj j)}) := by
    intro j
    haveI := FiniteDimensional.span_of_finite ℂ (Set.finite_range fun i : Fin (-j).toNat => Rj (j + i))
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun i : Fin (-j).toNat => Rj (j + i)))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨χ, hχ, hχe⟩ := hE2 z hz
    obtain ⟨cc, hcc⟩ := GlobalTheory.circleIntegral_zpow_mul_holo_mul_eq_sum ρ (ε / 2) W χ H₀ hr hWo hcb (hχ.mono hWV₂) hH₀d j
    have e : GlobalTheory.UAut.dop z (Rj j) = ∑ i : Fin (-j).toNat, cc i • Rj (j + i) := by
      funext g
      rw [GlobalTheory.T.moderate_eisenstein_holomorphic_derivative F E σ hCM n J hJ H₀ ρ (ε / 2) W hWo hr hcb hsmW hholW j z hz.1 g]
      rw [circleIntegral.integral_congr hr.le (g := fun w => (w - ρ) ^ j * (χ w * H₀ w g)) fun w hw => by
        simp only [hχe w (interior_subset (hWV₂ (hsph hw))), Pi.smul_apply, smul_eq_mul]]
      rw [hcc g, Finset.sum_apply]
      exact (Fin.sum_univ_eq_sum_range (fun i => cc i * circleIntegral (fun w => (w - ρ) ^ (j + (i : ℤ)) * H₀ w g) ρ (ε / 2)) _).symm
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have haut : ∀ j, GlobalTheory.UAut.IsAut σ J (levelAll σ J L a ⊓ infPts σ J) (Rj j) := by
    intro j
    have hleft : ∀ γ ∈ ratPts σ J, ∀ g, Rj j (γ * g) = Rj j g := fun γ hγ g =>
      circleIntegral.integral_congr hr.le fun z hz => by
        simp only [(hsmW z (hsph hz)).left γ hγ g]
    have hlev : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, Rj j (g * k) = Rj j g :=
      ⟨levelOpen σ J L, isOpen_levelOpen σ J L, fun k hk hkf g => hinv j g k (mem_levelAll.2
        ⟨mem_levelOpen.1 hk, fun w => by rw [mem_finPts_iff_forall.1 hkf w]; exact one_mem _⟩)⟩
    have hcont := GlobalTheory.CircleCont.continuous_circleIntegral_family F E σ hCM n J hJ H₀ ρ (ε / 2) W hWo hr hcb hsmW hholW j
    have hsm := GlobalTheory.T.moderate_eisenstein_holomorphic_ball F E σ hCM n J hJ H₀ ρ (ε / 2) W hWo hr hcb hsmW hholW j
    have hkf : GlobalTheory.Doubling.IsKFinite (levelAll σ J L a ⊓ infPts σ J) (Rj j) :=
      GlobalTheory.Doubling.IsKFinite.of_invariant fun g k hk => hinv j g k (Subgroup.mem_inf.1 hk).1
    have hgr : ∃ N : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
        ∃ C : ℝ, ∀ g, ‖l.foldr lineDer (Rj j) g‖ ≤ C * (height σ J g : ℝ) ^ N := by
      refine ⟨m, fun l hl => ?_⟩
      obtain ⟨C, hC⟩ := hE3 l hl
      refine ⟨2 * Real.pi * (ε / 2) * ((ε / 2) ^ j * C), fun g => ?_⟩
      have e := GlobalTheory.T.moderate_eisenstein_holomorphic_derivative F E σ hCM n J hJ H₀ ρ (ε / 2) W hWo hr hcb hsmW hholW j (Finsupp.single l 1)
        (fun l' hl' => by rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hl')]; exact hl) g
      simp only [GlobalTheory.UAut.dop, zero_mul, Finsupp.sum_single_index, one_mul] at e
      have hb : ∀ z ∈ Metric.sphere ρ (ε / 2),
          ‖(z - ρ) ^ j * l.foldr lineDer (H₀ z) g‖ ≤ (ε / 2) ^ j * C * (height σ J g : ℝ) ^ m := by
        intro z hz
        have hz' : ‖z - ρ‖ = ε / 2 := by simpa [dist_eq_norm] using hz
        rw [norm_mul, norm_zpow, hz', mul_assoc]
        exact mul_le_mul_of_nonneg_left (hC z (hWV₃ (hsph hz)) g) (zpow_nonneg hr.le j)
      refine (congrArg norm e).le.trans ((circleIntegral.norm_integral_le_of_norm_le_const hr.le hb).trans (le_of_eq ?_))
      ring
    exact ⟨⟨hleft, hlev, hcont, hsm, hgr⟩, GlobalTheory.UAut.kfin_iff.2 hkf, hzfin j⟩
  have e : (fun g => H ρ g - c₀) = (fun _ => -c₀) + (2 * ↑Real.pi * Complex.I)⁻¹ • Rj ((k : ℤ) - k₀ - 1) := by
    funext g; simp only [hHR, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e]
  have h1 := GlobalTheory.UAut.isAut_iff_isAutOn.1 (haut ((k : ℤ) - k₀ - 1))
  have h2 := (GlobalTheory.UAut.isAutOn_add_smul F E σ hCM n J hJ _ _ _ _ ((2 * ↑Real.pi * Complex.I)⁻¹) h1 h1).2
  exact GlobalTheory.UAut.isAut_iff_isAutOn.2
    (GlobalTheory.UAut.isAutOn_add_smul F E σ hCM n J hJ _ _ _ _ 1 (GlobalTheory.UAut.isAutOn_const σ J _ _ (-c₀)) h2).1

end GlobalTheory.LaurentAut
end
end
