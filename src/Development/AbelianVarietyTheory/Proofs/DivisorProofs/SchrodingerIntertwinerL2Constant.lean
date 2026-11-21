import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslationSeminormBound
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormSmulLeftLinearPhaseLe
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCoeffContinuousRapidDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairingCoordinatesSchrodingerFolland
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero

section
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.SchwartzIntegral

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def weightedDeriv (k m : ℕ) (f : 𝓢(E, ℂ)) : E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ m f x)
    ((continuous_norm.pow k).smul ((f.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)))
    (SchwartzMap.seminorm ℂ k m f) (fun x => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact f.le_seminorm ℂ k m x)

theorem weightedDeriv_apply (k m : ℕ) (f : 𝓢(E, ℂ)) (x : E) :
    weightedDeriv k m f x = (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ m f x := rfl

theorem norm_weightedDeriv_le (k m : ℕ) (f : 𝓢(E, ℂ)) :
    ‖weightedDeriv k m f‖ ≤ SchwartzMap.seminorm ℂ k m f :=
  (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr fun x => by
    rw [weightedDeriv_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact f.le_seminorm ℂ k m x

theorem seminorm_le_norm_weightedDeriv (k m : ℕ) (f : 𝓢(E, ℂ)) :
    SchwartzMap.seminorm ℂ k m f ≤ ‖weightedDeriv k m f‖ :=
  SchwartzMap.seminorm_le_bound ℂ k m f (norm_nonneg _) fun x => by
    have h := (weightedDeriv k m f).norm_coe_le_norm x
    rwa [weightedDeriv_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h

def weightedDerivCLM (k m : ℕ) :
    𝓢(E, ℂ) →L[ℂ] (E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (weightedDeriv k m)
    (fun f g => by
      ext x : 1
      simp only [weightedDeriv_apply, BoundedContinuousFunction.coe_add, Pi.add_apply, SchwartzMap.add_apply]
      rw [show ⇑(f + g) = ⇑f + ⇑g from rfl, iteratedFDeriv_add_apply ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
        ((g.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt, smul_add])
    (fun a f => by
      ext x : 1
      simp only [weightedDeriv_apply, BoundedContinuousFunction.coe_smul, Pi.smul_apply,
        RingHom.id_apply]
      rw [show ⇑(a • f) = a • ⇑f from rfl,
        iteratedFDeriv_const_smul_apply ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt, smul_comm])
    ⟨{(k, m)}, 1, zero_le_one, fun f => by
      simpa [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply] using norm_weightedDeriv_le k m f⟩

theorem weightedDerivCLM_apply (k m : ℕ) (f : 𝓢(E, ℂ)) : weightedDerivCLM k m f = weightedDeriv k m f := rfl

section Param

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] {ν : Measure W}

theorem continuous_iteratedFDeriv_param {G : W → 𝓢(E, ℂ)} (hG : Continuous G) (m : ℕ) (y : E) :
    Continuous fun w => iteratedFDeriv ℝ m (G w) y := by
  have h := ((BoundedContinuousFunction.evalCLM ℂ y).comp (weightedDerivCLM (E := E) 0 m)).continuous.comp hG
  refine h.congr fun w => ?_
  simp [weightedDerivCLM_apply, weightedDeriv_apply]

theorem integrable_iteratedFDeriv_param {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) (m : ℕ) (y : E) :
    Integrable (fun w => iteratedFDeriv ℝ m (G w) y) ν :=
  (hint 0 m).mono' (continuous_iteratedFDeriv_param hG m y).aestronglyMeasurable
    (.of_forall fun w => (G w).norm_iteratedFDeriv_le_seminorm ℂ m y)

theorem iteratedFDeriv_eq_integral {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) {g : 𝓢(E, ℂ)}
    (hg : ∀ x, g x = ∫ w, G w x ∂ν) (m : ℕ) :
    iteratedFDeriv ℝ m g = fun x => ∫ w, iteratedFDeriv ℝ m (G w) x ∂ν := by
  induction m with
  | zero =>
    funext x
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, hg x]
    exact ((continuousMultilinearCurryFin0 ℝ E ℂ).symm.toLinearIsometry.integral_comp_comm _).symm
  | succ m ih =>
    funext x
    set Ψ := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) ℂ
    have key : ∀ (f : E → ℂ) (y : E), iteratedFDeriv ℝ (m + 1) f y = Ψ.symm (fderiv ℝ (iteratedFDeriv ℝ m f) y) := by
      intro f y
      rw [iteratedFDeriv_succ_eq_comp_left]
      rfl
    have hdiff : ∀ w, Differentiable ℝ (iteratedFDeriv ℝ m (G w)) := fun w =>
      ((G w).smooth ⊤).differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top m)
    have hF' : ∀ w y, fderiv ℝ (iteratedFDeriv ℝ m (G w)) y = Ψ (iteratedFDeriv ℝ (m + 1) (G w) y) := by
      intro w y
      rw [key, LinearIsometryEquiv.apply_symm_apply]
    have hd : HasFDerivAt (fun y => ∫ w, iteratedFDeriv ℝ m (G w) y ∂ν)
        (∫ w, fderiv ℝ (iteratedFDeriv ℝ m (G w)) x ∂ν) x := by
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun w => SchwartzMap.seminorm ℂ 0 (m + 1) (G w))
        Filter.univ_mem (.of_forall fun y => (continuous_iteratedFDeriv_param hG m y).aestronglyMeasurable)
        (integrable_iteratedFDeriv_param hG hint m x) ?_ (.of_forall fun w y _ => ?_) (hint 0 (m + 1))
        (.of_forall fun w y _ => (hdiff w y).hasFDerivAt)
      · simp_rw [hF']
        exact (Ψ.continuous.comp (continuous_iteratedFDeriv_param hG (m + 1) x)).aestronglyMeasurable
      · rw [norm_fderiv_iteratedFDeriv]
        exact (G w).norm_iteratedFDeriv_le_seminorm ℂ (m + 1) y
    rw [key, ih, hd.fderiv]
    have := Ψ.symm.toLinearIsometry.integral_comp_comm (μ := ν) (fun w => fderiv ℝ (iteratedFDeriv ℝ m (G w)) x)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at this
    rw [← this]
    simp_rw [hF', LinearIsometryEquiv.symm_apply_apply]

abbrev Target (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset (ℕ × ℕ)) : Type :=
  (i : s) → (E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => E) ℂ)

def embed (s : Finset (ℕ × ℕ)) : 𝓢(E, ℂ) →L[ℂ] Target E s :=
  ContinuousLinearMap.pi fun i => weightedDerivCLM i.1.1 i.1.2

theorem embed_apply (s : Finset (ℕ × ℕ)) (f : 𝓢(E, ℂ)) (i : s) : embed s f i = weightedDeriv i.1.1 i.1.2 f := rfl

theorem norm_embed_le (s : Finset (ℕ × ℕ)) (f : 𝓢(E, ℂ)) :
    ‖embed s f‖ ≤ ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 f :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => apply_nonneg _ _)).mpr fun i =>
    (norm_weightedDeriv_le _ _ f).trans
      (Finset.single_le_sum (f := fun j : ℕ × ℕ => SchwartzMap.seminorm ℂ j.1 j.2 f)
        (fun j _ => apply_nonneg _ _) i.2)

theorem seminorm_le_norm_embed (s : Finset (ℕ × ℕ)) (f : 𝓢(E, ℂ)) {i : ℕ × ℕ} (hi : i ∈ s) :
    SchwartzMap.seminorm ℂ i.1 i.2 f ≤ ‖embed s f‖ :=
  (seminorm_le_norm_weightedDeriv _ _ f).trans (norm_le_pi_norm (embed s f) ⟨i, hi⟩)

theorem clm_apply_eq_integral (L : 𝓢(E, ℂ) →L[ℂ] ℂ) {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) {g : 𝓢(E, ℂ)}
    (hg : ∀ x, g x = ∫ w, G w x ∂ν) : L g = ∫ w, L (G w) ∂ν := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ)
    ((normSeminorm ℂ ℂ).comp (L : 𝓢(E, ℂ) →ₗ[ℂ] ℂ)) (continuous_norm.comp L.continuous)
  have hL : ∀ f, ‖L f‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ E ℂ)) f := fun f => hC f
  set t := insert ((0 : ℕ), (0 : ℕ)) s
  have hLt : ∀ f, ‖L f‖ ≤ C * ‖embed t f‖ := fun f => (hL f).trans (mul_le_mul_of_nonneg_left
    (Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi =>
      seminorm_le_norm_embed t f (Finset.mem_insert_of_mem hi)) C.2)
  have hinj : Function.Injective (embed (E := E) t) := by
    refine (injective_iff_map_eq_zero (embed (E := E) t)).mpr fun f hf => ?_
    ext x
    have h1 := seminorm_le_norm_embed t f (Finset.mem_insert_self _ _)
    rw [hf, norm_zero] at h1
    have h2 := (f.norm_le_seminorm ℂ x).trans h1
    simpa using h2
  let Φ : 𝓢(E, ℂ) →ₗ[ℂ] Target E t := (embed (E := E) t : 𝓢(E, ℂ) →ₗ[ℂ] Target E t)
  let e := LinearEquiv.ofInjective Φ hinj
  have he : ∀ y : LinearMap.range Φ, embed t (e.symm y) = y := fun y => by
    have := congrArg Subtype.val (e.apply_symm_apply y)
    exact (LinearEquiv.ofInjective_apply Φ (e.symm y)).symm.trans this
  let f0 : LinearMap.range Φ →ₗ[ℂ] ℂ := (L : 𝓢(E, ℂ) →ₗ[ℂ] ℂ).comp e.symm.toLinearMap
  let f1 : StrongDual ℂ (LinearMap.range Φ) := f0.mkContinuous C fun y => by
    show ‖L (e.symm y)‖ ≤ C * ‖(y : Target E t)‖
    rw [← he]
    exact hLt _
  obtain ⟨ℓ, hℓ, -⟩ := exists_extension_norm_eq (LinearMap.range Φ) f1
  have hLℓ : ∀ f, L f = ℓ (embed t f) := by
    intro f
    have h1 := hℓ ⟨embed t f, LinearMap.mem_range_self Φ f⟩
    have h2 : e.symm ⟨embed t f, LinearMap.mem_range_self Φ f⟩ = f := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    have h3 : ℓ (embed t f) = f1 ⟨embed t f, LinearMap.mem_range_self Φ f⟩ := h1
    rw [h3, LinearMap.mkContinuous_apply]
    show L f = L (e.symm _)
    rw [h2]
  have hcont : Continuous fun w => embed t (G w) := (embed t).continuous.comp hG
  haveI : SecondCountableTopology W := inferInstance
  haveI : SecondCountableTopologyEither W (Target E t) := secondCountableTopologyEither_of_left _ _
  have hInt : Integrable (fun w => embed t (G w)) ν :=
    (integrable_finset_sum t fun i _ => hint i.1 i.2).mono' hcont.aestronglyMeasurable
      (.of_forall fun w => norm_embed_le t (G w))
  have hemb : embed t g = ∫ w, embed t (G w) ∂ν := by
    funext i
    refine BoundedContinuousFunction.ext fun x => ?_
    have h1 := ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun i : t => E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => E) ℂ) i)).integral_comp_comm hInt
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      BoundedContinuousFunction.evalCLM_apply] at h1
    rw [← h1]
    simp only [embed_apply, weightedDeriv_apply]
    rw [integral_smul, iteratedFDeriv_eq_integral hG hint hg]
  rw [hLℓ g, hemb, ← ℓ.integral_comp_comm hInt]
  simp_rw [← hLℓ]

end Param

theorem clm_integral_interchange : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (ν : Measure W) [SigmaFinite ν] (n : ℕ) (L : Sch (Fin n) →L[ℂ] ℂ)
    (G : W → Sch (Fin n)) (c : W → ℂ) (g : Sch (Fin n)), Continuous G → Continuous c →
    (∀ k m : ℕ, Integrable (fun w => ‖c w‖ * SchwartzMap.seminorm ℂ k m (G w)) ν) →
    (∀ x, g x = ∫ w, c w * G w x ∂ν) → L g = ∫ w, c w * L (G w) ∂ν := by
  intro W _ _ _ _ _ ν _ n L G c g hG hc hint hg
  have hG' : Continuous fun w => c w • G w := hc.smul hG
  have hint' : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (c w • G w)) ν := by
    intro k m
    simpa only [map_smul_eq_mul] using hint k m
  have hg' : ∀ x, g x = ∫ w, (c w • G w) x ∂ν := by
    intro x
    rw [hg x]
    rfl
  rw [clm_apply_eq_integral L hG' hint' hg']
  simp only [map_smul, smul_eq_mul]

end GlobalTheory.SchwartzIntegral
end
end

section
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_functional_integral_comm : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
    [BorelSpace W] (ν : Measure W) [SigmaFinite ν] (n : ℕ) (L : Sch (Fin n) →L[ℂ] ℂ) (G : W → Sch (Fin n))
    (c : W → ℂ) (g : Sch (Fin n)), Continuous G → Continuous c →
    (∀ k m : ℕ, Integrable (fun w => ‖c w‖ * SchwartzMap.seminorm ℂ k m (G w)) ν) →
    (∀ x, g x = ∫ w, c w * G w x ∂ν) → L g = ∫ w, c w * L (G w) ∂ν := by
  first | exact @GlobalTheory.SchwartzIntegral.clm_integral_interchange | exact GlobalTheory.SchwartzIntegral.clm_integral_interchange | (intros; apply GlobalTheory.SchwartzIntegral.clm_integral_interchange <;> assumption)
end

section
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic

noncomputable section

namespace GlobalTheory.PhaseLipschitz

def psi (k : ℝ) : ℝ → ℂ := fun t =>
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) - 1

theorem eChar_sub_one_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (k : ℝ) :
    (fun y => eChar (L y + k) - 1) = psi k ∘ ⇑L := by
  funext y
  simp only [psi, Function.comp_apply, eChar_apply, ← Complex.exp_add]
  congr 2; push_cast; ring

theorem contDiff_psi (k : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (psi k) := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  unfold psi; fun_prop

theorem norm_psi_le (k t : ℝ) : ‖psi k t‖ ≤ 2 * Real.pi * |t + k| := by
  have e : psi k t = Complex.exp (Complex.I * ((2 * Real.pi * (t + k) : ℝ) : ℂ)) - 1 := by
    simp only [psi, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [e]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]

theorem iteratedDeriv_psi_succ (k : ℝ) (j : ℕ) :
    iteratedDeriv (j + 1) (psi k) = fun t : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * (2 * Real.pi * Complex.I) ^ (j + 1) *
        Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) := by
  rw [iteratedDeriv_succ']
  have hd : deriv (psi k) = deriv (fun t : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ))) := by
    unfold psi; exact deriv_sub_const_fun _
  rw [hd, ← iteratedDeriv_succ', GlobalTheory.LinPhaseSeminorm.iteratedDeriv_const_mul_cexp]

theorem norm_iteratedDeriv_psi_succ (k : ℝ) (j : ℕ) (t : ℝ) :
    ‖iteratedDeriv (j + 1) (psi k) t‖ = (2 * Real.pi) ^ (j + 1) := by
  rw [iteratedDeriv_psi_succ]
  have h1 : ∀ r : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := by
    intro r
    rw [show (2 * Real.pi * Complex.I * (r : ℂ)) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  simp only [norm_mul, norm_pow, h1]
  simp [abs_of_pos Real.pi_pos]

theorem norm_iteratedFDeriv_psi_comp_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) {N i : ℕ} (hi : i ≤ N) (x : V) :
    ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ ≤
      (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * (1 + ‖x‖) := by
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hL := norm_nonneg L
  have hx := norm_nonneg x
  have hk := abs_nonneg k
  have h1N : (1 : ℝ) ≤ (1 + ‖L‖) ^ N := one_le_pow₀ (by linarith)
  rcases i with _ | j
  · rw [norm_iteratedFDeriv_zero, Function.comp_apply]
    refine (norm_psi_le k (L x)).trans ?_
    have h2 : |L x + k| ≤ (‖L‖ + |k|) * (1 + ‖x‖) := by
      have h3 : |L x| ≤ ‖L‖ * ‖x‖ := by simpa [Real.norm_eq_abs] using L.le_opNorm x
      calc |L x + k| ≤ |L x| + |k| := abs_add_le _ _
        _ ≤ ‖L‖ * ‖x‖ + |k| := by linarith
        _ ≤ (‖L‖ + |k|) * (1 + ‖x‖) := by nlinarith
    have h4 : 2 * Real.pi ≤ (2 * Real.pi) ^ (N + 1) := le_self_pow₀ hpi (by omega)
    calc 2 * Real.pi * |L x + k| ≤ 2 * Real.pi * ((‖L‖ + |k|) * (1 + ‖x‖)) := by gcongr
      _ ≤ (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * 1) * (1 + ‖x‖) := by
          rw [mul_one]; rw [← mul_assoc]; gcongr
      _ ≤ _ := by gcongr
  · rw [L.iteratedFDeriv_comp_right (contDiff_psi k) x (i := j + 1) (by exact_mod_cast le_top)]
    have h5 : (2 * Real.pi) ^ (j + 1) ≤ (2 * Real.pi) ^ (N + 1) := pow_le_pow_right₀ hpi (by omega)
    have h6 : ‖L‖ ^ (j + 1) ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ N := by
      rw [pow_succ']
      gcongr
      · linarith
      · calc ‖L‖ ^ j ≤ (1 + ‖L‖) ^ j := by gcongr; linarith
          _ ≤ (1 + ‖L‖) ^ N := pow_le_pow_right₀ (by linarith) (by omega)
    calc _ ≤ ‖iteratedFDeriv ℝ (j + 1) (psi k) (L x)‖ * ∏ _j : Fin (j + 1), ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = (2 * Real.pi) ^ (j + 1) * ‖L‖ ^ (j + 1) := by
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedDeriv_psi_succ]; simp
      _ ≤ (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * 1 := by
          rw [mul_one]; gcongr
      _ ≤ _ := by gcongr; linarith

theorem hasTemperateGrowth_phase {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) : Function.HasTemperateGrowth (fun y => eChar (L y + k)) :=
  hasTemperateGrowth_eChar.comp (L.hasTemperateGrowth.add (Function.HasTemperateGrowth.const _))

theorem coe_smulLeft_sub {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) (f : 𝓢(V, ℂ)) :
    ⇑(SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k)) f - f) = fun y => (psi k ∘ ⇑L) y * f y := by
  funext y
  rw [SchwartzMap.sub_apply, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase L k), smul_eq_mul,
    ← congrFun (eChar_sub_one_eq L k) y]
  ring

theorem seminorm_smulLeft_sub_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A N a n : ℕ} (ha : a ≤ A) (hn : n ≤ N) (L : V →L[ℝ] ℝ) (k : ℝ) (f : 𝓢(V, ℂ)) :
    SchwartzMap.seminorm ℂ a n (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k)) f - f) ≤
      ((N + 1) * 2 ^ N * (2 * Real.pi) ^ (N + 1) * 2 ^ (A + 1)) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) *
        (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f := by
  set S := (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f with hS
  set P := (‖L‖ + |k|) * (1 + ‖L‖) ^ N with hP
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hP0 : 0 ≤ P := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ a n _ (by positivity) fun x => ?_
  rw [coe_smulLeft_sub]
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    ((contDiff_psi k).comp L.contDiff) (f.smooth ⊤) x (n := n) (by exact_mod_cast le_top)
  have hx := norm_nonneg x
  have hf : ∀ j ≤ N, ‖x‖ ^ a * (1 + ‖x‖) * ‖iteratedFDeriv ℝ j f x‖ ≤ 2 ^ (A + 1) * S := by
    intro j hj
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (A + 1, N)) (k := a + 1) (n := j)
      (by simp; omega) hj f x
    have h' : ‖x‖ ^ a * (1 + ‖x‖) ≤ (1 + ‖x‖) ^ (a + 1) := by
      rw [pow_succ]; gcongr; linarith
    calc _ ≤ (1 + ‖x‖) ^ (a + 1) * ‖iteratedFDeriv ℝ j f x‖ := by gcongr
      _ ≤ _ := h
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ a * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ *
        ‖iteratedFDeriv ℝ (n - i) f x‖) ≤ 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := norm_iteratedFDeriv_psi_comp_le L k (N := N) (i := i) (by omega) x
    have h2 := hf (n - i) (by omega)
    have hc : (n.choose i : ℝ) ≤ 2 ^ N :=
      (by exact_mod_cast Nat.choose_le_two_pow n i : (n.choose i : ℝ) ≤ 2 ^ n).trans
        (pow_le_pow_right₀ (by norm_num) hn)
    calc ‖x‖ ^ a * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖)
        ≤ ‖x‖ ^ a * ((2 ^ N : ℝ) * ((2 * Real.pi) ^ (N + 1) * P * (1 + ‖x‖)) *
          ‖iteratedFDeriv ℝ (n - i) f x‖) := by gcongr
      _ = 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) *
          (‖x‖ ^ a * (1 + ‖x‖) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
      _ ≤ _ := by gcongr
  calc ‖x‖ ^ a * ‖iteratedFDeriv ℝ n (fun y => (psi k ∘ ⇑L) y * f y) x‖
      ≤ ‖x‖ ^ a * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
        gcongr
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ a * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ Finset.range (n + 1), 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S) :=
        Finset.sum_le_sum hterm
    _ = ((n : ℝ) + 1) * (2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S)) := by simp
    _ ≤ ((N : ℝ) + 1) * (2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S)) := by
        gcongr
    _ = _ := by ring

theorem continuous_finset_sup_seminorm {E ι : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {p : ι → Seminorm ℂ E} (hp : ∀ i, Continuous (p i)) (s : Finset ι) :
    Continuous ⇑(s.sup p : Seminorm ℂ E) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    exact continuous_const
  | insert i s _ ih =>
    rw [Finset.sup_insert]
    exact ((hp i).max ih).congr fun x => (Seminorm.sup_apply _ _ _).symm

theorem seminorm_smulLeft_eChar_sub_le : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : Seminorm ℂ (SchwartzMap V ℂ)), Continuous p →
    ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (L : V →L[ℝ] ℝ) (k : ℝ) (f : SchwartzMap V ℂ),
      p (SchwartzMap.smulLeftCLM ℂ (fun y => GlobalTheory.Published.Metaplectic.eChar (L y + k)) f - f) ≤
        (‖L‖ + |k|) * (1 + ‖L‖) ^ M * q f := by
  intro V _ _ p hp
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) p hp
  set A := s.sup Prod.fst with hA
  set N := s.sup Prod.snd with hN
  set K : ℝ := (N + 1) * 2 ^ N * (2 * Real.pi) ^ (N + 1) * 2 ^ (A + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  set Q : Seminorm ℂ (SchwartzMap V ℂ) :=
    (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) with hQ
  refine ⟨(C * ⟨K, hK0⟩ : NNReal) • Q, N, ?_, ?_⟩
  · exact (continuous_finset_sup_seminorm
      (fun i => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i) _).const_smul _
  · intro L k f
    set g := SchwartzMap.smulLeftCLM ℂ (fun y => GlobalTheory.Published.Metaplectic.eChar (L y + k)) f - f
    have hP0 : 0 ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ N := by positivity
    have hQ0 : 0 ≤ Q f := apply_nonneg _ _
    have hs : (s.sup (schwartzSeminormFamily ℂ V ℂ)) g ≤ K * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * Q f := by
      refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
      exact seminorm_smulLeft_sub_le (Finset.le_sup (f := Prod.fst) hi) (Finset.le_sup (f := Prod.snd) hi) L k f
    calc p g ≤ (C • s.sup (schwartzSeminormFamily ℂ V ℂ)) g := hC g
      _ = (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) g := by
          rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
      _ ≤ (C : ℝ) * (K * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * Q f) := by gcongr
      _ = (‖L‖ + |k|) * (1 + ‖L‖) ^ N * (((C * ⟨K, hK0⟩ : NNReal) • Q) f) := by
          rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
          change (C : ℝ) * _ = _ * (((C : ℝ) * K) * Q f)
          ring

end GlobalTheory.PhaseLipschitz
end
end

section
section
open MeasureTheory GlobalTheory.RealWeil Filter Topology
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

namespace GlobalTheory.RealWeil.SchrFamily

variable {l : Type} [Fintype l]

def pCLM (l : Type) [Fintype l] : (l ⊕ l → ℝ) →L[ℝ] EuclideanSpace ℝ l :=
  LinearMap.toContinuousLinearMap { toFun := pPart, map_add' := pPart_add, map_smul' := pPart_smul }

def qCLM (l : Type) [Fintype l] : (l ⊕ l → ℝ) →L[ℝ] EuclideanSpace ℝ l :=
  LinearMap.toContinuousLinearMap { toFun := qPart, map_add' := qPart_add, map_smul' := qPart_smul }

theorem rhoSch_eq (w : l ⊕ l → ℝ) (g : Sch l) :
    rhoSch w g = SchwartzMap.smulLeftCLM ℂ
      (fun y => GlobalTheory.Published.Metaplectic.eChar (innerSL ℝ (qPart w) y + ⟪pPart w, qPart w⟫ / 2))
      (SchwartzMap.compSubConstCLM ℂ (-pPart w) g) := by
  ext x
  rw [coe_rhoSch, SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.PhaseLipschitz.hasTemperateGrowth_phase _ _),
    SchwartzMap.compSubConstCLM_apply, smul_eq_mul, rhoFun, phase_eq_eChar, sub_neg_eq_add]
  simp

theorem seminorm_rhoSch_sub_le (p : Seminorm ℂ (Sch l)) (hp : Continuous p) :
    ∃ (q₁ q₂ q₃ : Seminorm ℂ (Sch l)) (M₁ M₂ M₃ : ℕ), ∀ (w : l ⊕ l → ℝ) (g : Sch l),
      p (rhoSch w g - g) ≤ (‖qPart w‖ + |⟪pPart w, qPart w⟫ / 2|) * (1 + ‖qPart w‖) ^ M₁ *
          (‖pPart w‖ * (1 + ‖pPart w‖) ^ M₃ * q₃ g + q₁ g) + ‖pPart w‖ * (1 + ‖pPart w‖) ^ M₂ * q₂ g := by
  obtain ⟨q₁, M₁, hq₁, hb₁⟩ := GlobalTheory.PhaseLipschitz.seminorm_smulLeft_eChar_sub_le (EuclideanSpace ℝ l) p hp
  obtain ⟨q₂, M₂, -, hb₂⟩ := GlobalTheory.SchwartzTranslateLip.translate_sub_le (EuclideanSpace ℝ l) p hp
  obtain ⟨q₃, M₃, -, hb₃⟩ := GlobalTheory.SchwartzTranslateLip.translate_sub_le (EuclideanSpace ℝ l) q₁ hq₁
  refine ⟨q₁, q₂, q₃, M₁, M₂, M₃, fun w g => ?_⟩
  set T := SchwartzMap.compSubConstCLM ℂ (-pPart w) g with hT
  have hL : ‖innerSL ℝ (qPart w)‖ = ‖qPart w‖ := innerSL_apply_norm _ _
  have h1 := map_add_le_add p (SchwartzMap.smulLeftCLM ℂ
    (fun y => GlobalTheory.Published.Metaplectic.eChar (innerSL ℝ (qPart w) y + ⟪pPart w, qPart w⟫ / 2)) T - T) (T - g)
  rw [sub_add_sub_cancel] at h1
  rw [rhoSch_eq]
  refine le_trans h1 (add_le_add ((hb₁ _ _ T).trans ?_) (hb₂ _ g))
  rw [hL]
  have h2 := map_add_le_add q₁ (T - g) g
  rw [sub_add_cancel] at h2
  have h3 := hb₃ (pPart w) g
  gcongr
  linarith

theorem tendsto_rhoSch_zero (g : Sch l) : Tendsto (fun u => rhoSch u g) (𝓝 0) (𝓝 g) := by
  rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).tendsto_nhds _ g]
  intro i ε hε
  obtain ⟨q₁, q₂, q₃, M₁, M₂, M₃, hb⟩ := seminorm_rhoSch_sub_le (schwartzSeminormFamily ℂ _ ℂ i)
    ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).continuous_seminorm i)
  have hpc : Tendsto (fun u : l ⊕ l → ℝ => pPart u) (𝓝 0) (𝓝 0) := by
    have := (pCLM l).continuous.tendsto 0
    rw [map_zero] at this
    exact this
  have hqc : Tendsto (fun u : l ⊕ l → ℝ => qPart u) (𝓝 0) (𝓝 0) := by
    have := (qCLM l).continuous.tendsto 0
    rw [map_zero] at this
    exact this
  have hpn : Tendsto (fun u : l ⊕ l → ℝ => ‖pPart u‖) (𝓝 0) (𝓝 0) := by simpa using hpc.norm
  have hqn : Tendsto (fun u : l ⊕ l → ℝ => ‖qPart u‖) (𝓝 0) (𝓝 0) := by simpa using hqc.norm
  have hk : Tendsto (fun u : l ⊕ l → ℝ => |⟪pPart u, qPart u⟫ / 2|) (𝓝 0) (𝓝 0) := by
    have := ((hpc.inner (𝕜 := ℝ) hqc).div_const 2).abs
    simpa using this
  have lim : Tendsto (fun u : l ⊕ l → ℝ => (‖qPart u‖ + |⟪pPart u, qPart u⟫ / 2|) * (1 + ‖qPart u‖) ^ M₁ *
          (‖pPart u‖ * (1 + ‖pPart u‖) ^ M₃ * q₃ g + q₁ g) + ‖pPart u‖ * (1 + ‖pPart u‖) ^ M₂ * q₂ g)
      (𝓝 0) (𝓝 0) := by
    have := (((hqn.add hk).mul ((hqn.const_add 1).pow M₁)).mul
      (((hpn.mul ((hpn.const_add 1).pow M₃)).mul_const (q₃ g)).add_const (q₁ g))).add
      ((hpn.mul ((hpn.const_add 1).pow M₂)).mul_const (q₂ g))
    simpa using this
  filter_upwards [lim.eventually (gt_mem_nhds hε)] with u hu
  exact (hb u g).trans_lt hu

theorem rhoSch_rhoSch (w₀ u : l ⊕ l → ℝ) (g : Sch l) :
    rhoSch w₀ (rhoSch u g) = Complex.exp (((Real.pi * sympl w₀ u : ℝ) : ℂ) * Complex.I) • rhoSch (w₀ + u) g := by
  ext x
  rw [coe_rhoSch, coe_rhoSch, rhoFun_rhoFun, SchwartzMap.smul_apply, coe_rhoSch]
  rfl

theorem continuous_rhoSch (g : Sch l) : Continuous fun w => rhoSch w g := by
  refine continuous_iff_continuousAt.2 fun w₀ => ?_
  set c : (l ⊕ l → ℝ) → ℂ := fun u => Complex.exp (((Real.pi * sympl w₀ u : ℝ) : ℂ) * Complex.I) with hcdef
  have hs : Continuous fun u : l ⊕ l → ℝ => sympl w₀ u := by
    have e : (fun u : l ⊕ l → ℝ => sympl w₀ u) =
        fun u => ⟪pPart w₀, qCLM l u⟫ - ⟪qPart w₀, pCLM l u⟫ := rfl
    rw [e]
    exact (continuous_const.inner (qCLM l).continuous).sub (continuous_const.inner (pCLM l).continuous)
  have hc : Continuous c := by
    rw [hcdef]
    fun_prop
  have h1 : Tendsto (fun u => (c u)⁻¹ • rhoSch w₀ (rhoSch u g)) (𝓝 0) (𝓝 ((c 0)⁻¹ • rhoSch w₀ g)) :=
    ((hc.tendsto 0).inv₀ (Complex.exp_ne_zero _)).smul
      (((rhoSch w₀).continuous.tendsto g).comp (tendsto_rhoSch_zero g))
  have hq0 : qPart (0 : l ⊕ l → ℝ) = 0 := rfl
  have hp0 : pPart (0 : l ⊕ l → ℝ) = 0 := rfl
  have hc0 : c 0 = 1 := by simp [hcdef, sympl, hq0, hp0]
  have e : ∀ u, (c u)⁻¹ • rhoSch w₀ (rhoSch u g) = rhoSch (w₀ + u) g := fun u => by
    rw [rhoSch_rhoSch, inv_smul_smul₀ (Complex.exp_ne_zero _)]
  simp only [e, hc0, inv_one, one_smul] at h1
  have h3 : Tendsto (fun w => w - w₀) (𝓝 w₀) (𝓝 0) := (continuous_sub_right w₀).tendsto' _ _ (sub_self _)
  refine (h1.comp h3).congr fun w => ?_
  simp

theorem seminorm_rhoSch_le (g : Sch l) (k m : ℕ) :
    ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (rhoSch w g) ≤ C * (1 + ‖w‖) ^ N := by
  obtain ⟨q₁, q₂, q₃, M₁, M₂, M₃, hb⟩ := seminorm_rhoSch_sub_le (SchwartzMap.seminorm ℂ k m)
    ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).continuous_seminorm (k, m))
  set p := SchwartzMap.seminorm ℂ k m (E := EuclideanSpace ℝ l) (F := ℂ) with hpdef
  set c := ‖pCLM l‖ + ‖qCLM l‖ with hcdef
  set N := 3 + M₁ + M₂ + M₃ with hN
  have hq1 : 0 ≤ q₁ g := apply_nonneg _ _
  have hq2 : 0 ≤ q₂ g := apply_nonneg _ _
  have hq3 : 0 ≤ q₃ g := apply_nonneg _ _
  have hp : 0 ≤ p g := apply_nonneg _ _
  refine ⟨(1 + c) ^ N * (2 * q₃ g + 2 * q₁ g + q₂ g + p g), N, fun w => ?_⟩
  have hc : 0 ≤ c := by positivity
  have hw := norm_nonneg w
  set X := (1 + c) * (1 + ‖w‖) with hX
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have hpw : ‖pPart w‖ ≤ ‖pCLM l‖ * ‖w‖ := (pCLM l).le_opNorm w
  have hqw : ‖qPart w‖ ≤ ‖qCLM l‖ * ‖w‖ := (qCLM l).le_opNorm w
  have hpn := norm_nonneg (pCLM l)
  have hqn := norm_nonneg (qCLM l)
  have ha : 1 + ‖pPart w‖ ≤ X := by rw [hX]; nlinarith
  have hb' : 1 + ‖qPart w‖ ≤ X := by rw [hX]; nlinarith
  have ha' : ‖pPart w‖ ≤ X := by linarith
  have hb'' : ‖qPart w‖ ≤ X := by linarith
  have hk : ‖qPart w‖ + |⟪pPart w, qPart w⟫ / 2| ≤ 2 * X ^ 2 := by
    have h1 : |⟪pPart w, qPart w⟫| ≤ ‖pPart w‖ * ‖qPart w‖ := abs_real_inner_le_norm _ _
    have h2 : ‖pPart w‖ * ‖qPart w‖ ≤ X * X := mul_le_mul ha' hb'' (norm_nonneg _) (by linarith)
    rw [abs_div, abs_two]
    nlinarith
  have hsub : p (rhoSch w g) ≤ p (rhoSch w g - g) + p g := by
    simpa using map_add_le_add p (rhoSch w g - g) g
  calc p (rhoSch w g) ≤ p (rhoSch w g - g) + p g := hsub
    _ ≤ (2 * X ^ 2) * X ^ M₁ * (X * X ^ M₃ * q₃ g + q₁ g) + X * X ^ M₂ * q₂ g + p g := by
        refine add_le_add ((hb w g).trans ?_) le_rfl
        gcongr
    _ = 2 * X ^ (3 + M₁ + M₃) * q₃ g + 2 * X ^ (2 + M₁) * q₁ g + X ^ (1 + M₂) * q₂ g + 1 * p g := by ring
    _ ≤ 2 * X ^ N * q₃ g + 2 * X ^ N * q₁ g + X ^ N * q₂ g + X ^ N * p g := by
        have e1 : X ^ (3 + M₁ + M₃) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e2 : X ^ (2 + M₁) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e3 : X ^ (1 + M₂) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e4 : (1 : ℝ) ≤ X ^ N := one_le_pow₀ hX1
        have f1 := mul_le_mul_of_nonneg_right e1 hq3
        have f2 := mul_le_mul_of_nonneg_right e2 hq1
        have f3 := mul_le_mul_of_nonneg_right e3 hq2
        have f4 := mul_le_mul_of_nonneg_right e4 hp
        nlinarith
    _ = (1 + c) ^ N * (2 * q₃ g + 2 * q₁ g + q₂ g + p g) * (1 + ‖w‖) ^ N := by
        rw [hX, mul_pow]; ring

theorem exists_continuous_schwartz_rhoFun : ∀ (n : ℕ) (f : Sch (Fin n)), ∃ G : (Fin n ⊕ Fin n → ℝ) → Sch (Fin n),
    Continuous G ∧ (∀ w, ⇑(G w) = rhoFun w ⇑f) ∧
    ∀ k m : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (G w) ≤ C * (1 + ‖w‖) ^ N :=
  fun _ f => ⟨fun w => rhoSch w f, continuous_rhoSch f, fun w => coe_rhoSch w f, seminorm_rhoSch_le f⟩

end GlobalTheory.RealWeil.SchrFamily
end
end

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_rep_schwartz_polynomial_bound : ∀ (n : ℕ) (f : Sch (Fin n)), ∃ G : (Fin n ⊕ Fin n → ℝ) → Sch (Fin n), Continuous G ∧
    (∀ w, ⇑(G w) = rhoFun w ⇑f) ∧
    ∀ k m : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (G w) ≤ C * (1 + ‖w‖) ^ N := by
  atlas_forward_decl GlobalTheory.RealWeil.SchrFamily.exists_continuous_schwartz_rhoFun
end

section
section
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

noncomputable section

namespace GlobalTheory.MoyalPointwise

variable {l : Type} [Fintype l]

def ambU (g g' : Sch l) (p : EuclideanSpace ℝ l) : Sch l :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) g'.hasTemperateGrowth
    (SchwartzMap.compSubConstCLM ℂ (-p) (GlobalTheory.ConjSch.conjSch g))

theorem ambU_apply (g g' : Sch l) (p t : EuclideanSpace ℝ l) :
    ambU g g' p t = starRingEnd ℂ (g (t + p)) * g' t := by
  simp [ambU, SchwartzMap.bilinLeftCLM_apply, GlobalTheory.ConjSch.conjSch_apply, sub_neg_eq_add]

end GlobalTheory.MoyalPointwise

noncomputable section

namespace GlobalTheory.MoyalPointwise

open Complex
open scoped Real RealInnerProductSpace FourierTransform

variable {l : Type} [Fintype l]

theorem integrand_eq (g g' f : Sch l) (x : EuclideanSpace ℝ l) (w : l ⊕ l → ℝ) :
    starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * rhoFun w ⇑f x =
      cexp (((2 * π * ⟪qPart w, x⟫ : ℝ) : ℂ) * I) * 𝓕 (ambU g g' (pPart w)) (qPart w) * f (x + pPart w) := by
  have h1 : ∀ t, starRingEnd ℂ (rhoFun w ⇑g t * starRingEnd ℂ (g' t)) =
      cexp (((-π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I) *
        (cexp (((-2 * π * ⟪t, qPart w⟫ : ℝ) : ℂ) * I) • ambU g g' (pPart w) t) := by
    intro t
    rw [ambU_apply, smul_eq_mul, rhoFun, phase, map_mul, map_mul, Complex.conj_conj, ← Complex.exp_conj,
      map_mul, Complex.conj_ofReal, Complex.conj_I]
    have e : cexp (((2 * π * ⟪qPart w, t⟫ + π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * -I) =
        cexp (((-π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I) * cexp (((-2 * π * ⟪t, qPart w⟫ : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add, real_inner_comm t (qPart w)]
      congr 1
      push_cast
      ring
    rw [e]
    ring
  have h2 : 𝓕 (ambU g g' (pPart w)) (qPart w) =
      ∫ t, cexp (((-2 * π * ⟪t, qPart w⟫ : ℝ) : ℂ) * I) • ambU g g' (pPart w) t := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  have h3 : starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) =
      cexp (((-π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I) * 𝓕 (ambU g g' (pPart w)) (qPart w) := by
    rw [← integral_conj, integral_congr_ae (Filter.Eventually.of_forall h1), integral_const_mul, h2]
  have key : cexp (((-π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I) *
      cexp (((2 * π * ⟪qPart w, x⟫ + π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I) =
      cexp (((2 * π * ⟪qPart w, x⟫ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h3, rhoFun, phase]
  linear_combination (𝓕 (ambU g g' (pPart w)) (qPart w) * f (x + pPart w)) * key

theorem measurePreserving_pq :
    MeasurePreserving (fun w : l ⊕ l → ℝ => (pPart w, qPart w)) volume volume ∧
      MeasurableEmbedding (fun w : l ⊕ l → ℝ => (pPart w, qPart w)) := by
  let e : (l ⊕ l → ℝ) ≃ᵐ EuclideanSpace ℝ l × EuclideanSpace ℝ l :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : l ⊕ l => ℝ)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (l → ℝ)) (MeasurableEquiv.toLp 2 (l → ℝ)))
  have he : ⇑e = fun w : l ⊕ l → ℝ => (pPart w, qPart w) := rfl
  rw [← he]
  refine ⟨?_, e.measurableEmbedding⟩
  exact ((PiLp.volume_preserving_toLp l).prod (PiLp.volume_preserving_toLp l)).comp
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : l ⊕ l => ℝ))

theorem integral_phase_fourier (u : Sch l) (x : EuclideanSpace ℝ l) :
    ∫ q, cexp (((2 * π * ⟪q, x⟫ : ℝ) : ℂ) * I) * 𝓕 u q = u x := by
  have h := congrFun (u.continuous.fourierInv_fourier_eq u.integrable (𝓕 u).integrable) x
  rw [Real.fourierInv_eq'] at h
  simpa [SchwartzMap.fourier_coe] using h

theorem moyal_pointwise : ∀ (n : ℕ) (f g g' : Sch (Fin n)) (x : EuclideanSpace ℝ (Fin n)),
    ∫ w : Fin n ⊕ Fin n → ℝ, starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * rhoFun w ⇑f x =
      (∫ t, f t * starRingEnd ℂ (g t)) * g' x := by
  intro n f g g' x
  obtain ⟨hmp, hme⟩ := measurePreserving_pq (l := Fin n)
  set G : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℂ := fun z =>
    cexp (((2 * π * ⟪z.2, x⟫ : ℝ) : ℂ) * I) * 𝓕 (ambU g g' z.1) z.2 * f (x + z.1) with hG
  have hI : (fun w : Fin n ⊕ Fin n → ℝ =>
      starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * rhoFun w ⇑f x) =
      G ∘ fun w => (pPart w, qPart w) := by
    funext w
    exact integrand_eq g g' f x w
  have hint : Integrable (fun w : Fin n ⊕ Fin n → ℝ =>
      starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * rhoFun w ⇑f x) := by
    obtain ⟨hc, hd⟩ := GlobalTheory.T.matrix_coeff_continuous_rapid_decay n g g'
    obtain ⟨C, hC⟩ := hd (2 * n + 1)
    have hr : (Module.finrank ℝ (Fin n ⊕ Fin n → ℝ) : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      push_cast
      linarith
    have hB := (integrable_one_add_norm (E := Fin n ⊕ Fin n → ℝ) (μ := volume) hr).const_mul
      (C * SchwartzMap.seminorm ℂ 0 0 f)
    have hp : Continuous (fun w : Fin n ⊕ Fin n → ℝ => pPart w) := by
      unfold pPart; fun_prop
    have hq : Continuous (fun w : Fin n ⊕ Fin n → ℝ => qPart w) := by
      unfold qPart; fun_prop
    have hcont : Continuous (fun w : Fin n ⊕ Fin n → ℝ => rhoFun w ⇑f x) := by
      simp only [rhoFun, phase]
      have := f.continuous
      fun_prop
    refine hB.mono' (((Complex.continuous_conj.comp hc).mul hcont).aestronglyMeasurable)
      (.of_forall fun w => ?_)
    have hpos : 0 < 1 + ‖w‖ := by positivity
    have e1 : ‖∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)‖ ≤ C * (1 + ‖w‖) ^ (-((2 * n + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg hpos.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hpos _)]
      exact hC w
    have e2 : ‖f (x + pPart w)‖ ≤ SchwartzMap.seminorm ℂ 0 0 f := SchwartzMap.norm_le_seminorm ℂ f _
    simp only [Function.comp_apply, norm_mul, RCLike.norm_conj, rhoFun, norm_phase, one_mul]
    calc _ ≤ C * (1 + ‖w‖) ^ (-((2 * n + 1 : ℕ) : ℝ)) * SchwartzMap.seminorm ℂ 0 0 f :=
          mul_le_mul e1 e2 (norm_nonneg _) (le_trans (norm_nonneg _) e1)
      _ = _ := by ring
  have hGint : Integrable G := (hmp.integrable_comp_emb hme).1 (hI ▸ hint)
  calc _ = ∫ w : Fin n ⊕ Fin n → ℝ, G (pPart w, qPart w) := by rw [hI]; rfl
    _ = ∫ z, G z := hmp.integral_comp hme G
    _ = ∫ p, ∫ q, G (p, q) := integral_prod G hGint
    _ = ∫ p, starRingEnd ℂ (g (x + p)) * g' x * f (x + p) := by
        congr 1
        funext p
        simp only [hG]
        rw [integral_mul_const, integral_phase_fourier, ambU_apply]
    _ = ∫ p, (fun y => f y * starRingEnd ℂ (g y)) (x + p) * g' x := by
        congr 1
        funext p
        ring
    _ = _ := by
        rw [integral_mul_const]
        exact congrArg (· * g' x) (integral_add_left_eq_self (fun y => f y * starRingEnd ℂ (g y)) x)

end GlobalTheory.MoyalPointwise
end
end
end

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_orthogonality_relation : ∀ (n : ℕ) (f g g' : Sch (Fin n)) (x : EuclideanSpace ℝ (Fin n)),
    ∫ w : Fin n ⊕ Fin n → ℝ, starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * rhoFun w ⇑f x =
      (∫ t, f t * starRingEnd ℂ (g t)) * g' x := by
  atlas_forward_decl GlobalTheory.MoyalPointwise.moyal_pointwise
end

section
section
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory

theorem gaussian_selfPairing_pos (n : ℕ) :
    ∃ r : ℝ, 0 < r ∧ (∫ x, GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin n)) x *
      starRingEnd ℂ (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin n)) x)) = (r : ℂ) := by
  refine ⟨∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2), ?_, ?_⟩
  · rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
    have : 0 < Real.pi / (2 * Real.pi) := by positivity
    positivity
  · rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [GroundTheory.Global.gaussianSchwartz_apply, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring

theorem hermitian_form_eq_smul_l2 : ∀ (n : ℕ) (B : Sch (Fin n) → Sch (Fin n) → ℂ), (∀ h h', B h' h = starRingEnd ℂ (B h h')) →
    (∀ h, 0 ≤ (B h h).re) →
    (∀ f f' g g' : Sch (Fin n), (∫ x, f x * starRingEnd ℂ (g x)) * B g' f' = (∫ x, g' x * starRingEnd ℂ (f' x)) * B f g) →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x) := by
  intro n B hherm hpos hid
  set h₀ : Sch (Fin n) := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin n)) with hh₀
  obtain ⟨r, hr, hs⟩ := gaussian_selfPairing_pos n
  have hb : B h₀ h₀ = ((B h₀ h₀).re : ℂ) := by
    have := hherm h₀ h₀
    apply Complex.ext
    · simp
    · have h2 : (B h₀ h₀).im = -(B h₀ h₀).im := by
        conv_lhs => rw [this]
        simp
      simp; linarith
  refine ⟨(B h₀ h₀).re / r, div_nonneg (hpos h₀) hr.le, fun h h' => ?_⟩
  have key := hid h₀ h' h₀ h
  rw [hs, hb] at key
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp
  linear_combination key

end GlobalTheory
end

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_const_mul_inner : ∀ (n : ℕ) (B : Sch (Fin n) → Sch (Fin n) → ℂ), (∀ h h', B h' h = starRingEnd ℂ (B h h')) →
    (∀ h, 0 ≤ (B h h).re) →
    (∀ f f' g g' : Sch (Fin n), (∫ x, f x * starRingEnd ℂ (g x)) * B g' f' = (∫ x, g' x * starRingEnd ℂ (f' x)) * B f g) →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x) := by
  atlas_forward_decl GlobalTheory.hermitian_form_eq_smul_l2
end

section
section
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory.RealWeil

theorem integral_rhoFun_mul_conj (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n) → ℂ) :
    ∫ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) = ∫ x, u x * starRingEnd ℂ (v x) := by
  have h : ∀ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) =
      u (x + pPart w) * starRingEnd ℂ (v (x + pPart w)) := by
    intro x
    have hp : phase w x * starRingEnd ℂ (phase w x) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]
      simp
    simp only [rhoFun, map_mul]
    calc _ = (phase w x * starRingEnd ℂ (phase w x)) * (u (x + pPart w) * starRingEnd ℂ (v (x + pPart w))) := by
          ring
      _ = _ := by rw [hp, one_mul]
  simp_rw [h]
  exact integral_add_right_eq_self (fun x => u x * starRingEnd ℂ (v x)) (pPart w)

end GlobalTheory.RealWeil
end

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_rep_unitary : ∀ (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n) → ℂ),
    ∫ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) = ∫ x, u x * starRingEnd ℂ (v x) := by
  atlas_forward_decl GlobalTheory.RealWeil.integral_rhoFun_mul_conj
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ArchUniq.FormTransport

open GlobalTheory.RealWeil GlobalTheory.ArchUniq
open scoped SchwartzMap ComplexConjugate

theorem rhoFun_mul_conj {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) (G G' : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) :
    rhoFun w G x * conj (rhoFun w G' x) = G (x + pPart w) * conj (G' (x + pPart w)) := by
  have h : phase w x * conj (phase w x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]; simp
  simp only [rhoFun, map_mul]
  calc _ = (phase w x * conj (phase w x)) * (G (x + pPart w) * conj (G' (x + pPart w))) := by ring
    _ = _ := by rw [h, one_mul]

theorem integral_rhoFun_mul_conj {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) (G G' : EuclideanSpace ℝ (Fin n) → ℂ) :
    ∫ x, rhoFun w G x * conj (rhoFun w G' x) = ∫ x, G x * conj (G' x) := by
  simp_rw [rhoFun_mul_conj]
  exact integral_add_right_eq_self (fun x => G x * conj (G' x)) (pPart w)

open scoped Classical in

theorem schr_eq_schrF {F : Type} [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)]
    {κ : Type} [Fintype κ] (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ)
    (hψ : ∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ)))
    (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (u : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    schr ψ w u = schrF (trP F κ) w u := by
  funext x
  have h2 : (⅟(2 : mixedEmbedding.mixedSpace F)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2, ← map_mul]
    norm_num
  have ht : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ w.2 + ⅟(2 : mixedEmbedding.mixedSpace F) * (w.1 ⬝ᵥ w.2)) =
      trP F κ x w.2 + trP F κ w.1 w.2 / 2 := by
    rw [map_add, h2, ← Algebra.smul_def, map_smul, smul_eq_mul]
    simp only [trP, dotProduct]
    ring
  simp only [schr, schrF, hψ, ht]

theorem haar_coords_cplx {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ k : ℝ, ∀ G : V → ℂ, ∫ y, G y ∂μ = (k : ℂ) * ∫ x, G (C.symm x) := by
  let e : V ≃ᵐ EuclideanSpace ℝ (Fin n) := C.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = C y := fun y => rfl
  haveI : (μ.map e).IsAddHaarMeasure := C.isAddHaarMeasure_map μ
  have hk := Measure.isAddLeftInvariant_eq_smul (μ.map e) (volume : Measure (EuclideanSpace ℝ (Fin n)))
  refine ⟨(Measure.addHaarScalarFactor (μ.map e) volume : ℝ), fun G => ?_⟩
  have h1 : ∫ y, G y ∂μ = ∫ x, G (C.symm x) ∂(μ.map e) := by
    rw [integral_map_equiv]
    simp [he]
  rw [h1, congrArg (fun m => ∫ x, G (C.symm x) ∂m) hk]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

open scoped Classical in

theorem const_of_euclidean : (∀ (n : ℕ) (B : GlobalTheory.RealWeil.Sch (Fin n) → GlobalTheory.RealWeil.Sch (Fin n) → ℂ),
    (∀ h', ∃ L : GlobalTheory.RealWeil.Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h) →
    (∀ h h', B h' h = starRingEnd ℂ (B h h')) → (∀ h, 0 ≤ (B h h).re) →
    (∀ (w : Fin n ⊕ Fin n → ℝ) (h h' g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑h' → B g g' = B h h') →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x)) → ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
  intro H F _ _ _ κ _ ψ hψ T A hT
  letI : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  have hP : IsPairing (trP F κ) := Coord.isPairing_trP κ
  obtain ⟨C, φ, -, hS⟩ := exists_pairing_coords (κ → mixedEmbedding.mixedSpace F) (trP F κ) hP _ rfl
  generalize Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F) = n at C φ hS
  let toE : SInf F κ →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let toV : Sch (Fin n) →L[ℂ] SInf F κ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑C.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑C := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  let T' : Sch (Fin n) →L[ℂ] Sch (Fin n) := toE.comp (T.comp toV)
  have hT' : ∀ h, T' h = toE (T (toV h)) := fun h => rfl
  have hI : ∀ w (h g : Sch (Fin n)), ⇑g = rhoFun w ⇑h → ⇑(T' g) = rhoFun (φ (A (φ.symm w))) ⇑(T' h) := by
    intro w h g hg
    have e1 : ⇑(toV g) = schr ψ (φ.symm w) ⇑(toV h) := by
      rw [schr_eq_schrF ψ hψ]
      funext x
      have := congrFun (hS (φ.symm w) ⇑h) x
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply] at this
      simp only [htoV, Function.comp_apply, hg]
      exact this.symm
    have e2 := hT _ _ _ e1
    rw [schr_eq_schrF ψ hψ] at e2
    rw [hT', hT', htoE, htoE, e2]
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin n) → ℂ, ⇑(T (toV h)) = G ∘ ⇑C :=
      ⟨⇑(T (toV h)) ∘ ⇑C.symm, by ext x; simp⟩
    have hGC : (G ∘ ⇑C) ∘ ⇑C.symm = G := by funext x; simp
    rw [hG, hS, hGC]
    funext x
    simp
  let B : Sch (Fin n) → Sch (Fin n) → ℂ := fun h h' => ∫ x, T' h x * conj (T' h' x)
  have hcont : ∀ h', ∃ L : Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h := by
    intro h'
    refine ⟨(innerSL ℂ ((T' h').toLp 2)).comp
      ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))).comp T'), fun h => ?_⟩
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, SchwartzMap.toLpCLM_apply]
    rw [SchwartzMap.inner_toL2_toL2_eq (T' h') (T' h) volume]
    simp only [B, RCLike.inner_apply]
  have hherm : ∀ h h', B h' h = conj (B h h') := by
    intro h h'
    simp only [B]
    rw [← integral_conj]
    congr 1
    funext x
    simp [mul_comm]
  have hpos : ∀ h, 0 ≤ (B h h).re := by
    intro h
    have e : B h h = ((∫ x, Complex.normSq (T' h x) : ℝ) : ℂ) := by
      have e0 : B h h = ∫ x, ((Complex.normSq (T' h x) : ℝ) : ℂ) := by simp only [B, Complex.mul_conj]
      rw [e0]
      first
        | exact integral_complex_ofReal
        | exact integral_ofReal
    rw [e, Complex.ofReal_re]
    exact integral_nonneg fun x => Complex.normSq_nonneg _
  have hinv : ∀ (w : Fin n ⊕ Fin n → ℝ) (h h' g g' : Sch (Fin n)), ⇑g = rhoFun w ⇑h →
      ⇑g' = rhoFun w ⇑h' → B g g' = B h h' := by
    intro w h h' g g' hg hg'
    simp only [B]
    rw [hI w h g hg, hI w h' g' hg']
    exact integral_rhoFun_mul_conj _ _ _
  obtain ⟨c, hc0, hc⟩ := H n B hcont hherm hpos hinv
  have hB : ∀ f f' : SInf F κ, ∫ x, T f (C.symm x) * conj (T f' (C.symm x)) =
      (c : ℂ) * ∫ x, f (C.symm x) * conj (f' (C.symm x)) := by
    intro f f'
    have := hc (toE f) (toE f')
    simpa only [B, hT', hVE, htoE, Function.comp_apply] using this
  refine ⟨c, hc0, fun μ hμ f f' => ?_⟩
  haveI := hμ
  obtain ⟨k, hk⟩ := haar_coords_cplx μ C
  rw [hk, hk, hB]
  ring

end GlobalTheory.ArchUniq.FormTransport

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rho_invariant_form_const_mul_inner : (∀ (n : ℕ) (B : GlobalTheory.RealWeil.Sch (Fin n) → GlobalTheory.RealWeil.Sch (Fin n) → ℂ),
    (∀ h', ∃ L : GlobalTheory.RealWeil.Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h) →
    (∀ h h', B h' h = starRingEnd ℂ (B h h')) → (∀ h, 0 ≤ (B h h).re) →
    (∀ (w : Fin n ⊕ Fin n → ℝ) (h h' g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑h' → B g g' = B h h') →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x)) → ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
  atlas_forward_decl GlobalTheory.ArchUniq.FormTransport.const_of_euclidean
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory GlobalTheory.RealWeil
open scoped Matrix ENNReal SchwartzMap

namespace GlobalTheory.SvNForm

theorem sympl_neg_self {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) : sympl w (-w) = 0 := by
  have h1 : pPart (-w) = -pPart w := rfl
  have h2 : qPart (-w) = -qPart w := rfl
  simp only [sympl, h1, h2, inner_neg_right, real_inner_comm (pPart w) (qPart w)]
  ring

theorem rhoFun_neg_cancel {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℂ) :
    rhoFun w (rhoFun (-w) u) = u := by
  rw [rhoFun_rhoFun, sympl_neg_self, add_neg_cancel, rhoFun_zero]
  simp

theorem step (n : ℕ) (B : Sch (Fin n) → Sch (Fin n) → ℂ)
    (hB : ∀ h', ∃ L : Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h)
    (f f' g g' : Sch (Fin n)) (G : (Fin n ⊕ Fin n → ℝ) → Sch (Fin n)) (hGc : Continuous G)
    (hG : ∀ w, ⇑(G w) = rhoFun w ⇑f)
    (hGb : ∀ k m : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (G w) ≤ C * (1 + ‖w‖) ^ N) :
    (∫ x, f x * starRingEnd ℂ (g x)) * B g' f' =
      ∫ w, starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * B (G w) f' := by
  obtain ⟨L, hL⟩ := hB f'
  set ip : ℂ := ∫ x, f x * starRingEnd ℂ (g x) with hip
  set c : (Fin n ⊕ Fin n → ℝ) → ℂ := fun w => starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) with hc
  have hcc : Continuous c := Complex.continuous_conj.comp (GlobalTheory.T.matrix_coeff_continuous_rapid_decay n g g').1
  have hint : ∀ k m : ℕ, Integrable (fun w => ‖c w‖ * SchwartzMap.seminorm ℂ k m (G w)) := by
    intro k m
    obtain ⟨C, N, hC⟩ := hGb k m
    set d : ℕ := Module.finrank ℝ (Fin n ⊕ Fin n → ℝ)
    obtain ⟨C', hC'⟩ := (GlobalTheory.T.matrix_coeff_continuous_rapid_decay n g g').2 (N + (d + 1))
    have hsc : Continuous fun w => SchwartzMap.seminorm ℂ k m (G w) :=
      ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Fin n)) ℂ).continuous_seminorm (k, m)).comp hGc
    have hI : Integrable (fun w : Fin n ⊕ Fin n → ℝ => (1 + ‖w‖) ^ (-((d + 1 : ℕ) : ℝ))) :=
      integrable_one_add_norm (by push_cast; linarith)
    refine (hI.const_mul (C' * |C|)).mono' ((hcc.norm.mul hsc).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => ?_)
    have hpos : 0 < 1 + ‖w‖ := by positivity
    have e1 : ‖c w‖ = ‖∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)‖ := by simp [hc]
    have h1 := hC' w
    have h2 := hC w
    have hs0 : 0 ≤ SchwartzMap.seminorm ℂ k m (G w) := apply_nonneg _ _
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hs0, e1]
    have hrp : (1 + ‖w‖) ^ (-((d + 1 : ℕ) : ℝ)) = ((1 + ‖w‖) ^ (d + 1))⁻¹ := by
      rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
    rw [hrp]
    set M := ‖∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)‖
    have hM : 0 ≤ M := norm_nonneg _
    have hA : (0:ℝ) < (1 + ‖w‖) ^ N := by positivity
    have hB' : (0:ℝ) < (1 + ‖w‖) ^ (d + 1) := by positivity
    have h3 : SchwartzMap.seminorm ℂ k m (G w) ≤ |C| * (1 + ‖w‖) ^ N :=
      h2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hA.le)
    rw [pow_add] at h1
    calc M * SchwartzMap.seminorm ℂ k m (G w) ≤ M * (|C| * (1 + ‖w‖) ^ N) := mul_le_mul_of_nonneg_left h3 hM
      _ = |C| * (M * ((1 + ‖w‖) ^ N * (1 + ‖w‖) ^ (d + 1))) * ((1 + ‖w‖) ^ (d + 1))⁻¹ := by
          field_simp
      _ ≤ |C| * C' * ((1 + ‖w‖) ^ (d + 1))⁻¹ := by
          gcongr
      _ = C' * |C| * ((1 + ‖w‖) ^ (d + 1))⁻¹ := by ring
  have hpt : ∀ x, (ip • g') x = ∫ w, c w * G w x := by
    intro x
    simp only [SchwartzMap.smul_apply, smul_eq_mul, hc, hG]
    rw [GlobalTheory.T.schrodinger_orthogonality_relation n f g g' x]
  have key := GlobalTheory.T.schwartz_functional_integral_comm (Fin n ⊕ Fin n → ℝ) volume n L G c (ip • g') hGc hcc hint hpt
  calc ip * B g' f' = B (ip • g') f' := by rw [hL, hL, map_smul, smul_eq_mul]
    _ = ∫ w, c w * L (G w) := by rw [hL]; exact key
    _ = ∫ w, c w * B (G w) f' := by simp only [hL]

theorem core : ∀ (n : ℕ) (B : GlobalTheory.RealWeil.Sch (Fin n) → GlobalTheory.RealWeil.Sch (Fin n) → ℂ),
    (∀ h', ∃ L : GlobalTheory.RealWeil.Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h) →
    (∀ h h', B h' h = starRingEnd ℂ (B h h')) → (∀ h, 0 ≤ (B h h).re) →
    (∀ (w : Fin n ⊕ Fin n → ℝ) (h h' g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑h' → B g g' = B h h') →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x) := by
  intro n B hB hherm hpos hinv
  refine GlobalTheory.T.hermitian_form_const_mul_inner n B hherm hpos fun f f' g g' => ?_
  obtain ⟨G, hGc, hG, hGb⟩ := GlobalTheory.T.schrodinger_rep_schwartz_polynomial_bound n f
  obtain ⟨G', hG'c, hG', hG'b⟩ := GlobalTheory.T.schrodinger_rep_schwartz_polynomial_bound n f'
  have s1 := step n B hB f f' g g' G hGc hG hGb
  have s2 := step n B hB f' f g' g G' hG'c hG' hG'b
  set mc : Sch (Fin n) → Sch (Fin n) → (Fin n ⊕ Fin n → ℝ) → ℂ :=
    fun u v w => ∫ t, rhoFun w ⇑u t * starRingEnd ℂ (v t) with hmc
  have pw : ∀ w, starRingEnd ℂ (mc g g' w) * B (G w) f' = mc g' g (-w) * starRingEnd ℂ (B (G' (-w)) f) := by
    intro w
    have e1 : B (G w) f' = B f (G' (-w)) :=
      hinv w f (G' (-w)) (G w) f' (hG w) (by rw [hG' (-w), rhoFun_neg_cancel])
    have e2 : mc g g' w = ∫ t, g t * starRingEnd ℂ (rhoFun (-w) ⇑g' t) := by
      simp only [hmc]
      conv_lhs => rw [← rhoFun_neg_cancel w ⇑g']
      exact GlobalTheory.T.schrodinger_rep_unitary n w ⇑g (rhoFun (-w) ⇑g')
    rw [e1, hherm, e2, ← integral_conj]
    simp only [hmc, map_mul, Complex.conj_conj]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp [mul_comm]
  rw [s1]
  have e3 : (∫ x, g' x * starRingEnd ℂ (f' x)) * B f g =
      starRingEnd ℂ ((∫ x, f' x * starRingEnd ℂ (g' x)) * B g f) := by
    rw [map_mul, ← integral_conj, hherm g f]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp [mul_comm]
  simp only [hmc] at pw
  rw [e3, s2, ← integral_conj]
  simp only [pw]
  have hneg := integral_neg_eq_self (fun w => (∫ t, rhoFun w ⇑g' t * starRingEnd ℂ (g t)) *
    starRingEnd ℂ (B (G' w) f)) (volume : Measure (Fin n ⊕ Fin n → ℝ))
  rw [hneg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp [map_mul]

theorem schrodinger_intertwiner_l2_const : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := GlobalTheory.T.rho_invariant_form_const_mul_inner core

end GlobalTheory.SvNForm
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_intertwiner_l2_constant : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
  atlas_forward_decl GlobalTheory.SvNForm.schrodinger_intertwiner_l2_const
end
