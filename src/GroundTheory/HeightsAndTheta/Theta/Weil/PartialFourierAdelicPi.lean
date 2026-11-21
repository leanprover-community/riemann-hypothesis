import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.WeilPolarization.StdFormOneNondegenerate

section
namespace GroundTheory.Heights₂.Theta

open MeasureTheory SchwartzMap Real Complex Filter Topology
open scoped FourierTransform ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] {ι : Type} [Fintype ι]

section Slice

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_slice_le {f : V₁ × (EuclideanSpace ℝ ι) → E} (hf : ContDiff ℝ ∞ f) (x : V₁) (v : (EuclideanSpace ℝ ι))
    (n : ℕ) : ‖iteratedFDeriv ℝ n (fun v' ↦ f (x, v')) v‖ ≤ ‖iteratedFDeriv ℝ n f (x, v)‖ := by
  have h : (fun v' : (EuclideanSpace ℝ ι) ↦ f (x, v')) =
      (fun q ↦ f (q + (x, 0))) ∘ (ContinuousLinearMap.inr ℝ V₁ (EuclideanSpace ℝ ι)) := by
    funext v'
    simp
  have hc : ContDiff ℝ ∞ (fun q ↦ f (q + (x, 0))) := hf.comp (contDiff_id.add contDiff_const)
  rw [h, ContinuousLinearMap.iteratedFDeriv_comp_right _ hc _ (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ V₁ (EuclideanSpace ℝ ι)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ ↦ by positivity) fun _ _ ↦ ContinuousLinearMap.norm_inr_le_one ℝ V₁ (EuclideanSpace ℝ ι)
  have h2 : (ContinuousLinearMap.inr ℝ V₁ (EuclideanSpace ℝ ι)) v + (x, 0) = (x, v) := by simp
  rw [h2]
  calc _ ≤ ‖iteratedFDeriv ℝ n f (x, v)‖ * 1 := by gcongr
    _ = _ := mul_one _

def schwartzSlice (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) (x : V₁) : 𝓢((EuclideanSpace ℝ ι), E) where
  toFun v := F (x, v)
  smooth' := (F.smooth ⊤).comp (contDiff_const.prodMk contDiff_id)
  decay' k n := by
    obtain ⟨C, -, hC⟩ := F.decay k n
    refine ⟨C, fun v ↦ ?_⟩
    calc ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (fun v' ↦ F (x, v')) v‖
        ≤ ‖(x, v)‖ ^ k * ‖iteratedFDeriv ℝ n F (x, v)‖ := by
          gcongr
          · exact norm_snd_le (x, v)
          · exact norm_iteratedFDeriv_slice_le (F.smooth ⊤) x v n
      _ ≤ C := hC _


theorem seminorm_smul_schwartzSlice_le (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) (x : V₁) (j k n : ℕ) :
    SchwartzMap.seminorm ℝ k n ((‖x‖ ^ j) • schwartzSlice F x) ≤
      SchwartzMap.seminorm ℝ (j + k) n F := by
  refine SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity) fun v ↦ ?_
  have hsm : ContDiffAt ℝ n (schwartzSlice F x) v :=
    ((schwartzSlice F x).smooth ⊤).contDiffAt.of_le (by exact_mod_cast le_top)
  have hcoe : (((‖x‖ ^ j) • schwartzSlice F x : 𝓢((EuclideanSpace ℝ ι), E)) : (EuclideanSpace ℝ ι) → E) =
      (‖x‖ ^ j) • (schwartzSlice F x : (EuclideanSpace ℝ ι) → E) := rfl
  rw [hcoe, iteratedFDeriv_const_smul_apply hsm, norm_smul,
    Real.norm_of_nonneg (by positivity)]
  calc ‖v‖ ^ k * (‖x‖ ^ j * ‖iteratedFDeriv ℝ n (schwartzSlice F x) v‖)
      ≤ ‖(x, v)‖ ^ k * (‖(x, v)‖ ^ j * ‖iteratedFDeriv ℝ n F (x, v)‖) := by
        gcongr
        · exact norm_snd_le (x, v)
        · exact norm_fst_le (x, v)
        · exact norm_iteratedFDeriv_slice_le (F.smooth ⊤) x v n
    _ = ‖(x, v)‖ ^ (j + k) * ‖iteratedFDeriv ℝ n F (x, v)‖ := by ring
    _ ≤ _ := F.le_seminorm ℝ (j + k) n (x, v)

theorem exists_integrable_bound_snd (G : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) :
    ∃ b : (EuclideanSpace ℝ ι) → ℝ, Integrable b ∧ ∀ x v, ‖G (x, v)‖ ≤ b v := by
  set r : ℕ := Module.finrank ℝ (EuclideanSpace ℝ ι) + 1
  set C : ℝ := 2 ^ r * ((Finset.Iic (r, 0)).sup fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) G
  refine ⟨fun v ↦ C * (1 + ‖v‖) ^ (-(r : ℝ)),
    (integrable_one_add_norm (by simp [r])).const_mul C, fun x v ↦ ?_⟩
  have h := G.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (r, 0)) (k := r) (n := 0) le_rfl le_rfl
    (x, v)
  rw [norm_iteratedFDeriv_zero] at h
  have h1 : (1 + ‖v‖) ^ r ≤ (1 + ‖(x, v)‖) ^ r := by
    gcongr
    exact norm_snd_le (x, v)
  have hpos : 0 < (1 + ‖v‖) ^ r := by positivity
  show ‖G (x, v)‖ ≤ C * (1 + ‖v‖) ^ (-(r : ℝ))
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖G (x, v)‖ * (1 + ‖v‖) ^ r ≤ (1 + ‖(x, v)‖) ^ r * ‖G (x, v)‖ := by
        rw [mul_comm]
        gcongr
    _ ≤ C := h

end Slice

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E) (p : V₁ × (EuclideanSpace ℝ ι)) : E :=
  𝓕 (fun v ↦ F (p.1, v)) p.2

theorem partialFourierSnd_apply (F : V₁ × (EuclideanSpace ℝ ι) → E) (x : V₁) (w : (EuclideanSpace ℝ ι)) :
    partialFourierSnd F (x, w) = ∫ v, 𝐞 (-inner ℝ v w) • F (x, v) := by
  rw [partialFourierSnd, Real.fourier_eq]

theorem partialFourierSnd_eq (F : V₁ × (EuclideanSpace ℝ ι) → E) :
    partialFourierSnd F = fun p ↦ ∫ v, ((𝐞 (-inner ℝ v p.2) : ℂ)) • F (p.1, v) := by
  funext p
  exact partialFourierSnd_apply F p.1 p.2

theorem exists_bound_partialFourierSnd (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) (j k : ℕ) :
    ∃ C, ∀ x w, ‖x‖ ^ j * (‖w‖ ^ k * ‖partialFourierSnd F (x, w)‖) ≤ C := by
  let T : 𝓢((EuclideanSpace ℝ ι), E) →L[ℝ] 𝓢((EuclideanSpace ℝ ι), E) := SchwartzMap.fourierTransformCLM ℝ
  let q : Seminorm ℝ 𝓢((EuclideanSpace ℝ ι), E) := (SchwartzMap.seminorm ℝ k 0).comp T.toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℝ (EuclideanSpace ℝ ι) E).continuous_seminorm (k, 0)).comp T.continuous
  obtain ⟨s, C₀, -, hC₀⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ (EuclideanSpace ℝ ι) E) q hq
  set M : ℝ := ∑ i ∈ s, SchwartzMap.seminorm ℝ (j + i.1) i.2 F
  refine ⟨C₀ * M, fun x w ↦ ?_⟩
  set g : 𝓢((EuclideanSpace ℝ ι), E) := (‖x‖ ^ j) • schwartzSlice F x
  have hTg : T g w = (‖x‖ ^ j) • partialFourierSnd F (x, w) := by
    simp only [g, map_smul, smul_apply]
    rfl
  have h2 : ‖w‖ ^ k * ‖T g w‖ ≤ q g := (T g).norm_pow_mul_le_seminorm ℝ k w
  have h3 : q g ≤ C₀ * (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ ι) E)) g := by
    have := hC₀ g
    simpa [NNReal.smul_def] using this
  have h4 : (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ ι) E)) g ≤ M := by
    refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _)
      fun i hi ↦ ?_
    refine (seminorm_smul_schwartzSlice_le F x j i.1 i.2).trans ?_
    exact Finset.single_le_sum (f := fun i : ℕ × ℕ ↦ SchwartzMap.seminorm ℝ (j + i.1) i.2 F)
      (fun _ _ ↦ apply_nonneg _ _) hi
  calc ‖x‖ ^ j * (‖w‖ ^ k * ‖partialFourierSnd F (x, w)‖) = ‖w‖ ^ k * ‖T g w‖ := by
        rw [hTg, norm_smul, Real.norm_of_nonneg (by positivity)]
        ring
    _ ≤ q g := h2
    _ ≤ C₀ * (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ ι) E)) g := h3
    _ ≤ C₀ * M := by gcongr

variable (V₁ ι) in

abbrev fstIncl : V₁ × (EuclideanSpace ℝ ι) →L[ℝ] V₁ × (EuclideanSpace ℝ ι) :=
  (ContinuousLinearMap.inl ℝ V₁ (EuclideanSpace ℝ ι)).comp (ContinuousLinearMap.fst ℝ V₁ (EuclideanSpace ℝ ι))

variable (V₁ ι) in

def sndInnerCLM : V₁ × (EuclideanSpace ℝ ι) →L[ℝ] (V₁ × (EuclideanSpace ℝ ι) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (V₁ × (EuclideanSpace ℝ ι)) (EuclideanSpace ℝ ι) ℝ).flip (ContinuousLinearMap.snd ℝ V₁ (EuclideanSpace ℝ ι))).comp
    ((innerSL ℝ).comp (ContinuousLinearMap.snd ℝ V₁ (EuclideanSpace ℝ ι)))

theorem sndInnerCLM_apply (p q : V₁ × (EuclideanSpace ℝ ι)) :
    sndInnerCLM V₁ ι p q = inner ℝ p.2 q.2 := by
  simp [sndInnerCLM]

def partialFourierDeriv (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) : 𝓢(V₁ × (EuclideanSpace ℝ ι), V₁ × (EuclideanSpace ℝ ι) →L[ℝ] E) :=
  SchwartzMap.postcompCLM ((ContinuousLinearMap.compL ℝ (V₁ × (EuclideanSpace ℝ ι)) (V₁ × (EuclideanSpace ℝ ι)) E).flip
      (fstIncl V₁ ι)) (SchwartzMap.fderivCLM ℝ (V₁ × (EuclideanSpace ℝ ι)) E F) +
    (-(2 * π * I) : ℂ) • SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.smulRightL ℝ (V₁ × (EuclideanSpace ℝ ι)) E).flip
      (sndInnerCLM V₁ ι).hasTemperateGrowth F

theorem partialFourierDeriv_apply (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) (p q : V₁ × (EuclideanSpace ℝ ι)) :
    partialFourierDeriv F p q =
      fderiv ℝ F p (q.1, 0) + (-(2 * π * I) : ℂ) • (inner ℝ p.2 q.2 • F p) := by
  simp [partialFourierDeriv, SchwartzMap.postcompCLM_apply, SchwartzMap.bilinLeftCLM_apply,
    sndInnerCLM_apply, fstIncl]

theorem hasFDerivAt_partialFourierSnd_integrand (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) (v : (EuclideanSpace ℝ ι)) (q : V₁ × (EuclideanSpace ℝ ι)) :
    HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q'.2) : ℂ)) • F (q'.1, v))
      (((𝐞 (-inner ℝ v q.2) : ℂ)) • partialFourierDeriv F (q.1, v)) q := by
  have he : HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q'.2) : Circle) : ℂ))
      (((-2 * π * I * 𝐞 (-(innerSL ℝ) v q.2)) • (ofRealCLM ∘L ((innerSL ℝ) v))).comp
        (ContinuousLinearMap.snd ℝ V₁ (EuclideanSpace ℝ ι))) q :=
    (hasFDerivAt_fourierChar_neg_bilinear_right (innerSL ℝ) v q.2).comp q hasFDerivAt_snd
  have hpair : HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ (q'.1, v)) (fstIncl V₁ ι) q := by
    have h : (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ (q'.1, v)) =
        fun q' ↦ fstIncl V₁ ι q' + ((0 : V₁), v) := by
      funext q'
      simp
    rw [h]
    exact (fstIncl V₁ ι).hasFDerivAt.add_const _
  have hF : HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ F (q'.1, v))
      ((fderiv ℝ F (q.1, v)).comp (fstIncl V₁ ι)) q :=
    (F.differentiableAt.hasFDerivAt).comp q hpair
  have hs : HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q'.2) : ℂ)) • F (q'.1, v))
      ((((𝐞 (-inner ℝ v q.2) : Circle) : ℂ)) • (fderiv ℝ F (q.1, v)).comp (fstIncl V₁ ι) +
        (((-2 * π * I * 𝐞 (-(innerSL ℝ) v q.2)) • (ofRealCLM ∘L ((innerSL ℝ) v))).comp
          (ContinuousLinearMap.snd ℝ V₁ (EuclideanSpace ℝ ι))).smulRight (F (q.1, v))) q := he.smul hF
  refine hs.congr_fderiv (ContinuousLinearMap.ext fun r ↦ ?_)
  rw [ContinuousLinearMap.smul_apply, partialFourierDeriv_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ofRealCLM_apply, innerSL_apply_apply,
    smul_eq_mul]
  rw [← Complex.coe_smul, smul_add, smul_smul, smul_smul]
  congr 1
  ring_nf
  rfl

theorem hasFDerivAt_partialFourierSnd (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E))
    (p : V₁ × (EuclideanSpace ℝ ι)) :
    HasFDerivAt (partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E))
      (partialFourierSnd (partialFourierDeriv F : V₁ × (EuclideanSpace ℝ ι) →
        (V₁ × (EuclideanSpace ℝ ι) →L[ℝ] E)) p) p := by
  obtain ⟨b, hb, hbF⟩ := exists_integrable_bound_snd (partialFourierDeriv F)
  obtain ⟨b₀, hb₀, hb₀F⟩ := exists_integrable_bound_snd F
  have hce : ∀ w : (EuclideanSpace ℝ ι),
      Continuous fun v : (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v w) : Circle) : ℂ) := fun w ↦
    continuous_subtype_val.comp (continuous_fourierChar.comp
      (continuous_id.inner continuous_const).neg)
  have hcont : ∀ q : V₁ × (EuclideanSpace ℝ ι),
      Continuous fun v : (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q.2) : ℂ)) • F (q.1, v) :=
    fun q ↦ (hce q.2).smul (F.continuous.comp (continuous_const.prodMk continuous_id))
  have hcont' : Continuous fun v : (EuclideanSpace ℝ ι) ↦
      ((𝐞 (-inner ℝ v p.2) : ℂ)) • partialFourierDeriv F (p.1, v) :=
    (hce p.2).smul ((partialFourierDeriv F).continuous.comp
      (continuous_const.prodMk continuous_id))
  have hm : ∀ᶠ q in 𝓝 p, AEStronglyMeasurable
      (fun v : (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q.2) : ℂ)) • F (q.1, v)) volume :=
    Eventually.of_forall fun q ↦ (hcont q).aestronglyMeasurable
  have hi : Integrable
      (fun v : (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v p.2) : ℂ)) • F (p.1, v)) volume := by
    refine hb₀.mono' (hcont p).aestronglyMeasurable (Eventually.of_forall fun v ↦ ?_)
    rw [norm_smul, Circle.norm_coe, one_mul]
    exact hb₀F _ _
  have hm' : AEStronglyMeasurable (fun v : (EuclideanSpace ℝ ι) ↦
      ((𝐞 (-inner ℝ v p.2) : ℂ)) • partialFourierDeriv F (p.1, v)) volume :=
    hcont'.aestronglyMeasurable
  have hbd : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ ι)), ∀ q ∈ (Set.univ : Set (V₁ × (EuclideanSpace ℝ ι))),
      ‖((𝐞 (-inner ℝ v q.2) : ℂ)) • partialFourierDeriv F (q.1, v)‖ ≤ b v := by
    refine Eventually.of_forall fun v q _ ↦ ?_
    rw [norm_smul, Circle.norm_coe, one_mul]
    exact hbF _ _
  have hd : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ ι)), ∀ q ∈ (Set.univ : Set (V₁ × (EuclideanSpace ℝ ι))),
      HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q'.2) : ℂ)) • F (q'.1, v))
        (((𝐞 (-inner ℝ v q.2) : ℂ)) • partialFourierDeriv F (q.1, v)) q :=
    Eventually.of_forall fun v q _ ↦ hasFDerivAt_partialFourierSnd_integrand F v q
  have key : HasFDerivAt (fun q : V₁ × (EuclideanSpace ℝ ι) ↦
      ∫ v, ((𝐞 (-inner ℝ v q.2) : ℂ)) • F (q.1, v))
      (∫ v, ((𝐞 (-inner ℝ v p.2) : ℂ)) • partialFourierDeriv F (p.1, v)) p :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (E := E)
      (H := V₁ × (EuclideanSpace ℝ ι)) Filter.univ_mem hm hi hm' hbd hb hd
  rw [partialFourierSnd_eq (F : V₁ × (EuclideanSpace ℝ ι) → E)]
  convert key using 1
  exact congrFun (partialFourierSnd_eq _) p

theorem fderiv_partialFourierSnd (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) :
    fderiv ℝ (partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E)) =
      partialFourierSnd (partialFourierDeriv F : V₁ × (EuclideanSpace ℝ ι) →
        (V₁ × (EuclideanSpace ℝ ι) →L[ℝ] E)) :=
  funext fun p ↦ (hasFDerivAt_partialFourierSnd F p).fderiv

theorem contDiff_partialFourierSnd (n : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)),
      ContDiff ℝ n (partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E)) := by
  induction n with
  | zero =>
    intro E _ _ _ F
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun p ↦
      (hasFDerivAt_partialFourierSnd F p).continuousAt)
  | succ n ih =>
    intro E _ _ _ F
    have h : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [h, contDiff_succ_iff_fderiv]
    refine ⟨fun p ↦ (hasFDerivAt_partialFourierSnd F p).differentiableAt, fun h' ↦ ?_, ?_⟩
    · exact absurd h' (by simp)
    · rw [fderiv_partialFourierSnd]
      exact ih _ (partialFourierDeriv F)

theorem exists_bound_iteratedFDeriv_partialFourierSnd (n : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E))
      (k : ℕ), ∃ C, ∀ p : V₁ × (EuclideanSpace ℝ ι),
        ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E)) p‖ ≤ C := by
  induction n with
  | zero =>
    intro E _ _ _ F k
    obtain ⟨C₁, h₁⟩ := exists_bound_partialFourierSnd F k 0
    obtain ⟨C₂, h₂⟩ := exists_bound_partialFourierSnd F 0 k
    refine ⟨C₁ + C₂, fun p ↦ ?_⟩
    rw [norm_iteratedFDeriv_zero]
    have h1 := h₁ p.1 p.2
    have h2 := h₂ p.1 p.2
    simp only [pow_zero, one_mul, Prod.mk.eta] at h1 h2
    have hp : ‖p‖ ^ k ≤ ‖p.1‖ ^ k + ‖p.2‖ ^ k := by
      rw [Prod.norm_def]
      rcases le_total ‖p.1‖ ‖p.2‖ with h | h
      · rw [max_eq_right h]
        linarith [pow_nonneg (norm_nonneg p.1) k]
      · rw [max_eq_left h]
        linarith [pow_nonneg (norm_nonneg p.2) k]
    calc ‖p‖ ^ k * ‖partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E) p‖
        ≤ (‖p.1‖ ^ k + ‖p.2‖ ^ k) * ‖partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E) p‖ := by gcongr
      _ = ‖p.1‖ ^ k * ‖partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E) p‖ +
          ‖p.2‖ ^ k * ‖partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E) p‖ := by ring
      _ ≤ C₁ + C₂ := add_le_add h1 h2
  | succ n ih =>
    intro E _ _ _ F k
    obtain ⟨C, hC⟩ := ih _ (partialFourierDeriv F) k
    refine ⟨C, fun p ↦ ?_⟩
    rw [← norm_iteratedFDeriv_fderiv, fderiv_partialFourierSnd]
    exact hC p

def partialFourierSndSchwartz (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) : 𝓢(V₁ × (EuclideanSpace ℝ ι), E) where
  toFun := partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E)
  smooth' := contDiff_infty.mpr fun n ↦ contDiff_partialFourierSnd n E F
  decay' k n := exists_bound_iteratedFDeriv_partialFourierSnd n E F k


end

end GroundTheory.Heights₂.Theta
end

section
namespace GroundTheory.Heights₂.Theta

open GroundTheory.Global NumberField MeasureTheory TensorProduct
open scoped NumberField.AdeleRing ComplexOrder

noncomputable section

section Alg

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

def IsLagrangian (ω : LinearMap.BilinForm R W) (L : Submodule R W) : Prop :=
  ω.orthogonal L = L

variable {P₁ P₂ Q₁ Q₂ : Type*} [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
  [AddCommGroup Q₁] [Module R Q₁] [AddCommGroup Q₂] [Module R Q₂]

namespace FourPieces

variable {ω : LinearMap.BilinForm R W}

def incP₂ (F : FourPieces ω P₁ P₂ Q₁ Q₂) : P₂ →ₗ[R] W :=
  F.e.symm.toLinearMap ∘ₗ LinearMap.inl R (P₁ × P₂) (Q₁ × Q₂) ∘ₗ LinearMap.inr R P₁ P₂

def incQ₂ (F : FourPieces ω P₁ P₂ Q₁ Q₂) : Q₂ →ₗ[R] W :=
  F.e.symm.toLinearMap ∘ₗ LinearMap.inr R (P₁ × P₂) (Q₁ × Q₂) ∘ₗ LinearMap.inr R Q₁ Q₂

theorem incP₂_apply (F : FourPieces ω P₁ P₂ Q₁ Q₂) (p : P₂) :
    F.incP₂ p = F.e.symm ((0, p), (0, 0)) := rfl

theorem incQ₂_apply (F : FourPieces ω P₁ P₂ Q₁ Q₂) (q : Q₂) :
    F.incQ₂ q = F.e.symm ((0, 0), (0, q)) := rfl

theorem form_incP₂_incQ₂ (F : FourPieces ω P₁ P₂ Q₁ Q₂) (p : P₂) (q : Q₂) :
    ω (F.incP₂ p) (F.incQ₂ q) = F.a₂ p q := by
  rw [F.form, incP₂_apply, incQ₂_apply]
  simp

end FourPieces

end Alg

section Adelic

variable (K : Type*) [Field K] [NumberField K]

variable (P Q : Type*) [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q] in

abbrev adelicProdEquiv : AdelicPoints K (P × Q) ≃ₗ[𝔸[K]] AdelicPoints K P × AdelicPoints K Q :=
  TensorProduct.prodRight K 𝔸[K] 𝔸[K] P Q

variable {K}
variable {W P₁ P₂ Q₁ Q₂ : Type*} [AddCommGroup W] [Module K W]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup Q₁] [Module K Q₁] [AddCommGroup Q₂] [Module K Q₂]

namespace FourPieces

variable {ω : LinearMap.BilinForm K W}

def adelicPairing₂ (F : FourPieces ω P₁ P₂ Q₁ Q₂) (p : AdelicPoints K P₂) (q : AdelicPoints K Q₂) :
    𝔸[K] :=
  ω.baseChange 𝔸[K] (F.incP₂.baseChange 𝔸[K] p) (F.incQ₂.baseChange 𝔸[K] q)

theorem adelicPairing₂_tmul (F : FourPieces ω P₁ P₂ Q₁ Q₂) (a a' : 𝔸[K]) (p : P₂) (q : Q₂) :
    F.adelicPairing₂ (a ⊗ₜ p) (a' ⊗ₜ q) = algebraMap K 𝔸[K] (F.a₂ p q) * (a * a') := by
  rw [adelicPairing₂, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
    LinearMap.BilinForm.baseChange_tmul, form_incP₂_incQ₂, Algebra.smul_def]

variable [FiniteDimensional K P₁] [FiniteDimensional K P₂] [FiniteDimensional K Q₂]

def adelicPartialFourier (ψ : AddChar 𝔸[K] Circle) (F : FourPieces ω P₁ P₂ Q₁ Q₂)
    (φ : AdelicPoints K (P₁ × P₂) → ℂ) : AdelicPoints K (P₁ × Q₂) → ℂ :=
  fun z ↦ ∫ p : AdelicPoints K P₂,
    φ ((adelicProdEquiv K P₁ P₂).symm ((adelicProdEquiv K P₁ Q₂ z).1, p)) *
      (ψ (F.adelicPairing₂ p (adelicProdEquiv K P₁ Q₂ z).2) : ℂ) ∂adelicPointsMeasure K P₂

def adelicPartialFourierInv (ψ : AddChar 𝔸[K] Circle) (F : FourPieces ω P₁ P₂ Q₁ Q₂)
    (Φ : AdelicPoints K (P₁ × Q₂) → ℂ) : AdelicPoints K (P₁ × P₂) → ℂ :=
  fun z ↦ ∫ q : AdelicPoints K Q₂,
    Φ ((adelicProdEquiv K P₁ Q₂).symm ((adelicProdEquiv K P₁ P₂ z).1, q)) *
      (ψ (-F.adelicPairing₂ (adelicProdEquiv K P₁ P₂ z).2 q) : ℂ) ∂adelicPointsMeasure K Q₂

end FourPieces

end Adelic

def PartialFourierTheta.Statement : Prop :=
  ∀ (K W P₁ P₂ Q₁ Q₂ : Type) [Field K] [NumberField K] [AddCommGroup W] [Module K W]
    [AddCommGroup P₁] [Module K P₁] [FiniteDimensional K P₁]
    [AddCommGroup P₂] [Module K P₂] [FiniteDimensional K P₂]
    [AddCommGroup Q₁] [Module K Q₁] [AddCommGroup Q₂] [Module K Q₂] [FiniteDimensional K Q₂]
    (ψ : AddChar 𝔸[K] Circle), Continuous ψ → (∀ k : K, ψ (algebraMap K 𝔸[K] k) = 1) → ψ ≠ 1 →
    ∀ (ω : LinearMap.BilinForm K W), ω.IsAlt → ω.Nondegenerate →
    ∀ (F : FourPieces ω P₁ P₂ Q₁ Q₂) (φ : AdelicPoints K (P₁ × P₂) → ℂ),
      φ ∈ schwartzBruhatPoints K (P₁ × P₂) →
        F.adelicPartialFourier ψ φ ∈ schwartzBruhatPoints K (P₁ × Q₂) ∧
          rationalTheta (F.adelicPartialFourier ψ φ) = rationalTheta φ

def PartialFourierInversion.Statement : Prop :=
  ∀ (K W P₁ P₂ Q₁ Q₂ : Type) [Field K] [NumberField K] [AddCommGroup W] [Module K W]
    [AddCommGroup P₁] [Module K P₁] [FiniteDimensional K P₁]
    [AddCommGroup P₂] [Module K P₂] [FiniteDimensional K P₂]
    [AddCommGroup Q₁] [Module K Q₁] [AddCommGroup Q₂] [Module K Q₂] [FiniteDimensional K Q₂]
    (ψ : AddChar 𝔸[K] Circle), Continuous ψ → (∀ k : K, ψ (algebraMap K 𝔸[K] k) = 1) → ψ ≠ 1 →
    ∀ (ω : LinearMap.BilinForm K W), ω.IsAlt → ω.Nondegenerate →
    ∀ (F : FourPieces ω P₁ P₂ Q₁ Q₂) (φ : AdelicPoints K (P₁ × P₂) → ℂ),
      φ ∈ schwartzBruhatPoints K (P₁ × P₂) →
        F.adelicPartialFourierInv ψ (F.adelicPartialFourier ψ φ) = φ

def LagrangianPairFourPieces.Statement : Prop :=
  ∀ (K W : Type) [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ω : LinearMap.BilinForm K W), ω.IsAlt → ω.Nondegenerate →
    ∀ L L' : Submodule K W, IsLagrangian ω L → IsLagrangian ω L' →
      ∃ (P₁ P₂ Q₁ Q₂ : Submodule K W) (F : FourPieces ω P₁ P₂ Q₁ Q₂),
        (∀ w, w ∈ L ↔ (F.e w).2 = 0) ∧ (∀ w, w ∈ L' ↔ (F.e w).1.2 = 0 ∧ (F.e w).2.1 = 0)

section Inhabitants

variable (R : Type*) [CommRing R]

def lineFourForm : LinearMap.BilinForm R ((R × R) × (R × R)) :=
  LinearMap.mk₂ R
    (fun w w' ↦ w.1.1 * w'.2.1 + w.1.2 * w'.2.2 - w'.1.1 * w.2.1 - w'.1.2 * w.2.2)
    (fun _ _ _ ↦ by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun _ _ _ ↦ by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun _ _ _ ↦ by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun _ _ _ ↦ by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

theorem lineFourForm_apply (w w' : (R × R) × (R × R)) :
    lineFourForm R w w' = w.1.1 * w'.2.1 + w.1.2 * w'.2.2 - w'.1.1 * w.2.1 - w'.1.2 * w.2.2 := rfl

def lineFourPieces : FourPieces (lineFourForm R) R R R R where
  e := LinearEquiv.refl R _
  a₁ := LinearMap.mul R R
  a₂ := LinearMap.mul R R
  form w w' := by simp [lineFourForm_apply]

def lineFourLagrangian : Submodule R ((R × R) × (R × R)) :=
  LinearMap.ker (LinearMap.snd R (R × R) (R × R))

end Inhabitants

end

end GroundTheory.Heights₂.Theta
end

section
namespace GroundTheory.Heights₂.Theta

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix NumberField NumberField.mixedEmbedding MeasureTheory
  TensorProduct Module
open scoped NumberField.AdeleRing SchwartzMap

noncomputable section

set_option linter.unusedSectionVars false

section Slice

open scoped Classical

variable {K : Type*} [Field K] [NumberField K]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private def sliceInl : (κ → mixedSpace K) →L[ℝ] ((ι ⊕ κ) → mixedSpace K) :=
  ContinuousLinearMap.pi fun s ↦
    Sum.elim (fun _ ↦ (0 : (κ → mixedSpace K) →L[ℝ] mixedSpace K))
      (fun j ↦ ContinuousLinearMap.proj j) s

private theorem sliceInl_apply (u : κ → mixedSpace K) :
    (sliceInl (ι := ι) u : (ι ⊕ κ) → mixedSpace K) = Sum.elim (0 : ι → mixedSpace K) u := by
  funext s
  cases s <;> rfl

private theorem sumElim_hasTemperateGrowth (c : ι → mixedSpace K) :
    (fun u : κ → mixedSpace K ↦ (Sum.elim c u : (ι ⊕ κ) → mixedSpace K)).HasTemperateGrowth := by
  have h : (fun u : κ → mixedSpace K ↦ (Sum.elim c u : (ι ⊕ κ) → mixedSpace K)) =
      fun u ↦ sliceInl (ι := ι) u + Sum.elim c 0 := by
    funext u s
    rw [sliceInl_apply]
    cases s <;> simp
  rw [h]
  exact (sliceInl (K := K) (ι := ι) (κ := κ)).hasTemperateGrowth.add
    (Function.HasTemperateGrowth.const _)

private theorem sumElim_upper (c : ι → mixedSpace K) :
    ∃ (k : ℕ) (C : ℝ), ∀ u : κ → mixedSpace K,
      ‖u‖ ≤ C * (1 + ‖(Sum.elim c u : (ι ⊕ κ) → mixedSpace K)‖) ^ k := by
  refine ⟨1, 1, fun u ↦ ?_⟩
  have hle : ‖u‖ ≤ ‖(Sum.elim c u : (ι ⊕ κ) → mixedSpace K)‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j ↦ by
      simpa using norm_le_pi_norm (Sum.elim c u : (ι ⊕ κ) → mixedSpace K) (Sum.inr j)
  rw [pow_one, one_mul]
  linarith

def schwartzMapSliceSumElim (c : ι → mixedSpace K) (φ : 𝓢((ι ⊕ κ) → mixedSpace K, ℂ)) :
    𝓢(κ → mixedSpace K, ℂ) :=
  SchwartzMap.compCLM ℝ (sumElim_hasTemperateGrowth c) (sumElim_upper c) φ

theorem schwartzMapSliceSumElim_apply (c : ι → mixedSpace K) (φ : 𝓢((ι ⊕ κ) → mixedSpace K, ℂ))
    (u : κ → mixedSpace K) : schwartzMapSliceSumElim c φ u = φ (Sum.elim c u) := rfl

theorem finiteSchwartzBruhatPi_sumElim_mem {g : ((ι ⊕ κ) → 𝔸ᶠ[K]) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi K)
    (c : ι → 𝔸ᶠ[K]) : (fun v : κ → 𝔸ᶠ[K] ↦ g (Sum.elim c v)) ∈ finiteSchwartzBruhatPi K := by
  rw [mem_finiteSchwartzBruhatPi] at hg ⊢
  obtain ⟨hl, hc⟩ := hg
  have hcont : Continuous fun v : κ → 𝔸ᶠ[K] ↦ (Sum.elim c v : (ι ⊕ κ) → 𝔸ᶠ[K]) :=
    continuous_pi fun s ↦ by
      cases s with
      | inl i => exact continuous_const
      | inr j => exact continuous_apply j
  refine ⟨hl.comp_continuous hcont, ?_⟩
  have hπ : Continuous fun w : (ι ⊕ κ) → 𝔸ᶠ[K] ↦ w ∘ Sum.inr :=
    continuous_pi fun j ↦ continuous_apply (Sum.inr j)
  refine HasCompactSupport.intro (hc.image hπ) fun v hv ↦ ?_
  by_contra h
  exact hv ⟨Sum.elim c v, subset_tsupport _ h, Sum.elim_comp_inr c v⟩

theorem infPartPi_sumElim (a : ι → 𝔸[K]) (x : κ → 𝔸[K]) :
    infPartPi (Sum.elim a x : (ι ⊕ κ) → 𝔸[K]) = Sum.elim (infPartPi a) (infPartPi x) := by
  funext s
  cases s <;> rfl

theorem finPartPi_sumElim (a : ι → 𝔸[K]) (x : κ → 𝔸[K]) :
    finPartPi (Sum.elim a x : (ι ⊕ κ) → 𝔸[K]) = Sum.elim (finPartPi a) (finPartPi x) := by
  funext s
  cases s <;> rfl

theorem schwartzBruhatPi_sumElim_mem {F : ((ι ⊕ κ) → 𝔸[K]) → ℂ}
    (hF : F ∈ schwartzBruhatPi K (ι ⊕ κ)) (a : ι → 𝔸[K]) :
    (fun x : κ → 𝔸[K] ↦ F (Sum.elim a x)) ∈ schwartzBruhatPi K κ := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    have h : (fun x : κ → 𝔸[K] ↦ schwartzBruhatTensorPi φ g (Sum.elim a x)) =
        schwartzBruhatTensorPi (schwartzMapSliceSumElim (infPartPi a) φ)
          (fun v ↦ g (Sum.elim (finPartPi a) v)) := by
      funext x
      simp only [schwartzBruhatTensorPi, schwartzMapSliceSumElim_apply, infPartPi_sumElim,
        finPartPi_sumElim]
    rw [h]
    exact schwartzBruhatTensorPi_mem _ (finiteSchwartzBruhatPi_sumElim_mem hg _)
  | zero => exact zero_mem _
  | add F G _ _ hF hG => exact add_mem hF hG
  | smul c F _ hF => exact Submodule.smul_mem _ c hF

end Slice

section Pairing

variable {K W P₁ P₂ Q₁ Q₂ : Type*} [Field K] [AddCommGroup W] [Module K W]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup Q₁] [Module K Q₁] [AddCommGroup Q₂] [Module K Q₂]
  {ω : LinearMap.BilinForm K W}

theorem FourPieces.a₂_eq_zero_left (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) {p : P₂}
    (h : ∀ q, F.a₂ p q = 0) : p = 0 := by
  have hw : F.incP₂ p = 0 := hω.1 _ fun w' ↦ by
    rw [F.form, FourPieces.incP₂_apply, LinearEquiv.apply_symm_apply]
    simp [h]
  have h2 := congrArg (fun w ↦ (F.e w).1.2) hw
  simpa [FourPieces.incP₂_apply] using h2

theorem FourPieces.a₂_eq_zero_right (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) {q : Q₂}
    (h : ∀ p, F.a₂ p q = 0) : q = 0 := by
  have hw : F.incQ₂ q = 0 := hω.2 _ fun w' ↦ by
    rw [F.form, FourPieces.incQ₂_apply, LinearEquiv.apply_symm_apply]
    simp [h]
  have h2 := congrArg (fun w ↦ (F.e w).2.2) hw
  simpa [FourPieces.incQ₂_apply] using h2

variable [FiniteDimensional K P₂] [FiniteDimensional K Q₂]

theorem FourPieces.finrank_P₂_eq_finrank_Q₂ (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) :
    finrank K P₂ = finrank K Q₂ := by
  have h1 : Function.Injective F.a₂ := (injective_iff_map_eq_zero _).mpr fun p hp ↦
    FourPieces.a₂_eq_zero_left hω F fun q ↦ by rw [hp]; rfl
  have h2 : Function.Injective F.a₂.flip := (injective_iff_map_eq_zero _).mpr fun q hq ↦
    FourPieces.a₂_eq_zero_right hω F fun p ↦ by
      have := LinearMap.congr_fun hq p
      simpa using this
  have i1 := LinearMap.finrank_le_finrank_of_injective h1
  have i2 := LinearMap.finrank_le_finrank_of_injective h2
  rw [Subspace.dual_finrank_eq] at i1 i2
  omega

def FourPieces.a₂DualEquiv (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) {ξ : K} (hξ : ξ ≠ 0) :
    Q₂ ≃ₗ[K] Module.Dual K P₂ :=
  LinearMap.linearEquivOfInjective (ξ • F.a₂.flip)
    ((injective_iff_map_eq_zero _).mpr fun q hq ↦ FourPieces.a₂_eq_zero_right hω F fun p ↦ by
      have := LinearMap.congr_fun hq p
      simp only [LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul, LinearMap.zero_apply,
        mul_eq_zero, hξ, false_or] at this
      exact this)
    (by rw [Subspace.dual_finrank_eq, FourPieces.finrank_P₂_eq_finrank_Q₂ hω F])

theorem FourPieces.a₂DualEquiv_apply (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) {ξ : K}
    (hξ : ξ ≠ 0) (q : Q₂) (p : P₂) : FourPieces.a₂DualEquiv hω F hξ q p = ξ * F.a₂ p q := rfl

def FourPieces.a₂PairedBasis (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) {ξ : K}
    (hξ : ξ ≠ 0) : Basis (Fin (finrank K P₂)) K Q₂ :=
  (Module.finBasis K P₂).dualBasis.map (FourPieces.a₂DualEquiv hω F hξ).symm

theorem FourPieces.a₂_a₂PairedBasis (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) {ξ : K}
    (hξ : ξ ≠ 0) (i j : Fin (finrank K P₂)) :
    F.a₂ (Module.finBasis K P₂ i) (FourPieces.a₂PairedBasis hω F hξ j) = ξ⁻¹ * (if i = j then 1 else 0) := by
  have h : FourPieces.a₂DualEquiv hω F hξ (FourPieces.a₂PairedBasis hω F hξ j) = (Module.finBasis K P₂).dualBasis j := by
    rw [FourPieces.a₂PairedBasis, Basis.map_apply, LinearEquiv.apply_symm_apply]
  have h2 := LinearMap.congr_fun h (Module.finBasis K P₂ i)
  rw [FourPieces.a₂DualEquiv_apply, Basis.dualBasis_apply_self] at h2
  rw [← h2, ← mul_assoc, inv_mul_cancel₀ hξ, one_mul]

end Pairing

section Adelic

variable {K W P₁ P₂ Q₁ Q₂ : Type*} [Field K] [NumberField K] [AddCommGroup W] [Module K W]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup Q₁] [Module K Q₁] [AddCommGroup Q₂] [Module K Q₂]
  {ω : LinearMap.BilinForm K W}

theorem FourPieces.adelicPairing₂_adelicCoord_symm [FiniteDimensional K P₂] [FiniteDimensional K Q₂]
    (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) {ξ : K} (hξ : ξ ≠ 0)
    (x y : Fin (finrank K P₂) → 𝔸[K]) :
    F.adelicPairing₂ ((adelicCoord (Module.finBasis K P₂)).symm x)
        ((adelicCoord (FourPieces.a₂PairedBasis hω F hξ)).symm y) =
      algebraMap K 𝔸[K] ξ⁻¹ * ∑ i, x i * y i := by
  have hij : ∀ i j, ω.baseChange 𝔸[K] (F.incP₂.baseChange 𝔸[K] ((1 : 𝔸[K]) ⊗ₜ Module.finBasis K P₂ i))
      (F.incQ₂.baseChange 𝔸[K] ((1 : 𝔸[K]) ⊗ₜ FourPieces.a₂PairedBasis hω F hξ j)) =
      algebraMap K 𝔸[K] ξ⁻¹ * (if i = j then 1 else 0) := by
    intro i j
    have h := F.adelicPairing₂_tmul 1 1 (Module.finBasis K P₂ i) (FourPieces.a₂PairedBasis hω F hξ j)
    rw [FourPieces.adelicPairing₂] at h
    rw [h, FourPieces.a₂_a₂PairedBasis, mul_one, map_mul]
    split_ifs <;> simp
  rw [adelicCoord_symm_apply, adelicCoord_symm_apply]
  simp only [FourPieces.adelicPairing₂, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, hij, mul_ite, mul_zero, mul_one,
    Finset.mem_univ, if_true, Finset.sum_ite_eq']
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring



theorem FourPieces.adelicFourierInversion_P₂ [FiniteDimensional K P₂] [FiniteDimensional K Q₂]
    (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) {ψ : AddChar 𝔸[K] Circle} {ξ : K}
    (hξ : ξ ≠ 0) (hψ : ∀ x, ψ x = adelicChar K (algebraMap K 𝔸[K] ξ * x))
    {f : AdelicPoints K P₂ → ℂ} (hf : f ∈ schwartzBruhatPoints K P₂) (p₂ : AdelicPoints K P₂) :
    ∫ q, (∫ p, f p * (ψ (F.adelicPairing₂ p q) : ℂ) ∂adelicPointsMeasure K P₂) *
        (ψ (-F.adelicPairing₂ p₂ q) : ℂ) ∂adelicPointsMeasure K Q₂ = f p₂ := by
  set b := Module.finBasis K P₂
  set c := FourPieces.a₂PairedBasis hω F hξ
  set G := f ∘ (adelicCoord b).symm with hGdef
  have hG : G ∈ schwartzBruhatPi K (Fin (finrank K P₂)) := (mem_schwartzBruhatPoints_iff b).mp hf
  obtain ⟨x₀, rfl⟩ : ∃ x₀, (adelicCoord b).symm x₀ = p₂ :=
    ⟨adelicCoord b p₂, LinearEquiv.symm_apply_apply _ _⟩
  have hchar : ∀ x y, (ψ (F.adelicPairing₂ ((adelicCoord b).symm x) ((adelicCoord c).symm y)) : ℂ) =
      adelicChar K (∑ i, x i * y i) := by
    intro x y
    rw [hψ, FourPieces.adelicPairing₂_adelicCoord_symm, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hξ, map_one, one_mul]
  have hchar' : ∀ y, (ψ (-F.adelicPairing₂ ((adelicCoord b).symm x₀) ((adelicCoord c).symm y)) : ℂ) =
      adelicChar K (∑ i, y i * (-x₀) i) := by
    intro y
    rw [hψ, FourPieces.adelicPairing₂_adelicCoord_symm, mul_neg, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hξ, map_one,
      one_mul, ← Finset.sum_neg_distrib]
    congr 2
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Pi.neg_apply]; ring
  have hinner : ∀ y, ∫ p, f p * (ψ (F.adelicPairing₂ p ((adelicCoord c).symm y)) : ℂ)
      ∂adelicPointsMeasure K P₂ = adelicFourierPi K G y := by
    intro y
    rw [adelicPointsMeasure_eq_map b, (measurableEmbedding_adelicCoord_symm b).integral_map]
    simp only [hchar]
    rfl
  rw [adelicPointsMeasure_eq_map c, (measurableEmbedding_adelicCoord_symm c).integral_map]
  simp only [hinner, hchar']
  have h := congrFun (adelicFourierPi_adelicFourierPi hG) (-x₀)
  simp only [neg_neg] at h
  exact h

end Adelic

end

end GroundTheory.Heights₂.Theta
end

section
namespace GroundTheory.Heights₂.Theta

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix NumberField NumberField.mixedEmbedding MeasureTheory
  Module
open scoped NumberField.AdeleRing SchwartzMap FourierTransform Classical

noncomputable section

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [NumberField K] {ι κ : Type} [Fintype ι] [Fintype κ]

variable (K ι κ) in

def toEuclidSplit : ((ι ⊕ κ) → mixedSpace K) ≃L[ℝ] (ι → mixedSpace K) × EuclidPi K κ :=
  (LinearEquiv.sumArrowLequivProdArrow ι κ ℝ (mixedSpace K)).toContinuousLinearEquiv.trans
    ((ContinuousLinearEquiv.refl ℝ (ι → mixedSpace K)).prodCongr (toEuclidPi K))

variable (K ι κ) in

def toEuclidSplitConj : ((ι ⊕ κ) → mixedSpace K) ≃L[ℝ] (ι → mixedSpace K) × EuclidPi K κ :=
  (LinearEquiv.sumArrowLequivProdArrow ι κ ℝ (mixedSpace K)).toContinuousLinearEquiv.trans
    ((ContinuousLinearEquiv.refl ℝ (ι → mixedSpace K)).prodCongr (toEuclidPiConj K))



def mixedPartialFourier (φ : ((ι ⊕ κ) → mixedSpace K) → ℂ) (x : (ι ⊕ κ) → mixedSpace K) : ℂ :=
  mixedFourierPi K (fun u : κ → mixedSpace K ↦ φ (Sum.elim (fun i ↦ x (.inl i)) u))
    (fun k ↦ x (.inr k))

def mixedPartialFourierSchwartz (φ : 𝓢((ι ⊕ κ) → mixedSpace K, ℂ)) :
    𝓢((ι ⊕ κ) → mixedSpace K, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidSplitConj K ι κ)
    (partialFourierSndSchwartz
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidSplit K ι κ).symm φ))

theorem mixedPartialFourierSchwartz_apply (φ : 𝓢((ι ⊕ κ) → mixedSpace K, ℂ)) :
    ⇑(mixedPartialFourierSchwartz φ) = mixedPartialFourier (φ : ((ι ⊕ κ) → mixedSpace K) → ℂ) := by
  funext x
  rw [mixedPartialFourier, mixedFourierPi_eq]
  rfl

def finitePartialFourier (g : ((ι ⊕ κ) → 𝔸ᶠ[K]) → ℂ) (x : (ι ⊕ κ) → 𝔸ᶠ[K]) : ℂ :=
  finiteFourierPi K (fun t : κ → 𝔸ᶠ[K] ↦ g (Sum.elim (fun i ↦ x (.inl i)) t)) (fun k ↦ x (.inr k))

theorem finitePartialFourier_finiteTensor (h : (ι ⊕ κ) → 𝔸ᶠ[K] → ℂ) :
    finitePartialFourier (finiteTensor h) =
      finiteTensor (Sum.elim (fun i ↦ h (.inl i)) fun k ↦ finiteFourier K (h (.inr k))) := by
  funext x
  have hsplit : (fun t : κ → 𝔸ᶠ[K] ↦ finiteTensor h (Sum.elim (fun i ↦ x (.inl i)) t)) =
      (∏ i, h (.inl i) (x (.inl i))) • finiteTensor fun k ↦ h (.inr k) := by
    funext t
    simp only [finiteTensor, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
      smul_eq_mul]
  rw [finitePartialFourier, hsplit, finiteFourierPi_smul, finiteFourierPi_finiteTensor]
  simp only [finiteTensor, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
    smul_eq_mul]

theorem finitePartialFourier_add {g₁ g₂ : ((ι ⊕ κ) → 𝔸ᶠ[K]) → ℂ}
    (h₁ : g₁ ∈ finiteSchwartzBruhatPi K) (h₂ : g₂ ∈ finiteSchwartzBruhatPi K) :
    finitePartialFourier (g₁ + g₂) = finitePartialFourier g₁ + finitePartialFourier g₂ := by
  funext x
  have e := finiteFourierPi_add
    (integrable_of_mem_finiteSchwartzBruhatPi (finiteSchwartzBruhatPi_sumElim_mem h₁ fun i ↦ x (.inl i)))
    (integrable_of_mem_finiteSchwartzBruhatPi (finiteSchwartzBruhatPi_sumElim_mem h₂ fun i ↦ x (.inl i)))
  exact congrFun e _

theorem finitePartialFourier_smul (c : ℂ) (g : ((ι ⊕ κ) → 𝔸ᶠ[K]) → ℂ) :
    finitePartialFourier (c • g) = c • finitePartialFourier g := by
  funext x
  exact congrFun (finiteFourierPi_smul (K := K) c _) _

theorem finitePartialFourier_mem {g : ((ι ⊕ κ) → 𝔸ᶠ[K]) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi K) :
    finitePartialFourier g ∈ finiteSchwartzBruhatPi K := by
  have hsub := (finiteSchwartzBruhatPi_eq_span (K := K) (ι := ι ⊕ κ)).ge
  rw [finiteSchwartzBruhatPi_eq_span] at hg
  induction hg using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨J, a⟩, rfl⟩ := hf
    rw [finitePartialFourier_finiteTensor]
    refine finiteTensor_mem fun s ↦ ?_
    cases s with
    | inl i => exact cosetIndicator_mem_finiteSchwartzBruhat J (a (.inl i))
    | inr k =>
      exact finiteFourier_mem_finiteSchwartzBruhat (cosetIndicator_mem_finiteSchwartzBruhat J _)
  | zero =>
    have : finitePartialFourier (0 : ((ι ⊕ κ) → 𝔸ᶠ[K]) → ℂ) = 0 := by
      simpa using finitePartialFourier_smul (K := K) (ι := ι) (κ := κ) 0 0
    rw [this]
    exact zero_mem _
  | add f₁ f₂ h₁ h₂ ih₁ ih₂ =>
    rw [finitePartialFourier_add (hsub h₁) (hsub h₂)]
    exact add_mem ih₁ ih₂
  | smul c f _ ih =>
    rw [finitePartialFourier_smul]
    exact Submodule.smul_mem _ c ih

def partialFourierPi (F : ((ι ⊕ κ) → 𝔸[K]) → ℂ) (z : (ι ⊕ κ) → 𝔸[K]) : ℂ :=
  adelicFourierPi K (fun y : κ → 𝔸[K] ↦ F (Sum.elim (fun i ↦ z (.inl i)) y)) (fun k ↦ z (.inr k))

theorem partialFourierPi_sumElim (F : ((ι ⊕ κ) → 𝔸[K]) → ℂ) (a : ι → 𝔸[K]) (η : κ → 𝔸[K]) :
    partialFourierPi F (Sum.elim a η) = adelicFourierPi K (fun y ↦ F (Sum.elim a y)) η := rfl

theorem partialFourierPi_schwartzBruhatTensorPi (φ : 𝓢((ι ⊕ κ) → mixedSpace K, ℂ))
    (g : ((ι ⊕ κ) → 𝔸ᶠ[K]) → ℂ) :
    partialFourierPi (schwartzBruhatTensorPi φ g) =
      schwartzBruhatTensorPi (mixedPartialFourierSchwartz φ) (finitePartialFourier g) := by
  funext z
  have hslice : (fun y : κ → 𝔸[K] ↦ schwartzBruhatTensorPi φ g (Sum.elim (fun i ↦ z (.inl i)) y)) =
      schwartzBruhatTensorPi (schwartzMapSliceSumElim (infPartPi fun i ↦ z (.inl i)) φ)
        (fun t ↦ g (Sum.elim (finPartPi fun i ↦ z (.inl i)) t)) := by
    funext y
    simp only [schwartzBruhatTensorPi, infPartPi_sumElim, finPartPi_sumElim,
      schwartzMapSliceSumElim_apply]
  rw [partialFourierPi, hslice, adelicFourierPi_schwartzBruhatTensorPi, schwartzBruhatTensorPi,
    schwartzBruhatTensorPi, mixedPartialFourierSchwartz_apply, mixedFourierPiSchwartz_apply]
  rfl

theorem integrable_partialFourierPi_slice {F : ((ι ⊕ κ) → 𝔸[K]) → ℂ}
    (hF : F ∈ schwartzBruhatPi K (ι ⊕ κ)) (a : ι → 𝔸[K]) :
    Integrable (fun y : κ → 𝔸[K] ↦ F (Sum.elim a y)) (adeleMeasurePi K) :=
  integrable_of_mem_schwartzBruhatPi (schwartzBruhatPi_sumElim_mem hF a)

theorem partialFourierPi_mem {F : ((ι ⊕ κ) → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhatPi K (ι ⊕ κ)) :
    partialFourierPi F ∈ schwartzBruhatPi K (ι ⊕ κ) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    rw [partialFourierPi_schwartzBruhatTensorPi]
    exact schwartzBruhatTensorPi_mem _ (finitePartialFourier_mem hg)
  | zero =>
    have : partialFourierPi (0 : ((ι ⊕ κ) → 𝔸[K]) → ℂ) = 0 := by
      funext z
      simp [partialFourierPi, adelicFourierPi]
    rw [this]
    exact zero_mem _
  | add G H hG hH ihG ihH =>
    have : partialFourierPi (G + H) = partialFourierPi G + partialFourierPi H := by
      funext z
      exact congrFun (adelicFourierPi_add (integrable_partialFourierPi_slice hG _)
        (integrable_partialFourierPi_slice hH _)) _
    rw [this]
    exact add_mem ihG ihH
  | smul c G _ ih =>
    have : partialFourierPi (c • G) = c • partialFourierPi G := by
      funext z
      exact congrFun (adelicFourierPi_smul (K := K) c _) _
    rw [this]
    exact Submodule.smul_mem _ c ih

theorem algebraMap_sumElim (c : ι → K) (η : κ → K) :
    (fun s ↦ algebraMap K 𝔸[K] ((Sum.elim c η : (ι ⊕ κ) → K) s)) =
      Sum.elim (fun i ↦ algebraMap K 𝔸[K] (c i)) (fun k ↦ algebraMap K 𝔸[K] (η k)) := by
  funext s
  cases s <;> rfl

theorem tsum_sumElim {f : ((ι ⊕ κ) → K) → ℂ} (hf : Summable fun ξ ↦ ‖f ξ‖) :
    ∑' ξ, f ξ = ∑' c : ι → K, ∑' η : κ → K, f (Sum.elim c η) := by
  let e := Equiv.sumArrowEquivProdArrow ι κ K
  have h1 : Summable fun p : (ι → K) × (κ → K) ↦ f (e.symm p) :=
    (e.symm.summable_iff.mpr hf.of_norm)
  rw [← e.symm.tsum_eq, h1.tsum_prod' fun c ↦ h1.prod_factor c]
  rfl

theorem tsum_partialFourierPi {F : ((ι ⊕ κ) → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhatPi K (ι ⊕ κ)) :
    ∑' ξ : (ι ⊕ κ) → K, partialFourierPi F (fun s ↦ algebraMap K 𝔸[K] (ξ s)) =
      ∑' ξ : (ι ⊕ κ) → K, F (fun s ↦ algebraMap K 𝔸[K] (ξ s)) := by
  rw [tsum_sumElim (poisson_of_mem_schwartzBruhatPi (partialFourierPi_mem hF)).1,
    tsum_sumElim (poisson_of_mem_schwartzBruhatPi hF).1]
  refine tsum_congr fun c ↦ ?_
  simp only [algebraMap_sumElim, partialFourierPi_sumElim]
  exact ((poisson_of_mem_schwartzBruhatPi
    (schwartzBruhatPi_sumElim_mem hF fun i ↦ algebraMap K 𝔸[K] (c i))).2.2).symm

end

end GroundTheory.Heights₂.Theta
end
