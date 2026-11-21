import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenOfPoincareLelongHyperplane
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LogInt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenCoord
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HessCRestrictThm
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

section
namespace ReciprocityTheory.AnForm.A

open MeasureTheory Filter Topology

open scoped ContDiff

noncomputable section

theorem fderiv2_comp_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → ℝ) (P : F →L[ℝ] E) (hg : ContDiff ℝ 2 g)
    (z a b : F) :
    fderiv ℝ (fderiv ℝ (g ∘ P)) z a b = fderiv ℝ (fderiv ℝ g) (P z) (P a) (P b) := by
  have h1 := iteratedFDeriv_two_apply (𝕜 := ℝ) (g ∘ P) z ![a, b]
  have h2 := iteratedFDeriv_two_apply (𝕜 := ℝ) g (P z) ![P a, P b]
  rw [P.iteratedFDeriv_comp_right hg z le_rfl] at h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  rw [← h1, ← h2]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i; fin_cases i <;> rfl

def gReg (ε : ℝ) (ζ : ℂ) : ℝ := (1 / 2) * Real.log (‖ζ‖ ^ 2 + ε)

theorem gReg_hasFDerivAt {ε : ℝ} (hε : 0 < ε) (ζ : ℂ) :
    HasFDerivAt (gReg ε) ((‖ζ‖ ^ 2 + ε)⁻¹ • innerSL ℝ ζ) ζ := by
  have hs : ‖ζ‖ ^ 2 + ε ≠ 0 := by positivity
  have h1 := ((hasStrictFDerivAt_norm_sq ζ).hasFDerivAt.add_const ε).log hs
  have h2 : HasFDerivAt (gReg ε) ((1 / 2 : ℝ) • ((‖ζ‖ ^ 2 + ε)⁻¹ • (2 • innerSL ℝ ζ))) ζ :=
    h1.const_mul (1 / 2 : ℝ)
  refine h2.congr_fderiv ?_
  module

theorem fderiv_gReg {ε : ℝ} (hε : 0 < ε) :
    fderiv ℝ (gReg ε) = fun ζ => (‖ζ‖ ^ 2 + ε)⁻¹ • innerSL ℝ ζ := by
  funext ζ; exact (gReg_hasFDerivAt hε ζ).fderiv

theorem second_fderiv_regularized_log {ε : ℝ} (hε : 0 < ε) (ζ a b : ℂ) :
    fderiv ℝ (fderiv ℝ (gReg ε)) ζ a b =
      (‖ζ‖ ^ 2 + ε)⁻¹ * inner ℝ a b - 2 * inner ℝ ζ a * inner ℝ ζ b / (‖ζ‖ ^ 2 + ε) ^ 2 := by
  have hs : ‖ζ‖ ^ 2 + ε ≠ 0 := by positivity
  have hq : HasFDerivAt (fun y : ℂ => ‖y‖ ^ 2 + ε) (2 • innerSL ℝ ζ) ζ :=
    (hasStrictFDerivAt_norm_sq ζ).hasFDerivAt.add_const ε
  have hc := (hasFDerivAt_inv (𝕜 := ℝ) hs).comp ζ hq
  have hL : HasFDerivAt (fun y : ℂ => innerSL ℝ y) (innerSL ℝ) ζ :=
    (innerSL ℝ).hasFDerivAt
  have h := hc.smul hL
  have h' : HasFDerivAt (fun y : ℂ => (‖y‖ ^ 2 + ε)⁻¹ • innerSL ℝ y) _ ζ := h
  rw [fderiv_gReg hε, h'.fderiv]
  have hi : ∀ x y : ℂ, (innerSL ℝ x) y = x.re * y.re + x.im * y.im := fun x y => by
    rw [innerSL_apply_apply]; simp [Complex.inner]; ring
  simp [hi]
  field_simp
  ring

theorem gReg_contDiff {ε : ℝ} (hε : 0 < ε) {m : WithTop ℕ∞} : ContDiff ℝ m (gReg ε) := by
  unfold gReg
  refine contDiff_const.mul ((contDiff_norm_sq ℝ).add contDiff_const |>.log fun ζ => ?_)
  positivity

def cReg (ε : ℝ) (ζ : ℂ) : ℝ := ε / (2 * (‖ζ‖ ^ 2 + ε) ^ 2)

theorem hessC_gReg {n : ℕ} {ε : ℝ} (hε : 0 < ε) (i : Fin (n + 1)) (z : Fin (n + 1) → ℂ) :
    hessC (fun y : Fin (n + 1) → ℂ => gReg ε (y i)) z =
      ((cReg ε (z i) : ℝ) : ℂ) • Matrix.single i i 1 := by
  let P : (Fin (n + 1) → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℂ) i
  have hf : (fun y : Fin (n + 1) → ℂ => gReg ε (y i)) = gReg ε ∘ P := rfl
  have hP : ∀ y, P y = y i := fun y => rfl
  ext a b
  simp only [hessC, hf, fderiv2_comp_clm _ P (gReg_contDiff hε), hP]
  by_cases ha : a = i
  · by_cases hb : b = i
    · rw [ha, hb]
      have hs : ‖z i‖ ^ 2 + ε ≠ 0 := by positivity
      have hn : ‖z i‖ ^ 2 = (z i).re ^ 2 + (z i).im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      have h1 : fderiv ℝ (fderiv ℝ (gReg ε)) (z i) 1 1 +
          fderiv ℝ (fderiv ℝ (gReg ε)) (z i) Complex.I Complex.I = 4 * cReg ε (z i) := by
        rw [second_fderiv_regularized_log hε, second_fderiv_regularized_log hε]
        simp only [Complex.inner, cReg, hn]
        simp
        field_simp
        ring
      have h2 : fderiv ℝ (fderiv ℝ (gReg ε)) (z i) 1 Complex.I -
          fderiv ℝ (fderiv ℝ (gReg ε)) (z i) Complex.I 1 = 0 := by
        rw [second_fderiv_regularized_log hε, second_fderiv_regularized_log hε]
        simp only [Complex.inner]
        simp
        ring
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      rw [h1, h2]
      simp
    · simp [Pi.single_apply, Ne.symm hb]
  · simp [Pi.single_apply, Ne.symm ha]

theorem contDiff_of_contDiffOn_zero_off {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U K : Set E} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → F} {m : WithTop ℕ∞} (hf : ContDiffOn ℝ m f U)
    (h0 : ∀ z ∉ K, f z = 0) : ContDiff ℝ m f := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : z ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hz)
  · have hzK : z ∈ Kᶜ := fun h => hz (hKU h)
    refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [hK.isOpen_compl.mem_nhds hzK] with y hy using h0 y hy

theorem hessC_eq_zero_of_notMem {D : ℕ} {v : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (hz : z ∉ tsupport v) : hessC v z = 0 := by
  have h1 : v =ᶠ[𝓝 z] fun _ => 0 := (notMem_tsupport_iff_eventuallyEq).1 hz
  have h2 : fderiv ℝ (fderiv ℝ v) z = 0 := by
    rw [h1.fderiv.fderiv_eq]
    simp
  ext i j
  simp [hessC, h2]

theorem hessC_contDiffOn {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    {m : ℕ} (hφ : ContDiffOn ℝ (m + 2) φ U) (i j : Fin D) :
    ContDiffOn ℝ m (fun z => hessC φ z i j) U := by
  have h1 : ContDiffOn ℝ (m + 1) (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_cast)
  have h2 : ContDiffOn ℝ m (fderiv ℝ (fderiv ℝ φ)) U := h1.fderiv_of_isOpen hU le_rfl
  have hH : ∀ a b : Fin D → ℂ, ContDiffOn ℝ m (fun z => fderiv ℝ (fderiv ℝ φ) z a b) U :=
    fun a b => (h2.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hC : ∀ g : (Fin D → ℂ) → ℝ, ContDiffOn ℝ m g U → ContDiffOn ℝ m (fun z => (g z : ℂ)) U :=
    fun g hg => Complex.ofRealCLM.contDiff.comp_contDiffOn hg
  simp only [hessC]
  refine ContDiffOn.div_const (ContDiffOn.add (hC _ ((hH _ _).add (hH _ _)))
    (contDiffOn_const.mul (hC _ ((hH _ _).sub (hH _ _))))) _

theorem mdisc_contDiffOn {D : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin D → E → Matrix (Fin D) (Fin D) ℂ) {s : Set E} {m : WithTop ℕ∞}
    (hA : ∀ k i j, ContDiffOn ℝ m (fun z => A k z i j) s) :
    ContDiffOn ℝ m (fun z => mdisc (fun k => A k z)) s := by
  simp only [mdisc, Matrix.det_apply', Matrix.sum_apply]
  refine contDiffOn_const.mul (ContDiffOn.sum fun S _ => contDiffOn_const.mul
    (ContDiffOn.sum fun σ _ => contDiffOn_const.mul
      (contDiffOn_prod fun i _ => ContDiffOn.sum fun k _ => hA k _ _)))

theorem ae_coord_ne_zero {n : ℕ} (i : Fin (n + 1)) : ∀ᵐ z : Fin (n + 1) → ℂ ∂volume, z i ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rw [volume_pi]
  exact Measure.pi_hyperplane _ i 0

theorem gReg_abs_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {ζ : ℂ} (hζ : ζ ≠ 0) :
    |gReg ε ζ| ≤ |Real.log ‖ζ‖| + (1 / 2) * Real.log (‖ζ‖ ^ 2 + 1) := by
  have hr : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
  have hr2 : 0 < ‖ζ‖ ^ 2 := by positivity
  have hl1 : 0 ≤ Real.log (‖ζ‖ ^ 2 + 1) := Real.log_nonneg (by linarith)
  have hup : Real.log (‖ζ‖ ^ 2 + ε) ≤ Real.log (‖ζ‖ ^ 2 + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlo : Real.log (‖ζ‖ ^ 2) ≤ Real.log (‖ζ‖ ^ 2 + ε) := Real.log_le_log hr2 (by linarith)
  have h2 : Real.log (‖ζ‖ ^ 2) = 2 * Real.log ‖ζ‖ := by rw [Real.log_pow]; push_cast; ring
  unfold gReg
  rcases le_or_gt 0 (Real.log (‖ζ‖ ^ 2 + ε)) with h | h
  · rw [abs_of_nonneg (by linarith)]
    have := abs_nonneg (Real.log ‖ζ‖)
    linarith
  · rw [abs_of_neg (by linarith)]
    have := neg_abs_le (Real.log ‖ζ‖)
    linarith

theorem tendsto_gReg {ζ : ℂ} (hζ : ζ ≠ 0) :
    Tendsto (fun k : ℕ => gReg (1 / ((k : ℝ) + 1)) ζ) atTop (𝓝 (Real.log ‖ζ‖)) := by
  have hr2 : 0 < ‖ζ‖ ^ 2 := by have := norm_pos_iff.2 hζ; positivity
  have h1 : Tendsto (fun k : ℕ => ‖ζ‖ ^ 2 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (‖ζ‖ ^ 2 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at h1
  have h2 := ((Real.continuousAt_log hr2.ne').tendsto.comp h1).const_mul (1 / 2 : ℝ)
  have h3 : (1 / 2 : ℝ) * Real.log (‖ζ‖ ^ 2) = Real.log ‖ζ‖ := by
    rw [Real.log_pow]; push_cast; ring
  rw [h3] at h2
  exact h2

theorem tendsto_integral_gReg {n : ℕ} (i : Fin (n + 1)) (F : (Fin (n + 1) → ℂ) → ℝ) (hF : Continuous F)
    (hFc : HasCompactSupport F)
    (hlog : LocallyIntegrable (fun z : Fin (n + 1) → ℂ => Real.log ‖z i‖) volume) :
    Tendsto (fun k : ℕ => ∫ z, gReg (1 / ((k : ℝ) + 1)) (z i) * F z) atTop
      (𝓝 (∫ z, Real.log ‖z i‖ * F z)) := by
  have hε0 : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hε1 : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := fun k => by
    rw [div_le_one (by positivity)]; have := k.cast_nonneg (α := ℝ); linarith
  refine tendsto_integral_of_dominated_convergence
    (fun z => |Real.log ‖z i‖| * |F z| + (1 / 2) * Real.log (‖z i‖ ^ 2 + 1) * |F z|)
    (fun k => (((gReg_contDiff (hε0 k) (m := 0)).continuous.comp (continuous_apply i)).mul
      hF).aestronglyMeasurable) ?_ ?_ ?_
  · refine Integrable.add ?_ ?_
    · have := (hlog.integrable_smul_left_of_hasCompactSupport hF hFc).abs
      refine this.congr (Eventually.of_forall fun z => ?_)
      simp only [smul_eq_mul, abs_mul]; ring
    · refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · have hc : Continuous (fun z : Fin (n + 1) → ℂ => Real.log (‖z i‖ ^ 2 + 1)) :=
          Continuous.log (by fun_prop) fun z =>
            (add_pos_of_nonneg_of_pos (sq_nonneg _) one_pos).ne'
        exact (continuous_const.mul hc).mul hF.abs
      · exact hFc.abs.mul_left
  · intro k
    filter_upwards [ae_coord_ne_zero i] with z hz
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, ← add_mul]
    exact mul_le_mul_of_nonneg_right (gReg_abs_le (hε0 k) (hε1 k) hz) (abs_nonneg _)
  · filter_upwards [ae_coord_ne_zero i] with z hz
    exact (tendsto_gReg hz).mul_const _

variable {n : ℕ}

theorem hessC_cons (f : (Fin (n + 1) → ℂ) → ℝ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    (z : Fin (n + 1) → ℂ) :
    (fun k => hessC ((Fin.cons f φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z) =
      Fin.cons (hessC f z) (fun k => hessC (φ k) z) := by
  funext k; refine Fin.cases rfl (fun k => rfl) k

theorem mdisc_cons_smul_single (i : Fin (n + 1)) (c : ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons (c • Matrix.single i i 1) B :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      c * ((1 / ((n : ℂ) + 1)) * mdisc (fun k => (B k).submatrix i.succAbove i.succAbove)) := by
  have h := mdisc_update_smul
    (Fin.cons (Matrix.single i i 1) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 c
    (Matrix.single i i 1)
  rw [Fin.update_cons_zero, Fin.update_cons_zero] at h
  rw [h]
  have h2 := mixedCof_diag B i
  simp only [mixedCof] at h2
  rw [h2]
  push_cast
  ring

theorem mdisc_cons_zero (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons 0 B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 0 := by
  have h := mdisc_update_smul
    (Fin.cons 0 B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 0 0
  simpa [Fin.update_cons_zero] using h

def kDens (n : ℕ) : ℝ := ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1)

def minorDens (i : Fin (n + 1)) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ) : ℝ :=
  (mdisc (fun k => (hessC (φ k) z).submatrix i.succAbove i.succAbove)).re

theorem maDens_cons_gReg {ε : ℝ} (hε : 0 < ε) (i : Fin (n + 1))
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ) :
    maDens (Fin.cons (fun y => gReg ε (y i)) φ) z =
      kDens n * cReg ε (z i) * (1 / ((n : ℝ) + 1)) * minorDens i φ z := by
  unfold maDens
  rw [hessC_cons, hessC_gReg hε, mdisc_cons_smul_single]
  have h1 : (1 / ((n : ℂ) + 1)) = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [h1, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  simp only [kDens, minorDens]
  ring
theorem maDens_cons_eq_zero {v : (Fin (n + 1) → ℂ) → ℝ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    {z : Fin (n + 1) → ℂ} (hz : z ∉ tsupport v) : maDens (Fin.cons v φ) z = 0 := by
  unfold maDens
  rw [hessC_cons, hessC_eq_zero_of_notMem hz, mdisc_cons_zero]
  simp

def psiRef (n : ℕ) : Fin n → (Fin (n + 1) → ℂ) → ℝ := fun _ z => ∑ i, Complex.normSq (z i)

theorem psiRef_contDiff (k : Fin n) {m : WithTop ℕ∞} : ContDiff ℝ m (psiRef n k) := by
  unfold psiRef
  simp only [Complex.normSq_eq_norm_sq]
  exact ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i)

theorem minorDens_psiRef (i : Fin (n + 1)) (z : Fin (n + 1) → ℂ) : minorDens i (psiRef n) z = 1 := by
  have hp : ∀ k, hessC (psiRef n k) z = 1 := fun k => hessC_sum_normSq z
  simp only [minorDens, hp]
  rw [Matrix.submatrix_one _ (Fin.succAbove_right_injective), mdisc_const]
  simp

theorem cdo_of_infty {D : ℕ} {f : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)}
    (h : ContDiffOn ℝ ∞ f U) (m : ℕ) : ContDiffOn ℝ (m + 2) f U := by
  exact_mod_cast contDiffOn_infty.1 h (m + 2)

theorem cdo_of_three {D : ℕ} {f : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)}
    (h : ContDiff ℝ 3 f) : ContDiffOn ℝ ((1 : ℕ) + 2) f U := by
  have e : ((1 : ℕ) : WithTop ℕ∞) + 2 = 3 := by norm_num
  rw [e]; exact h.contDiffOn

theorem contDiffOn_re' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℂ}
    {s : Set E} {m : WithTop ℕ∞} (h : ContDiffOn ℝ m g s) :
    ContDiffOn ℝ m (fun z => (g z).re) s :=
  Complex.reCLM.contDiff.comp_contDiffOn h

theorem minorDens_contDiffOn (i : Fin (n + 1)) {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U)
    {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hφ : ∀ k, ContDiffOn ℝ ∞ (φ k) U) (m : ℕ) :
    ContDiffOn ℝ m (minorDens i φ) U := by
  unfold minorDens
  refine contDiffOn_re' ?_
  refine mdisc_contDiffOn (fun k z => (hessC (φ k) z).submatrix i.succAbove i.succAbove)
    fun k a b => ?_
  exact hessC_contDiffOn hU (cdo_of_infty (hφ k) m) (i.succAbove a) (i.succAbove b)

theorem maDens_cons_continuous {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U)
    {f : (Fin (n + 1) → ℂ) → ℝ} (hf : ContDiff ℝ 3 f) (hfU : tsupport f ⊆ U)
    {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hφ : ∀ k, ContDiffOn ℝ ∞ (φ k) U) :
    Continuous (maDens (Fin.cons f φ)) := by
  have h : ContDiffOn ℝ (1 : ℕ) (maDens (Fin.cons f φ)) U := by
    unfold maDens
    refine contDiffOn_const.mul (contDiffOn_re' ?_)
    refine mdisc_contDiffOn (fun k z => hessC ((Fin.cons f φ : Fin (n + 1) → _) k) z)
      fun k i j => ?_
    cases k using Fin.cases with
    | zero => simpa using hessC_contDiffOn hU (cdo_of_three hf) i j
    | succ k => simpa using hessC_contDiffOn hU (cdo_of_infty (hφ k) 1) i j
  exact (contDiff_of_contDiffOn_zero_off hU (isClosed_tsupport f) hfU h
    (fun z hz => maDens_cons_eq_zero φ hz)).continuous

theorem maDens_cons_hasCompactSupport {f : (Fin (n + 1) → ℂ) → ℝ} (hf : HasCompactSupport f)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) : HasCompactSupport (maDens (Fin.cons f φ)) := by
  refine HasCompactSupport.intro hf.isCompact fun z hz => maDens_cons_eq_zero φ hz

def hDens (i : Fin (n + 1)) (v : (Fin (n + 1) → ℂ) → ℝ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    (z : Fin (n + 1) → ℂ) : ℝ :=
  v z * minorDens i φ z

theorem hDens_props (i : Fin (n + 1)) {U : Set (Fin (n + 1) → ℂ)} {v : (Fin (n + 1) → ℂ) → ℝ}
    {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hp : PoincareLelongData U v φ) :
    ContDiff ℝ 3 (hDens i v φ) ∧ HasCompactSupport (hDens i v φ) := by
  obtain ⟨hU, hv, hvc, hvU, hφ⟩ := hp
  refine ⟨contDiff_of_contDiffOn_zero_off hU (isClosed_tsupport v) hvU
    (hv.contDiffOn.mul (minorDens_contDiffOn i hU hφ 3)) fun z hz => ?_, hvc.mul_right⟩
  simp [hDens, image_eq_zero_of_notMem_tsupport hz]

end

end ReciprocityTheory.AnForm.A
end

section
namespace ReciprocityTheory.AnForm.A

open MeasureTheory Filter Topology

open scoped ContDiff

noncomputable section

variable {n : ℕ}

theorem integral_gReg_eq (i : Fin (n + 1)) {U : Set (Fin (n + 1) → ℂ)}
    {v : (Fin (n + 1) → ℂ) → ℝ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hp : PoincareLelongData U v φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∫ z, gReg ε (z i) * densV v φ z =
      ∫ z, gReg ε (z i) * maDens (Fin.cons (hDens i v φ) (psiRef n)) z := by
  obtain ⟨hh, hhc⟩ := hDens_props i hp
  obtain ⟨hU, hv, hvc, hvU, hφ⟩ := hp
  have hg : ContDiff ℝ 3 (fun y : Fin (n + 1) → ℂ => gReg ε (y i)) :=
    (gReg_contDiff hε).comp (contDiff_apply ℝ ℂ i)
  have h1 := (parts_thm n φ v (fun y => gReg ε (y i)) U
    ⟨hU, hv.contDiffOn, hvc, hvU, hg.contDiffOn,
      fun k => by exact_mod_cast contDiffOn_infty.1 (hφ k) 3⟩).2.2.2.2
  have h2 := (parts_thm n (psiRef n) (hDens i v φ) (fun y => gReg ε (y i)) Set.univ
    ⟨isOpen_univ, hh.contDiffOn, hhc, Set.subset_univ _, hg.contDiffOn,
      fun k => (psiRef_contDiff k).contDiffOn⟩).2.2.2.2
  simp only [maInt, Measure.restrict_univ] at h1 h2
  have e1 : ∫ z in U, gReg ε (z i) * maDens (Fin.cons v φ) z =
      ∫ z, gReg ε (z i) * maDens (Fin.cons v φ) z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [maDens_cons_eq_zero φ (fun h => hz (hvU h)), mul_zero]
  have e2 : ∫ z in U, v z * maDens (Fin.cons (fun y => gReg ε (y i)) φ) z =
      ∫ z, v z * maDens (Fin.cons (fun y => gReg ε (y i)) φ) z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hvU h)), zero_mul]
  rw [e1, e2] at h1
  unfold densV
  rw [h1, h2]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [maDens_cons_gReg hε, minorDens_psiRef, hDens]
  ring

theorem integral_log_densV_eq (i : Fin (n + 1)) {U : Set (Fin (n + 1) → ℂ)}
    {v : (Fin (n + 1) → ℂ) → ℝ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hp : PoincareLelongData U v φ) :
    ∫ z, Real.log ‖z i‖ * densV v φ z =
      ∫ z, Real.log ‖z i‖ * maDens (Fin.cons (hDens i v φ) (psiRef n)) z := by
  obtain ⟨hh, hhc⟩ := hDens_props i hp
  have hlog := logCoordLocInt_thm (n + 1) i
  have t1 := tendsto_integral_gReg i (densV v φ)
    (maDens_cons_continuous hp.1 hp.2.1 hp.2.2.2.1 hp.2.2.2.2)
    (maDens_cons_hasCompactSupport hp.2.2.1 φ) hlog
  have t2 := tendsto_integral_gReg i (maDens (Fin.cons (hDens i v φ) (psiRef n)))
    (maDens_cons_continuous isOpen_univ hh (Set.subset_univ _)
      fun k => (psiRef_contDiff k).contDiffOn)
    (maDens_cons_hasCompactSupport hhc _) hlog
  exact tendsto_nhds_unique t1 (t2.congr fun k => (integral_gReg_eq i hp (by positivity)).symm)

theorem maDens_cons_psiRef (h : (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ) :
    maDens (Fin.cons h (psiRef n)) z = kDens n *
      (∑ j, ∑ k, hessC h z j k *
        mixedCof (fun _ : Fin n => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) j k).re := by
  unfold maDens
  rw [hessC_cons]
  have hp : (fun k => hessC (psiRef n k) z) = fun _ => 1 := funext fun k => hessC_sum_normSq z
  rw [hp, mdisc_cons_eq_sum]
  unfold kDens
  rfl

theorem mixedCof_one_diag (i : Fin (n + 1)) :
    mixedCof (fun _ : Fin n => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) i i =
      ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by
  rw [mixedCof_diag]
  have h1 : (fun _ : Fin n => ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).submatrix i.succAbove i.succAbove) =
      fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) := by
    funext _
    exact Matrix.submatrix_one _ Fin.succAbove_right_injective
  rw [h1, mdisc_const, Matrix.det_one, mul_one]
  push_cast
  ring

theorem re_hessC_diag {D : ℕ} (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (j : Fin D) :
    (hessC f z j j).re = levi f z (Pi.single j 1) := by
  simp [hessC, levi, Complex.div_ofNat_re]

def fTerm (i : Fin (n + 1)) (h : (Fin (n + 1) → ℂ) → ℝ) (j k : Fin (n + 1))
    (z : Fin (n + 1) → ℂ) : ℝ :=
  ((Real.log ‖z i‖ : ℂ) * (hessC h z j k *
    mixedCof (fun _ : Fin n => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) j k)).re

theorem fTerm_props (i : Fin (n + 1)) {h : (Fin (n + 1) → ℂ) → ℝ} (hh : ContDiff ℝ 2 h)
    (hhc : HasCompactSupport h) (j k : Fin (n + 1)) :
    Integrable (fTerm i h j k) ∧ ∫ z, fTerm i h j k z =
      if j = i ∧ k = i then
        (Real.pi / 2) * (1 / ((n : ℝ) + 1)) * ∫ w, h (Fin.insertNth i 0 w)
      else 0 := by
  have hG := greenCoord_thm n i h hh hhc
  by_cases hjk : j = i ∧ k = i
  · obtain ⟨hj, hk⟩ := hjk
    rw [hj, hk]
    have e : ∀ z, fTerm i h i i z =
        (Real.pi / 2) * (1 / ((n : ℝ) + 1)) * (Real.log ‖z i‖ * ddcCoordDens i h z) := by
      intro z
      simp only [fTerm, mixedCof_one_diag, Complex.re_ofReal_mul, Complex.re_mul_ofReal,
        re_hessC_diag, ddcCoordDens]
      field_simp
    have e' : fTerm i h i i = fun z =>
        (Real.pi / 2) * (1 / ((n : ℝ) + 1)) * (Real.log ‖z i‖ * ddcCoordDens i h z) := funext e
    rw [e', if_pos ⟨rfl, rfl⟩, integral_const_mul, hG.2]
    exact ⟨hG.1.const_mul _, rfl⟩
  · have hne : (j, k) ≠ (i, i) := fun h' => hjk ⟨(Prod.mk.inj h').1, (Prod.mk.inj h').2⟩
    have hm := greenMixed_thm n i j k h hh hhc hne
    set M := mixedCof (fun _ : Fin n => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) j k
    have hi : Integrable (fun z : Fin (n + 1) → ℂ =>
        (Real.log ‖z i‖ : ℂ) * (hessC h z j k * M)) := by
      simpa [mul_assoc] using hm.1.mul_const M
    refine ⟨Complex.reCLM.integrable_comp hi, ?_⟩
    rw [if_neg hjk]
    have := Complex.reCLM.integral_comp_comm hi
    simp only [Complex.reCLM_apply] at this
    simp only [fTerm]
    rw [this]
    simp_rw [← mul_assoc]
    rw [integral_mul_const, hm.2]
    simp

theorem integral_log_maDens_psiRef (i : Fin (n + 1)) {h : (Fin (n + 1) → ℂ) → ℝ}
    (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) :
    ∫ z, Real.log ‖z i‖ * maDens (Fin.cons h (psiRef n)) z =
      kDens n * ((Real.pi / 2) * (1 / ((n : ℝ) + 1)) * ∫ w, h (Fin.insertNth i 0 w)) := by
  classical
  have hsplit : (fun z => Real.log ‖z i‖ * maDens (Fin.cons h (psiRef n)) z) =
      fun z => kDens n * ∑ j, ∑ k, fTerm i h j k z := by
    funext z
    rw [maDens_cons_psiRef, Complex.re_sum]
    simp only [fTerm, Complex.re_ofReal_mul, Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hint : ∀ j, ∫ z, ∑ k, fTerm i h j k z = ∑ k, ∫ z, fTerm i h j k z := fun j =>
    integral_finset_sum _ fun k _ => (fTerm_props i hh hhc j k).1
  have hval : ∀ j k, ∫ z, fTerm i h j k z = if j = i ∧ k = i then
      (Real.pi / 2) * (1 / ((n : ℝ) + 1)) * ∫ w, h (Fin.insertNth i 0 w) else 0 :=
    fun j k => (fTerm_props i hh hhc j k).2
  rw [hsplit, integral_const_mul, integral_finset_sum _ fun j _ =>
    integrable_finset_sum _ fun k _ => (fTerm_props i hh hhc j k).1]
  simp only [hint, hval]
  simp [ite_and]

theorem v_densHypAt_eq (i : Fin (n + 1)) {U : Set (Fin (n + 1) → ℂ)}
    {v : (Fin (n + 1) → ℂ) → ℝ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hp : PoincareLelongData U v φ)
    (w : Fin n → ℂ) :
    v (hypInclAt i w) * densHypAt i φ w =
      ((n.factorial : ℝ) * (2 / Real.pi) ^ n) * hDens i v φ (hypInclAt i w) := by
  obtain ⟨hU, hv, hvc, hvU, hφ⟩ := hp
  by_cases hw : hypInclAt i w ∈ U
  · have hr : ∀ k, hessC (φ k ∘ hypInclAt i) w =
        (hessC (φ k) (hypInclAt i w)).submatrix i.succAbove i.succAbove := fun k =>
      hessCRestrict_thm n (φ k) U i hU (by exact_mod_cast contDiffOn_infty.1 (hφ k) 2) w hw
    simp only [densHypAt, maDens, hr]
    simp only [hDens, minorDens]
    ring
  · have h0 : v (hypInclAt i w) = 0 := image_eq_zero_of_notMem_tsupport fun h => hw (hvU h)
    simp [hDens, h0]

theorem continuous_hypInclAt (i : Fin (n + 1)) : Continuous (hypInclAt (n := n) i) := by
  unfold hypInclAt
  exact Continuous.finInsertNth i continuous_const continuous_id

theorem hasCompactSupport_comp_hypInclAt (i : Fin (n + 1)) {h : (Fin (n + 1) → ℂ) → ℝ}
    (hhc : HasCompactSupport h) : HasCompactSupport (fun w : Fin n → ℂ => h (hypInclAt i w)) := by
  have hr : Continuous (fun z : Fin (n + 1) → ℂ => Fin.removeNth i z) :=
    continuous_pi fun j => continuous_apply _
  have hK : IsCompact ((fun z : Fin (n + 1) → ℂ => Fin.removeNth i z) '' tsupport h) := hhc.image hr
  unfold HasCompactSupport
  refine IsCompact.of_isClosed_subset hK (isClosed_tsupport _) ?_
  refine closure_minimal ?_ hK.isClosed
  intro w hw
  exact ⟨hypInclAt i w, subset_tsupport _ hw, by simp [hypInclAt, Fin.removeNth_insertNth]⟩

theorem kDens_mul : kDens n * (Real.pi / 2 * (1 / ((n : ℝ) + 1))) =
    (n.factorial : ℝ) * (2 / Real.pi) ^ n := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold kDens
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

theorem log_norm_integral_at_coordinate (n : ℕ) (i : Fin (n + 1)) (U : Set (Fin (n + 1) → ℂ))
    (v : (Fin (n + 1) → ℂ) → ℝ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (hp : PoincareLelongData U v φ) :
    Integrable (fun z => Real.log ‖z i‖ * densV v φ z) volume ∧
    Integrable (fun w => v (hypInclAt i w) * densHypAt i φ w) volume ∧
    ∫ z, Real.log ‖z i‖ * densV v φ z = ∫ w, v (hypInclAt i w) * densHypAt i φ w := by
  obtain ⟨hh, hhc⟩ := hDens_props i hp
  have hcont : Continuous (densV v φ) := maDens_cons_continuous hp.1 hp.2.1 hp.2.2.2.1 hp.2.2.2.2
  have hcs : HasCompactSupport (densV v φ) := maDens_cons_hasCompactSupport hp.2.2.1 φ
  have hR : (fun w => v (hypInclAt i w) * densHypAt i φ w) =
      fun w => ((n.factorial : ℝ) * (2 / Real.pi) ^ n) * hDens i v φ (hypInclAt i w) :=
    funext (v_densHypAt_eq i hp)
  have hRi : Integrable (fun w : Fin n → ℂ => hDens i v φ (hypInclAt i w)) :=
    (hh.continuous.comp (continuous_hypInclAt i)).integrable_of_hasCompactSupport
      (hasCompactSupport_comp_hypInclAt i hhc)
  refine ⟨?_, ?_, ?_⟩
  · have := (logCoordLocInt_thm (n + 1) i).integrable_smul_left_of_hasCompactSupport hcont hcs
    simpa [smul_eq_mul, mul_comm] using this
  · rw [hR]; exact hRi.const_mul _
  · rw [integral_log_densV_eq i hp, integral_log_maDens_psiRef i (hh.of_le (by norm_num)) hhc, hR,
      integral_const_mul, ← kDens_mul]
    simp only [hypInclAt]
    ring

theorem log_norm_contDiffOn {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    {u : (Fin D → ℂ) → ℂ} (hu : DifferentiableOn ℂ u U) (hu0 : ∀ z ∈ U, u z ≠ 0) :
    ContDiffOn ℝ ∞ (fun z => Real.log ‖u z‖) U := by
  have ha : AnalyticOnNhd ℂ u U := ReciprocityTheory.AnForm.Osgood.osgood D U u hU hu
  have hc : ContDiffOn ℝ ∞ u U := (ha.contDiffOn hU.uniqueDiffOn).restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ∞ (fun z => ‖u z‖ ^ 2) U := (contDiff_norm_sq ℝ).comp_contDiffOn hc
  have h3 : ContDiffOn ℝ ∞ (fun z => (1 / 2 : ℝ) * Real.log (‖u z‖ ^ 2)) U :=
    contDiffOn_const.mul (h2.log fun z hz => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hu0 z hz)))
  refine h3.congr fun z _ => ?_
  rw [Real.log_pow]
  push_cast
  ring

theorem unit_part {U : Set (Fin (n + 1) → ℂ)} {v : (Fin (n + 1) → ℂ) → ℝ}
    {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hp : PoincareLelongData U v φ) {u : (Fin (n + 1) → ℂ) → ℂ}
    (hu : DifferentiableOn ℂ u U) (hu0 : ∀ z ∈ U, u z ≠ 0) :
    Integrable (fun z => Real.log ‖u z‖ * densV v φ z) ∧
      ∫ z, Real.log ‖u z‖ * densV v φ z = 0 := by
  obtain ⟨hU, hv, hvc, hvU, hφ⟩ := hp
  have hl := log_norm_contDiffOn hU hu hu0
  have hP := parts_thm n φ v (fun z => Real.log ‖u z‖) U
    ⟨hU, hv.contDiffOn, hvc, hvU, by exact_mod_cast contDiffOn_infty.1 hl 3,
      fun k => by exact_mod_cast contDiffOn_infty.1 (hφ k) 3⟩
  have hsupp : Function.support (fun z => Real.log ‖u z‖ * densV v φ z) ⊆ U := by
    intro z hz
    by_contra hzU
    apply hz
    show Real.log ‖u z‖ * maDens (Fin.cons v φ) z = 0
    rw [maDens_cons_eq_zero φ (fun h => hzU (hvU h)), mul_zero]
  have hzero : ∀ z ∈ U, maDens (Fin.cons (fun z => Real.log ‖u z‖) φ) z = 0 := by
    intro z hz
    unfold maDens
    rw [hessC_cons, hessC_log_norm u z (ReciprocityTheory.AnForm.Osgood.osgood _ U u hU hu z hz) (hu0 z hz),
      mdisc_cons_zero]
    simp
  refine ⟨(integrableOn_iff_integrable_of_support_subset hsupp).1 hP.2.1, ?_⟩
  have h5 := hP.2.2.2.2
  simp only [maInt] at h5
  have e : ∫ z, Real.log ‖u z‖ * densV v φ z = ∫ z in U, Real.log ‖u z‖ * densV v φ z :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
      Function.notMem_support.1 fun h => hz (hsupp h)).symm
  rw [e]
  show ∫ z in U, Real.log ‖u z‖ * maDens (Fin.cons v φ) z = 0
  rw [h5]
  exact setIntegral_eq_zero_of_forall_eq_zero fun z hz => by rw [hzero z hz, mul_zero]

end

end ReciprocityTheory.AnForm.A
end

section
namespace ReciprocityTheory.AnForm.A

open MeasureTheory Filter Topology

theorem log_norm_integral_formula : PoincareLelongHyperplane := by
  intro n U v φ hp
  have hf : (hypInclAt (n := n) 0) = hypIncl := funext hypInclAt_zero
  have h := log_norm_integral_at_coordinate n 0 U v φ hp
  unfold densHypAt at h
  rw [hf] at h
  exact h

theorem log_norm_integral_formula_unit : PoincareLelongUnitPower := by
  intro n m U v φ u hp hu hu0
  obtain ⟨-, -, -, hsub, -⟩ := id hp
  obtain ⟨hI1, -, hE1⟩ := log_norm_integral_formula n U v φ hp
  obtain ⟨hI2, hE2⟩ := unit_part hp hu hu0
  have hae : (fun z : Fin (n + 1) → ℂ => Real.log ‖z 0 ^ m * u z‖ * densV v φ z) =ᵐ[volume]
      fun z => (m : ℝ) * (Real.log ‖z 0‖ * densV v φ z) + Real.log ‖u z‖ * densV v φ z := by
    filter_upwards [ae_coord_ne_zero (0 : Fin (n + 1))] with z hz
    by_cases hzv : z ∈ tsupport v
    · have huz : u z ≠ 0 := hu0 z (hsub hzv)
      rw [norm_mul, norm_zpow, Real.log_mul (zpow_ne_zero _ (norm_ne_zero_iff.mpr hz))
        (norm_ne_zero_iff.mpr huz), Real.log_zpow]
      ring
    · have h0 : densV v φ z = 0 := maDens_cons_eq_zero φ hzv
      rw [h0]
      ring
  refine ⟨((hI1.const_mul (m : ℝ)).add hI2).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_add (hI1.const_mul _) hI2]
  first
    | rw [integral_const_mul]
    | rw [integral_mul_left]
  rw [hE1, hE2, add_zero]

theorem log_norm_integral_formula_snc : PoincareLelongNormalCrossing := by
  intro n m U v φ u hp hu hu0
  obtain ⟨-, -, -, hsub, -⟩ := id hp
  have hI : ∀ i, Integrable (fun z : Fin (n + 1) → ℂ => Real.log ‖z i‖ * densV v φ z) volume :=
    fun i => (log_norm_integral_at_coordinate n i U v φ hp).1
  have hE : ∀ i, ∫ z, Real.log ‖z i‖ * densV v φ z = ∫ w, v (hypInclAt i w) * densHypAt i φ w :=
    fun i => (log_norm_integral_at_coordinate n i U v φ hp).2.2
  obtain ⟨hIu, hEu⟩ := unit_part hp hu hu0
  have hIs : Integrable (fun z : Fin (n + 1) → ℂ =>
      ∑ i ∈ Finset.univ, (m i : ℝ) * (Real.log ‖z i‖ * densV v φ z)) volume :=
    integrable_finset_sum Finset.univ (fun i _ => (hI i).const_mul (m i : ℝ))
  have hae : (fun z : Fin (n + 1) → ℂ => Real.log ‖u z * ∏ i, z i ^ m i‖ * densV v φ z) =ᵐ[volume]
      fun z => Real.log ‖u z‖ * densV v φ z +
        ∑ i ∈ Finset.univ, (m i : ℝ) * (Real.log ‖z i‖ * densV v φ z) := by
    filter_upwards [ae_all_iff.mpr (fun i => ae_coord_ne_zero (n := n) i)] with z hz
    by_cases hzv : z ∈ tsupport v
    · have huz : u z ≠ 0 := hu0 z (hsub hzv)
      have hp0 : ‖∏ i, z i ^ m i‖ ≠ 0 := by
        rw [norm_ne_zero_iff]
        exact Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero _ (hz i))
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr huz) hp0,
        log_norm_prod_zpow_eq_logMono m z hz, logMono, add_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    · have h0 : densV v φ z = 0 := maDens_cons_eq_zero φ hzv
      simp [h0]
  refine ⟨(hIu.add hIs).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_add hIu hIs, hEu, zero_add,
    integral_finset_sum Finset.univ (fun i _ => (hI i).const_mul (m i : ℝ))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  first
    | rw [integral_const_mul]
    | rw [integral_mul_left]
  rw [hE i]

end ReciprocityTheory.AnForm.A
end
