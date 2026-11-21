import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GauIntegrable

section
open MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Parseval

lemma norm_le_norm_cat_left (A : Ad3.LR.M22) (y : Fin 2 → ℝ) : ‖A‖ ≤ ‖cat A y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun r => ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun c => ?_
  have h1 : ‖(cat A y) r‖ ≤ ‖cat A y‖ := norm_le_pi_norm (cat A y) r
  refine le_trans ?_ h1
  fin_cases c
  · exact norm_le_pi_norm (cat A y r) 0
  · exact norm_le_pi_norm (cat A y r) 1

lemma norm_le_norm_cat_right (A : Ad3.LR.M22) (y : Fin 2 → ℝ) : ‖y‖ ≤ ‖cat A y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun r => ?_
  have h1 : ‖(cat A y) r‖ ≤ ‖cat A y‖ := norm_le_pi_norm (cat A y) r
  exact le_trans (norm_le_pi_norm (cat A y r) 2) h1

theorem fz_decay_in_A : ∀ (Φ : Ad3.LR.Sw) (N : ℕ), ∃ C : ℝ, ∀ (A : Ad3.LR.M22) (ξ : Fin 2 → ℝ),
    (1 + ‖A‖) ^ N * ‖GlobalTheory.CompanionTheory.Parseval.fz Φ A ξ‖ ≤ C := by
  intro Φ N
  set C' : ℝ := 2 ^ (N + 3) *
    ((Finset.Iic ((N + 3, 0) : ℕ × ℕ)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ with hC'
  have hdec : ∀ X : Ad3.LR.M23, (1 + ‖X‖) ^ (N + 3) * ‖Φ X‖ ≤ C' := by
    intro X
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N + 3, 0))
      (k := N + 3) (n := 0) le_rfl le_rfl Φ X
    simpa [norm_iteratedFDeriv_zero] using this
  have hC'0 : 0 ≤ C' := by
    have h0 := hdec 0
    refine le_trans ?_ h0
    positivity
  have hint : Integrable (fun y : Fin 2 → ℝ => (1 + ‖y‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  set I : ℝ := ∫ y : Fin 2 → ℝ, (1 + ‖y‖) ^ (-(3 : ℝ)) with hI
  refine ⟨C' * I, fun A ξ => ?_⟩
  have hA : 0 < (1 + ‖A‖) ^ N := by positivity
  have hpt : ∀ y : Fin 2 → ℝ,
      ‖(Φ (cat A y) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ))‖
        ≤ (C' / (1 + ‖A‖) ^ N) * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
    intro y
    have hph : ‖Complex.exp (2 * Real.pi * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ))‖ = 1 := by
      have : (2 * Real.pi * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ)) =
          ((2 * Real.pi * (ξ 0 * y 0 + ξ 1 * y 1) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, hph, mul_one]
    have hy : 0 < 1 + ‖y‖ := by positivity
    have hy3 : (1 + ‖y‖) ^ (-(3 : ℝ)) = ((1 + ‖y‖) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hy.le]
      norm_cast
    rw [hy3, div_mul_eq_mul_div, ← div_eq_mul_inv, div_div, le_div_iff₀ (by positivity)]
    have h1 : (1 + ‖A‖) ^ N ≤ (1 + ‖cat A y‖) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith [norm_le_norm_cat_left A y]) N
    have h2 : (1 + ‖y‖) ^ 3 ≤ (1 + ‖cat A y‖) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith [norm_le_norm_cat_right A y]) 3
    have h3 : (1 + ‖A‖) ^ N * (1 + ‖y‖) ^ 3 ≤ (1 + ‖cat A y‖) ^ (N + 3) := by
      rw [pow_add]
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    calc ‖Φ (cat A y)‖ * ((1 + ‖y‖) ^ 3 * (1 + ‖A‖) ^ N)
        ≤ ‖Φ (cat A y)‖ * (1 + ‖cat A y‖) ^ (N + 3) :=
          mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact h3) (norm_nonneg _)
      _ ≤ C' := by rw [mul_comm]; exact hdec _
  have hbound : ‖fz Φ A ξ‖ ≤ (C' / (1 + ‖A‖) ^ N) * I := by
    unfold fz
    have := norm_integral_le_of_norm_le (hint.const_mul (C' / (1 + ‖A‖) ^ N))
      (Filter.Eventually.of_forall hpt)
    rwa [integral_const_mul] at this
  calc (1 + ‖A‖) ^ N * ‖fz Φ A ξ‖
      ≤ (1 + ‖A‖) ^ N * ((C' / (1 + ‖A‖) ^ N) * I) :=
        mul_le_mul_of_nonneg_left hbound hA.le
    _ = C' * I := by field_simp

end GlobalTheory.CompanionTheory.Parseval
end
end

section
open MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Parseval.Ibp

open Ad3 Ad3.LR

def dirY (j : Fin 2) : M23 := fun r c => if r = j ∧ c = 2 then 1 else 0

def phase (ξ y : Fin 2 → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ))

lemma cat_add_smul (A : M22) (y : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    cat A (y + t • Pi.single j (1 : ℝ)) = cat A y + t • dirY j := by
  funext r c
  fin_cases j <;> fin_cases r <;> fin_cases c <;> simp [cat, dirY]

lemma continuous_cat (A : M22) : Continuous (cat A) := by
  refine continuous_pi fun r => continuous_pi fun c => ?_
  fin_cases c
  · simpa [cat] using continuous_const
  · simpa [cat] using continuous_const
  · simpa [cat] using continuous_apply r

lemma norm_le_norm_cat (A : M22) (y : Fin 2 → ℝ) : ‖y‖ ≤ ‖cat A y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun r => ?_
  have h1 : ‖cat A y r 2‖ ≤ ‖cat A y r‖ := norm_le_pi_norm (cat A y r) 2
  have h2 : ‖cat A y r‖ ≤ ‖cat A y‖ := norm_le_pi_norm (cat A y) r
  have h3 : cat A y r 2 = y r := by simp [cat]
  rw [h3] at h1
  exact h1.trans h2

lemma integrable_cat (Φ : Sw) (A : M22) : Integrable (fun y : Fin 2 → ℝ => Φ (cat A y)) := by
  set C : ℝ := 2 ^ 3 * ((Finset.Iic ((3, 0) : ℕ × ℕ)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ
  have hint : Integrable (fun y : Fin 2 → ℝ => C * (1 + ‖y‖) ^ (-(3 : ℝ))) :=
    (integrable_one_add_norm (by rw [Module.finrank_fin_fun]; norm_num)).const_mul C
  refine hint.mono' (Φ.continuous.comp (continuous_cat A)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (3, 0)) (k := 3) (n := 0)
    le_rfl le_rfl Φ (cat A y)
  rw [norm_iteratedFDeriv_zero] at hb
  have hpos : 0 < (1 + ‖y‖) ^ 3 := by positivity
  have hle : (1 + ‖y‖) ^ 3 ≤ (1 + ‖cat A y‖) ^ 3 := by
    have := norm_le_norm_cat A y
    gcongr
  have hb' : (1 + ‖y‖) ^ 3 * ‖Φ (cat A y)‖ ≤ C :=
    (mul_le_mul_of_nonneg_right hle (norm_nonneg _)).trans hb
  have he : (1 + ‖y‖) ^ (-(3 : ℝ)) = ((1 + ‖y‖) ^ 3)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    norm_cast
  rw [he, ← div_eq_mul_inv, le_div_iff₀ hpos]
  linarith

lemma continuous_phase (ξ : Fin 2 → ℝ) : Continuous (phase ξ) := by
  unfold phase
  fun_prop

lemma norm_phase (ξ y : Fin 2 → ℝ) : ‖phase ξ y‖ = 1 := by
  unfold phase
  have : 2 * (Real.pi : ℂ) * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ) =
      ((2 * Real.pi * (ξ 0 * y 0 + ξ 1 * y 1) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma integrable_cat_phase (Φ : Sw) (A : M22) (ξ : Fin 2 → ℝ) :
    Integrable (fun y : Fin 2 → ℝ => Φ (cat A y) * phase ξ y) := by
  refine (integrable_cat Φ A).mono
    ((Φ.continuous.comp (continuous_cat A)).mul (continuous_phase ξ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  simp [norm_phase]

lemma hasLineDerivAt_cat (Φ : Sw) (A : M22) (j : Fin 2) (y : Fin 2 → ℝ) :
    HasLineDerivAt ℝ (fun y : Fin 2 → ℝ => Φ (cat A y))
      (LineDeriv.lineDerivOp (dirY j) Φ (cat A y)) y (Pi.single j (1 : ℝ)) := by
  have h : HasFDerivAt Φ (fderiv ℝ Φ (cat A y)) (cat A y) :=
    (Φ.differentiableAt).hasFDerivAt
  have h2 := h.hasLineDerivAt (dirY j)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  unfold HasLineDerivAt at h2 ⊢
  have e : (fun t : ℝ => Φ (cat A (y + t • Pi.single j (1 : ℝ)))) =
      fun t : ℝ => Φ (cat A y + t • dirY j) := by
    funext t; rw [cat_add_smul]
  rw [e]
  exact h2

lemma dot_add_smul (ξ y : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    ξ 0 * (y + t • Pi.single j (1 : ℝ) : Fin 2 → ℝ) 0 + ξ 1 * (y + t • Pi.single j (1 : ℝ) : Fin 2 → ℝ) 1 =
      (ξ 0 * y 0 + ξ 1 * y 1) + t * ξ j := by
  fin_cases j <;> simp <;> ring

lemma hasLineDerivAt_phase (ξ : Fin 2 → ℝ) (j : Fin 2) (y : Fin 2 → ℝ) :
    HasLineDerivAt ℝ (phase ξ) (2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ) * phase ξ y) y
      (Pi.single j (1 : ℝ)) := by
  unfold HasLineDerivAt
  set a : ℝ := ξ 0 * y 0 + ξ 1 * y 1 with ha
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hc
  have e : (fun t : ℝ => phase ξ (y + t • Pi.single j (1 : ℝ))) =
      fun t : ℝ => Complex.exp (c * ((a + t * ξ j : ℝ) : ℂ)) := by
    funext t
    unfold phase
    rw [dot_add_smul]
  rw [e]
  have h1 : HasDerivAt (fun t : ℝ => a + t * ξ j) (ξ j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (ξ j)).const_add a
  have h2 : HasDerivAt (fun t : ℝ => ((a + t * ξ j : ℝ) : ℂ)) (ξ j : ℂ) 0 := h1.ofReal_comp
  have h3 := (h2.const_mul c).cexp
  have e0 : c * ((a + 0 * ξ j : ℝ) : ℂ) = c * (a : ℂ) := by simp
  rw [e0] at h3
  have e1 : c * (ξ j : ℂ) * phase ξ y = Complex.exp (c * (a : ℂ)) * (c * (ξ j : ℂ)) := by
    unfold phase
    rw [mul_comm]
  rw [e1]
  exact h3

theorem fz_lineDeriv (Φ : Sw) (j : Fin 2) (A : M22) (ξ : Fin 2 → ℝ) :
    fz (LineDeriv.lineDerivOp (dirY j) Φ) A ξ =
      -(2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ)) * fz Φ A ξ := by
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ) with hc
  set Ψ : Sw := LineDeriv.lineDerivOp (dirY j) Φ with hΨ
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Fin 2 → ℝ))) (B := ContinuousLinearMap.mul ℝ ℂ)
    (f := fun y => Φ (cat A y)) (f' := fun y => Ψ (cat A y))
    (g := phase ξ) (g' := fun y => c * phase ξ y) (v := Pi.single j (1 : ℝ))
    (integrable_cat_phase Ψ A ξ)
    (by
      have := (integrable_cat_phase Φ A ξ).const_mul c
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only [ContinuousLinearMap.mul_apply']
      ring)
    (integrable_cat_phase Φ A ξ)
    (fun y _ => hasLineDerivAt_cat Φ A j y)
    (fun y _ => hasLineDerivAt_phase ξ j y)
  simp only [ContinuousLinearMap.mul_apply'] at key
  have e1 : fz Ψ A ξ = ∫ y, Ψ (cat A y) * phase ξ y := rfl
  have e2 : fz Φ A ξ = ∫ y, Φ (cat A y) * phase ξ y := rfl
  have e3 : ∫ y, Φ (cat A y) * (c * phase ξ y) = c * ∫ y, Φ (cat A y) * phase ξ y := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  rw [e1, e2]
  rw [e3] at key
  linear_combination key

theorem main : ∀ (Φ : Ad3.LR.Sw) (j : Fin 2), ∃ Ψ : Ad3.LR.Sw, ∀ (A : Ad3.LR.M22) (ξ : Fin 2 → ℝ),
    GlobalTheory.CompanionTheory.Parseval.fz Ψ A ξ =
      -(2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ)) * GlobalTheory.CompanionTheory.Parseval.fz Φ A ξ :=
  fun Φ j => ⟨LineDeriv.lineDerivOp (dirY j) Φ, fun A ξ => fz_lineDeriv Φ j A ξ⟩

end GlobalTheory.CompanionTheory.Parseval.Ibp
end
end

section
open MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Parseval

open Ad3 Ad3.LR Ad3.LR.C

lemma of_mul_blk (h : M22) (z : Fin 2 → ℝ) :
    Matrix.of.symm (Matrix.of h * blk z) = cat h (fun r => h r 0 * z 0 + h r 1 * z 1) := by
  funext r c
  fin_cases c <;> simp [cat, blk, Matrix.mul_apply, Fin.sum_univ_succ]

lemma dualF_pair (h : M22) (ζ : ℝ) (z : Fin 2 → ℝ) (hd : (Matrix.of h).det ≠ 0) :
    ζ * z 0 + z 1 = dualF h ζ 0 * (h 0 0 * z 0 + h 0 1 * z 1) +
      dualF h ζ 1 * (h 1 0 * z 0 + h 1 1 * z 1) := by
  have hD : (Matrix.of h).det = h 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    simp [Matrix.det_fin_two]
  simp only [dualF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  rw [hD]
  ring

theorem gz_eq_fz : ∀ (Φ : Ad3.LR.Sw) (h : Ad3.LR.M22) (ζ : ℝ), (Matrix.of h).det ≠ 0 →
    GlobalTheory.CompanionTheory.Parseval.gz Φ h ζ = ((|(Matrix.of h).det|⁻¹ : ℝ) : ℂ) *
      GlobalTheory.CompanionTheory.Parseval.fz Φ h (GlobalTheory.CompanionTheory.Parseval.dualF h ζ) := by
  intro Φ h ζ hd
  let L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' (Matrix.of h)
  have hLdet : LinearMap.det L = (Matrix.of h).det := LinearMap.det_toLin' _
  have hLz : ∀ z, L z = fun r => h r 0 * z 0 + h r 1 * z 1 := by
    intro z
    funext r
    simp [L, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  let G : (Fin 2 → ℝ) → ℂ := fun y => Φ (cat h y) *
    Complex.exp (2 * Real.pi * Complex.I * ((dualF h ζ 0 * y 0 + dualF h ζ 1 * y 1 : ℝ) : ℂ))
  have hcat : Continuous (fun y : Fin 2 → ℝ => cat h y) := by
    refine continuous_pi fun r => continuous_pi fun c => ?_
    fin_cases c
    · simpa [cat] using continuous_const
    · simpa [cat] using continuous_const
    · simpa [cat] using continuous_apply r
  have hG : Continuous G := by
    refine (Φ.continuous.comp hcat).mul (Complex.continuous_exp.comp ?_)
    refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
    fun_prop
  have hmap : Measure.map L (volume : Measure (Fin 2 → ℝ)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hLdet]; exact hd)
  have hint : ∫ z, G (L z) = ∫ y, G y ∂(Measure.map L volume) :=
    (integral_map L.continuous_of_finiteDimensional.aemeasurable hG.aestronglyMeasurable).symm
  have hgz : gz Φ h ζ = ∫ z, G (L z) := by
    unfold gz
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [G]
    rw [of_mul_blk, hLz, dualF_pair h ζ z hd]
  rw [hgz, hint, hmap, integral_smul_measure, hLdet, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
  simp [fz, G, Complex.real_smul]

end GlobalTheory.CompanionTheory.Parseval
end
end

section
open MeasureTheory

noncomputable section
open Complex Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.Parseval.GaussRep

lemma continuous_rows (h : M22) :
    Continuous fun z : Fin 2 → ℝ => (Matrix.of.symm (Matrix.of h * blk z) : M23) := by
  refine continuous_pi fun r => continuous_pi fun c => ?_
  fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, blk] <;> fun_prop

lemma norm_mulVec_le (h : M22) (z : Fin 2 → ℝ) :
    ‖(Matrix.of h).mulVec z‖ ≤ ‖(Matrix.of.symm (Matrix.of h * blk z) : M23)‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun r => ?_
  have h1 : (Matrix.of h).mulVec z r = (Matrix.of.symm (Matrix.of h * blk z) : M23) r 2 := by
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, blk]
  rw [h1]
  exact (norm_le_pi_norm _ (2 : Fin 3)).trans (norm_le_pi_norm _ r)

lemma integrable_rows (Φ : Sw) (h : M22) (hd : (Matrix.of h).det ≠ 0) :
    Integrable (fun z : Fin 2 → ℝ => Φ (Matrix.of.symm (Matrix.of h * blk z))) := by
  have hker : LinearMap.ker (Matrix.mulVecLin (Matrix.of h)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro z hz
    exact Matrix.eq_zero_of_mulVec_eq_zero hd hz
  obtain ⟨K, hKpos, hK⟩ := LinearMap.exists_antilipschitzWith _ hker
  have hz : ∀ z : Fin 2 → ℝ,
      ‖z‖ ≤ (K : ℝ) * ‖(Matrix.of.symm (Matrix.of h * blk z) : M23)‖ := by
    intro z
    have h1 := hK.le_mul_dist z 0
    simp only [dist_zero_right, map_zero, Matrix.mulVecLin_apply] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (norm_mulVec_le h z) K.2)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ X : M23, (1 + ‖X‖) ^ 3 * ‖Φ X‖ ≤ C := by
    refine ⟨2 ^ 3 * (Finset.Iic ((3, 0) : ℕ × ℕ)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ, fun X => ?_⟩
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (3, 0))
      (k := 3) (n := 0) le_rfl le_rfl Φ X
    simpa [norm_iteratedFDeriv_zero] using this
  have hmaj : Integrable (fun z : Fin 2 → ℝ => (1 + (K : ℝ)) ^ 3 * C * (1 + ‖z‖) ^ (-(3 : ℝ))) := by
    refine (integrable_one_add_norm ?_).const_mul _
    simp only [Module.finrank_fin_fun]
    norm_num
  refine hmaj.mono' (Φ.continuous.comp (continuous_rows h)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  set X : M23 := Matrix.of.symm (Matrix.of h * blk z) with hX
  have hpos : (0 : ℝ) < 1 + ‖z‖ := by positivity
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hle : 1 + ‖z‖ ≤ (1 + (K : ℝ)) * (1 + ‖X‖) := by
    have := hz z
    have hX0 : 0 ≤ ‖X‖ := norm_nonneg _
    nlinarith
  have hpow : (1 + ‖z‖) ^ 3 ≤ (1 + (K : ℝ)) ^ 3 * (1 + ‖X‖) ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hpos.le hle 3
  have hmul : ‖Φ X‖ * (1 + ‖z‖) ^ 3 ≤ (1 + (K : ℝ)) ^ 3 * C := by
    calc ‖Φ X‖ * (1 + ‖z‖) ^ 3 ≤ ‖Φ X‖ * ((1 + (K : ℝ)) ^ 3 * (1 + ‖X‖) ^ 3) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (1 + (K : ℝ)) ^ 3 * ((1 + ‖X‖) ^ 3 * ‖Φ X‖) := by ring
      _ ≤ (1 + (K : ℝ)) ^ 3 * C := mul_le_mul_of_nonneg_left (hC X) (by positivity)
  have hr : (1 + ‖z‖) ^ (-(3 : ℝ)) = ((1 + ‖z‖) ^ 3)⁻¹ := by
    rw [Real.rpow_neg hpos.le]
    norm_cast
  rw [hr, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact hmul

lemma ge_eq_integral (ε u : ℝ) (hε : 0 < ε) :
    ((ge ε u : ℝ) : ℂ) = ∫ ζ : ℝ, (GlobalTheory.CompanionTheory.Parseval.gau ε ζ : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((ζ * u : ℝ) : ℂ)) := by
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set b : ℂ := ((-(Real.pi / ε ^ 2) : ℝ) : ℂ) with hb
  have hbre : b.re < 0 := by
    rw [hb, Complex.ofReal_re]
    have : 0 < Real.pi / ε ^ 2 := by positivity
    linarith
  have key := integral_cexp_quadratic hbre (2 * Real.pi * Complex.I * u) 0
  have hint : ∀ ζ : ℝ, (GlobalTheory.CompanionTheory.Parseval.gau ε ζ : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((ζ * u : ℝ) : ℂ)) =
      (ε⁻¹ : ℂ) * Complex.exp (b * (ζ : ℂ) ^ 2 + 2 * Real.pi * Complex.I * u * ζ + 0) := by
    intro ζ
    rw [GlobalTheory.CompanionTheory.Parseval.gau_eq]
    push_cast
    rw [mul_assoc, ← Complex.exp_add, hb]
    push_cast
    congr 2
    ring
  simp_rw [hint]
  rw [integral_const_mul, key]
  have hsq : (Real.pi : ℂ) / -b = ((ε ^ 2 : ℝ) : ℂ) := by
    rw [hb]; push_cast; field_simp
  have hroot : (((ε ^ 2 : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = ε := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hε.le]
  rw [hsq, hroot, ← mul_assoc, inv_mul_cancel₀ hε', one_mul]
  unfold ge
  push_cast
  congr 1
  rw [hb]
  push_cast
  field_simp
  ring_nf
  simp

lemma norm_psiR (x : ℝ) : ‖psiR x‖ = 1 := by
  unfold psiR
  have : -2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) = ((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma norm_cexp_two_pi (x : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))‖ = 1 := by
  have : 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma continuous_psiR : Continuous psiR := by
  unfold psiR; fun_prop

lemma continuous_gau (ε : ℝ) : Continuous (GlobalTheory.CompanionTheory.Parseval.gau ε) := by
  unfold GlobalTheory.CompanionTheory.Parseval.gau; fun_prop

lemma phase_identity (a g : ℂ) (ζ v z₀ z₁ : ℝ) :
    a * psiR (-z₁) * (g * Complex.exp (2 * Real.pi * Complex.I * ((ζ * (z₀ - v) : ℝ) : ℂ))) =
      g * psiR (ζ * v) * (a * Complex.exp (2 * Real.pi * Complex.I * ((ζ * z₀ + z₁ : ℝ) : ℂ))) := by
  have e : psiR (-z₁) * Complex.exp (2 * Real.pi * Complex.I * ((ζ * (z₀ - v) : ℝ) : ℂ)) =
      psiR (ζ * v) * Complex.exp (2 * Real.pi * Complex.I * ((ζ * z₀ + z₁ : ℝ) : ℂ)) := by
    unfold psiR
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination a * g * e

theorem Ae_eq_integral_gau : ∀ (Φ : Ad3.LR.Sw) (ε : ℝ) (h : Ad3.LR.M22) (v : ℝ), 0 < ε →
    (Matrix.of h).det ≠ 0 → Ad3.LR.C.Ae Φ ε h v =
      ∫ ζ : ℝ, (GlobalTheory.CompanionTheory.Parseval.gau ε ζ : ℂ) * Ad3.psiR (ζ * v) * GlobalTheory.CompanionTheory.Parseval.gz Φ h ζ := by
  intro Φ ε h v hε hd
  have hF := integrable_rows Φ h hd
  have hFc : Continuous fun z : Fin 2 → ℝ => Φ (Matrix.of.symm (Matrix.of h * blk z)) :=
    Φ.continuous.comp (continuous_rows h)
  set F : (Fin 2 → ℝ) → ℂ := fun z => Φ (Matrix.of.symm (Matrix.of h * blk z)) with hFdef
  let f : (Fin 2 → ℝ) → ℝ → ℂ := fun z ζ => F z * psiR (-(z 1)) *
    ((GlobalTheory.CompanionTheory.Parseval.gau ε ζ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((ζ * (z 0 - v) : ℝ) : ℂ)))
  have hψ := continuous_psiR
  have hg := continuous_gau ε
  have hcont : Continuous (Function.uncurry f) := by
    show Continuous fun p : (Fin 2 → ℝ) × ℝ => F p.1 * psiR (-(p.1 1)) *
      ((GlobalTheory.CompanionTheory.Parseval.gau ε p.2 : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((p.2 * (p.1 0 - v) : ℝ) : ℂ)))
    have h1 : Continuous fun p : (Fin 2 → ℝ) × ℝ => F p.1 := hFc.comp continuous_fst
    have h2 : Continuous fun p : (Fin 2 → ℝ) × ℝ => psiR (-(p.1 1)) :=
      hψ.comp (by fun_prop)
    have h3 : Continuous fun p : (Fin 2 → ℝ) × ℝ => (GlobalTheory.CompanionTheory.Parseval.gau ε p.2 : ℂ) :=
      Complex.continuous_ofReal.comp (hg.comp continuous_snd)
    have h4 : Continuous fun p : (Fin 2 → ℝ) × ℝ =>
        Complex.exp (2 * Real.pi * Complex.I * ((p.2 * (p.1 0 - v) : ℝ) : ℂ)) := by fun_prop
    exact (h1.mul h2).mul (h3.mul h4)
  have hint : Integrable (Function.uncurry f) ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ)) := by
    refine (hF.norm.mul_prod (GlobalTheory.CompanionTheory.Parseval.gau_integrable ε hε)).mono'
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    have hgn : ‖(GlobalTheory.CompanionTheory.Parseval.gau ε p.2 : ℂ)‖ = GlobalTheory.CompanionTheory.Parseval.gau ε p.2 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (GlobalTheory.CompanionTheory.Parseval.gau_nonneg ε p.2 hε)]
    simp only [Function.uncurry, f, norm_mul, norm_psiR, norm_cexp_two_pi, hgn, mul_one]
    exact le_rfl
  calc Ad3.LR.C.Ae Φ ε h v = ∫ z, ∫ ζ, f z ζ := by
        unfold Ad3.LR.C.Ae
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [f]
        rw [integral_const_mul, ← ge_eq_integral ε (z 0 - v) hε]
    _ = ∫ ζ, ∫ z, f z ζ := integral_integral_swap hint
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
        simp only [f, GlobalTheory.CompanionTheory.Parseval.gz]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        exact phase_identity _ _ ζ v (z 0) (z 1)

end GlobalTheory.CompanionTheory.Parseval.GaussRep
end
end

section
open MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Parseval.OneDim

open GlobalTheory.CompanionTheory.Parseval

lemma profile_integrable : Integrable (fun t : ℝ => ((1 + |t|) ^ 2)⁻¹) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  have hp : (0 : ℝ) < 1 + |t| := by positivity
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg hp.le, Real.rpow_two]

lemma wt_eq_comp (a l ζ : ℝ) (ha : 0 < a) :
    wt a l ζ = (fun t : ℝ => (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹) (t / a)) (ζ - l) := by
  simp only [wt, abs_div, abs_of_pos ha]

lemma wt_integrable (a l : ℝ) (ha : 0 < a) : Integrable (wt a l) := by
  have h1 := profile_integrable.comp_div ha.ne'
  have h2 := h1.comp_sub_right l
  exact h2.congr (Filter.Eventually.of_forall fun ζ => (wt_eq_comp a l ζ ha).symm)

lemma wt_integral (a l : ℝ) (ha : 0 < a) :
    ∫ ζ, wt a l ζ = a * ∫ t : ℝ, ((1 + |t|) ^ 2)⁻¹ := by
  have h : wt a l = fun ζ => (fun t : ℝ => (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹) (t / a)) (ζ - l) :=
    funext fun ζ => wt_eq_comp a l ζ ha
  rw [h, integral_sub_right_eq_self (fun t : ℝ => (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹) (t / a)) l,
    Measure.integral_comp_div (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹) a, abs_of_pos ha, smul_eq_mul]

lemma wt_le_near {a l ζ : ℝ} (ha : 0 < a) (hl : l ≠ 0) (h : |ζ| < |l| / 2) :
    wt a l ζ ≤ 2 * a / |l| := by
  have hlp : 0 < |l| := abs_pos.2 hl
  have h1 : |l| / 2 ≤ |ζ - l| := by
    have := abs_sub_abs_le_abs_sub l ζ
    rw [abs_sub_comm l ζ] at this
    linarith
  have hy : |l| / (2 * a) ≤ |ζ - l| / a := by
    rw [div_le_div_iff₀ (by positivity) ha]
    nlinarith
  have hy0 : 0 < |l| / (2 * a) := by positivity
  set y := |ζ - l| / a with hydef
  have hypos : 0 < y := lt_of_lt_of_le hy0 hy
  have h2 : ((1 + y) ^ 2)⁻¹ ≤ y⁻¹ := by
    apply inv_anti₀ hypos
    nlinarith
  have h3 : y⁻¹ ≤ (|l| / (2 * a))⁻¹ := inv_anti₀ hy0 hy
  have h4 : (|l| / (2 * a))⁻¹ = 2 * a / |l| := inv_div _ _
  calc wt a l ζ = ((1 + y) ^ 2)⁻¹ := rfl
    _ ≤ 2 * a / |l| := by rw [← h4]; exact h2.trans h3

lemma gau_le_far {ε l ζ : ℝ} (hε : 0 < ε) (hl : l ≠ 0) (h : |l| / 2 ≤ |ζ|) :
    gau ε ζ ≤ 1 / |l| := by
  have hlp : 0 < |l| := abs_pos.2 hl
  set x := |l| / ε with hx
  have hxp : 0 < x := by positivity
  have hpi := Real.pi_gt_three
  set u := Real.pi * x ^ 2 / 4 with hu
  have h1 : x ≤ Real.exp u := by
    have := Real.add_one_le_exp u
    have hx2 : 3 * x ^ 2 / 4 ≤ u := by
      rw [hu]
      have : 0 ≤ x ^ 2 := sq_nonneg x
      nlinarith
    nlinarith [sq_nonneg (x - 1), sq_nonneg x]
  have h2 : Real.exp (-u) ≤ x⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hxp h1
  have h3 : -Real.pi * ζ ^ 2 / ε ^ 2 ≤ -u := by
    have hz : |l| ^ 2 / 4 ≤ ζ ^ 2 := by
      rw [← sq_abs ζ]
      nlinarith
    have hux : u = Real.pi * (|l| ^ 2 / 4) / ε ^ 2 := by
      rw [hu, hx]; field_simp
    rw [hux, neg_mul, neg_div, neg_le_neg_iff]
    gcongr
  have h4 : Real.exp (-Real.pi * ζ ^ 2 / ε ^ 2) ≤ x⁻¹ := (Real.exp_le_exp.2 h3).trans h2
  unfold gau
  calc ε⁻¹ * Real.exp (-Real.pi * ζ ^ 2 / ε ^ 2) ≤ ε⁻¹ * x⁻¹ := by gcongr
    _ = 1 / |l| := by rw [hx]; field_simp

lemma wt_mul_gau_le {ε a l : ℝ} (hε : 0 < ε) (ha : 0 < a) (hl : l ≠ 0) (ζ : ℝ) :
    wt a l ζ * gau ε ζ ≤ 2 * a / |l| * gau ε ζ + 1 / |l| * wt a l ζ := by
  have hlp : 0 < |l| := abs_pos.2 hl
  have hw := wt_nonneg a l ζ
  have hg := gau_nonneg ε ζ hε
  by_cases h : |ζ| < |l| / 2
  · have h1 := mul_le_mul_of_nonneg_right (wt_le_near ha hl h) hg
    have h2 : 0 ≤ 1 / |l| * wt a l ζ := by positivity
    linarith
  · have h1 := mul_le_mul_of_nonneg_left (gau_le_far hε hl (not_lt.1 h)) hw
    have h2 : 0 ≤ 2 * a / |l| * gau ε ζ := by positivity
    rw [mul_comm (wt a l ζ) (1 / |l|)] at h1
    have : wt a l ζ * gau ε ζ ≤ 1 / |l| * wt a l ζ := by
      rw [mul_comm (1 / |l|)]; rw [mul_comm (1 / |l|)] at h1; exact h1
    linarith

theorem wt_gau_bound :
    ∃ C : ℝ, ∀ ε a l : ℝ, 0 < ε → 0 < a → l ≠ 0 →
      ∫ ζ : ℝ, GlobalTheory.CompanionTheory.Parseval.wt a l ζ * GlobalTheory.CompanionTheory.Parseval.gau ε ζ ≤ C * (a / |l|) := by
  refine ⟨2 + ∫ t : ℝ, ((1 + |t|) ^ 2)⁻¹, fun ε a l hε ha hl => ?_⟩
  have hlp : 0 < |l| := abs_pos.2 hl
  have hgi := gau_integrable ε hε
  have hwi := wt_integrable a l ha
  have hR : Integrable (fun ζ => 2 * a / |l| * gau ε ζ + 1 / |l| * wt a l ζ) :=
    (hgi.const_mul _).add (hwi.const_mul _)
  have hL : Integrable (fun ζ => wt a l ζ * gau ε ζ) := by
    refine hR.mono' ?_ (Filter.Eventually.of_forall fun ζ => ?_)
    · exact (hwi.aestronglyMeasurable).mul hgi.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (wt_nonneg a l ζ) (gau_nonneg ε ζ hε))]
      exact wt_mul_gau_le hε ha hl ζ
  have hmono := integral_mono hL hR (fun ζ => wt_mul_gau_le hε ha hl ζ)
  have hval : ∫ ζ, (2 * a / |l| * gau ε ζ + 1 / |l| * wt a l ζ)
      = (2 + ∫ t : ℝ, ((1 + |t|) ^ 2)⁻¹) * (a / |l|) := by
    rw [integral_add (hgi.const_mul _) (hwi.const_mul _), integral_const_mul, integral_const_mul,
      gau_integral ε hε, wt_integral a l ha]
    ring
  exact hmono.trans_eq hval

end GlobalTheory.CompanionTheory.Parseval.OneDim
end
end

section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.Parseval

lemma geom_real (p q r s ζ N D : ℝ) (hD : D = p * s - q * r) (hD0 : D ≠ 0) (hN : 0 ≤ N)
    (h0 : |(s * ζ - r) / D| ≤ N) (h1 : |(p - q * ζ) / D| ≤ N) :
    ((1 + N) ^ 2)⁻¹ ≤ 4 * ((1 + |ζ - (p * q + r * s) / (q ^ 2 + s ^ 2)| /
      (|D| / Real.sqrt (q ^ 2 + s ^ 2))) ^ 2)⁻¹ := by
  have hm : 0 < q ^ 2 + s ^ 2 := by
    rcases eq_or_ne q 0 with hq | hq
    · rcases eq_or_ne s 0 with hs | hs
      · exact absurd (by rw [hD, hq, hs]; ring) hD0
      · positivity
    · positivity
  obtain ⟨m, hmdef⟩ : ∃ m, m = q ^ 2 + s ^ 2 := ⟨_, rfl⟩
  obtain ⟨l, hldef⟩ : ∃ l, l = (p * q + r * s) / (q ^ 2 + s ^ 2) := ⟨_, rfl⟩
  rw [← hldef, ← hmdef]
  rw [← hmdef] at hm
  obtain ⟨t, htdef⟩ : ∃ t, t = |ζ - l| / (|D| / Real.sqrt m) := ⟨_, rfl⟩
  rw [← htdef]
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have hD2 : 0 < D ^ 2 := by positivity
  have ht2 : t ^ 2 = (ζ - l) ^ 2 * m / D ^ 2 := by
    rw [htdef, div_pow, div_pow, sq_abs, sq_abs, Real.sq_sqrt hm.le]
    field_simp
  have hid : (s * ζ - r) ^ 2 + (p - q * ζ) ^ 2 = m * (ζ - l) ^ 2 + D ^ 2 / m := by
    rw [hldef, ← hmdef]
    have hm' : m ≠ 0 := hm.ne'
    field_simp
    rw [hD, hmdef]
    ring
  have hx : ((s * ζ - r) / D) ^ 2 ≤ N ^ 2 := sq_le_sq.2 (by rwa [abs_of_nonneg hN])
  have hy : ((p - q * ζ) / D) ^ 2 ≤ N ^ 2 := sq_le_sq.2 (by rwa [abs_of_nonneg hN])
  have hsum : ((s * ζ - r) / D) ^ 2 + ((p - q * ζ) / D) ^ 2 = t ^ 2 + 1 / m := by
    rw [div_pow, div_pow, ← add_div, hid, ht2]
    field_simp
  have hinv : 0 < 1 / m := by positivity
  have ht4 : t ^ 2 ≤ 2 * N ^ 2 := by linarith
  have ht : t ≤ 2 * N := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hle : (1 + t) ^ 2 ≤ 4 * (1 + N) ^ 2 := by nlinarith
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

theorem dualF_weight_le : ∀ (h : Ad3.LR.M22) (ζ : ℝ), (Matrix.of h).det ≠ 0 →
    ((1 + ‖GlobalTheory.CompanionTheory.Parseval.dualF h ζ‖) ^ 2)⁻¹ ≤ 4 * GlobalTheory.CompanionTheory.Parseval.wt
      (|(Matrix.of h).det| / Real.sqrt (h 0 1 ^ 2 + h 1 1 ^ 2))
      ((h 0 0 * h 0 1 + h 1 0 * h 1 1) / (h 0 1 ^ 2 + h 1 1 ^ 2)) ζ := by
  intro h ζ hD
  have hdet : (Matrix.of h).det = h 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    rw [Matrix.det_fin_two]
    rfl
  have h0 := norm_le_pi_norm (dualF h ζ) 0
  have h1 := norm_le_pi_norm (dualF h ζ) 1
  rw [Real.norm_eq_abs] at h0 h1
  exact geom_real (h 0 0) (h 0 1) (h 1 0) (h 1 1) ζ _ _ hdet hD (norm_nonneg _) h0 h1

end GlobalTheory.CompanionTheory.Parseval
end

section
noncomputable section
open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.Parseval.Max

theorem fz_decay2 (Φ : Sw) (N : ℕ) : ∃ C : ℝ, ∀ (A : M22) (ξ : Fin 2 → ℝ),
    (1 + ‖A‖) ^ N * ((1 + ‖ξ‖) ^ 2 * ‖fz Φ A ξ‖) ≤ C := by
  classical
  have key : ∀ j : Fin 2, ∃ C : ℝ, ∀ (A : M22) (ξ : Fin 2 → ℝ),
      (1 + ‖A‖) ^ N * (|ξ j| ^ 2 * ‖fz Φ A ξ‖) ≤ C := by
    intro j
    obtain ⟨Ψ₁, h₁⟩ := GlobalTheory.CompanionTheory.Parseval.Ibp.main Φ j
    obtain ⟨Ψ₂, h₂⟩ := GlobalTheory.CompanionTheory.Parseval.Ibp.main Ψ₁ j
    obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.Parseval.fz_decay_in_A Ψ₂ N
    refine ⟨C, fun A ξ => ?_⟩
    have e : ‖fz Ψ₂ A ξ‖ = (2 * Real.pi * |ξ j|) ^ 2 * ‖fz Φ A ξ‖ := by
      rw [h₂, h₁, norm_mul, norm_mul]
      have : ‖-(2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ))‖ = 2 * Real.pi * |ξ j| := by
        simp [abs_of_pos Real.pi_pos]
      rw [this]; ring
    have hp : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by
      have := Real.pi_gt_three
      nlinarith
    have hA : 0 ≤ (1 + ‖A‖) ^ N := by positivity
    refine le_trans ?_ (hC A ξ)
    refine mul_le_mul_of_nonneg_left ?_ hA
    rw [e, mul_pow]
    have : 0 ≤ |ξ j| ^ 2 * ‖fz Φ A ξ‖ := by positivity
    nlinarith
  obtain ⟨C₀, h₀⟩ := GlobalTheory.CompanionTheory.Parseval.fz_decay_in_A Φ N
  obtain ⟨C₁, h₁⟩ := key 0
  obtain ⟨C₂, h₂⟩ := key 1
  refine ⟨2 * (C₀ + C₁ + C₂) + 0, fun A ξ => ?_⟩
  have hx : ‖ξ‖ ^ 2 ≤ |ξ 0| ^ 2 + |ξ 1| ^ 2 := by
    have hn : ‖ξ‖ ≤ max |ξ 0| |ξ 1| := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      fin_cases i
      · simpa using le_max_left _ _
      · simpa using le_max_right _ _
    have h2 : ‖ξ‖ ^ 2 ≤ (max |ξ 0| |ξ 1|) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    refine h2.trans ?_
    rcases max_cases |ξ 0| |ξ 1| with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith [sq_nonneg |ξ 0|, sq_nonneg |ξ 1|]
  have hsq : (1 + ‖ξ‖) ^ 2 ≤ 2 * (1 + |ξ 0| ^ 2 + |ξ 1| ^ 2) := by
    nlinarith [sq_nonneg (‖ξ‖ - 1)]
  have hf : 0 ≤ ‖fz Φ A ξ‖ := norm_nonneg _
  have hA : 0 ≤ (1 + ‖A‖) ^ N := by positivity
  have s := h₀ A ξ
  have s1 := h₁ A ξ
  have s2 := h₂ A ξ
  calc (1 + ‖A‖) ^ N * ((1 + ‖ξ‖) ^ 2 * ‖fz Φ A ξ‖)
      ≤ (1 + ‖A‖) ^ N * ((2 * (1 + |ξ 0| ^ 2 + |ξ 1| ^ 2)) * ‖fz Φ A ξ‖) := by gcongr
    _ = 2 * ((1 + ‖A‖) ^ N * ‖fz Φ A ξ‖ + (1 + ‖A‖) ^ N * (|ξ 0| ^ 2 * ‖fz Φ A ξ‖)
          + (1 + ‖A‖) ^ N * (|ξ 1| ^ 2 * ‖fz Φ A ξ‖)) := by ring
    _ ≤ 2 * (C₀ + C₁ + C₂) + 0 := by linarith

theorem parseval_bound_max (Φ : Sw) (N : ℕ) : ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (h : M22) (v : ℝ),
    (Matrix.of h).det ≠ 0 →
    ‖Ae Φ ε h v‖ ≤ C * ((max |(Matrix.of h).det|
      (|h 0 0 * h 0 1 + h 1 0 * h 1 1| / Real.sqrt (h 0 1 ^ 2 + h 1 1 ^ 2)))⁻¹ / (1 + ‖h‖) ^ N) := by
  obtain ⟨C₁, hC₁⟩ := fz_decay2 Φ N
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.CompanionTheory.Parseval.OneDim.wt_gau_bound
  have hC₁0 : 0 ≤ C₁ := le_trans (by positivity) (hC₁ 0 0)
  set K : ℝ := max C₂ 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  refine ⟨C₁ * (1 + 4 * K), fun ε hε _ h v hdet => ?_⟩
  set D : ℝ := |(Matrix.of h).det| with hD
  have hD0 : 0 < D := abs_pos.2 hdet
  set S : ℝ := h 0 0 * h 0 1 + h 1 0 * h 1 1 with hSdef
  set m : ℝ := h 0 1 ^ 2 + h 1 1 ^ 2 with hm
  have hm0 : 0 < m := by
    have : m ≠ 0 := by
      intro h0
      have a1 : h 0 1 = 0 := by nlinarith [sq_nonneg (h 0 1), sq_nonneg (h 1 1)]
      have a2 : h 1 1 = 0 := by nlinarith [sq_nonneg (h 0 1), sq_nonneg (h 1 1)]
      apply hdet
      simp [Matrix.det_fin_two, a1, a2]
    exact lt_of_le_of_ne (by positivity) this.symm
  set n : ℝ := Real.sqrt m with hn
  have hn0 : 0 < n := Real.sqrt_pos.2 hm0
  have hnn : n * n = m := Real.mul_self_sqrt hm0.le
  set P : ℝ := (1 + ‖h‖) ^ N with hP
  have hP0 : 0 < P := by positivity
  set a : ℝ := D / n with ha
  have ha0 : 0 < a := div_pos hD0 hn0
  set l : ℝ := S / m with hl
  have hg : ∀ ζ, ‖gz Φ h ζ‖ ≤ D⁻¹ * C₁ / P * ((1 + ‖dualF h ζ‖) ^ 2)⁻¹ := by
    intro ζ
    rw [GlobalTheory.CompanionTheory.Parseval.gz_eq_fz Φ h ζ hdet, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hD0.le)]
    have := hC₁ h (dualF h ζ)
    have hq : 0 < (1 + ‖dualF h ζ‖) ^ 2 := by positivity
    have h3 : ‖fz Φ h (dualF h ζ)‖ ≤ C₁ / P * ((1 + ‖dualF h ζ‖) ^ 2)⁻¹ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hP0, ← div_eq_mul_inv, le_div_iff₀ hq]
      calc _ = P * ((1 + ‖dualF h ζ‖) ^ 2 * ‖fz Φ h (dualF h ζ)‖) := by ring
        _ ≤ C₁ := this
    calc D⁻¹ * ‖fz Φ h (dualF h ζ)‖ ≤ D⁻¹ * (C₁ / P * ((1 + ‖dualF h ζ‖) ^ 2)⁻¹) := by gcongr
      _ = _ := by ring
  set B : ℝ := D⁻¹ * C₁ / P with hB
  have hB0 : 0 ≤ B := by positivity
  have hnormI : ∀ ζ, ‖(gau ε ζ : ℂ) * Ad3.psiR (ζ * v) * gz Φ h ζ‖ = gau ε ζ * ‖gz Φ h ζ‖ := by
    intro ζ
    have : ‖Ad3.psiR (ζ * v)‖ = 1 := by
      unfold Ad3.psiR
      have : (-2 * (Real.pi : ℂ) * Complex.I * ((ζ * v : ℝ) : ℂ)) = ((-2 * Real.pi * (ζ * v) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, norm_mul, this, Complex.norm_real, Real.norm_of_nonneg (gau_nonneg ε ζ hε)]
    ring
  have b1 : ‖Ae Φ ε h v‖ ≤ B := by
    rw [GlobalTheory.CompanionTheory.Parseval.GaussRep.Ae_eq_integral_gau Φ ε h v hε hdet]
    have : ∀ ζ, ‖(gau ε ζ : ℂ) * Ad3.psiR (ζ * v) * gz Φ h ζ‖ ≤ gau ε ζ * B := by
      intro ζ
      rw [hnormI]
      refine mul_le_mul_of_nonneg_left ((hg ζ).trans ?_) (gau_nonneg ε ζ hε)
      have hi : ((1 + ‖dualF h ζ‖) ^ 2)⁻¹ ≤ 1 := by
        apply inv_le_one_of_one_le₀
        have : 0 ≤ ‖dualF h ζ‖ := norm_nonneg _
        nlinarith
      nlinarith
    refine (norm_integral_le_of_norm_le ((gau_integrable ε hε).mul_const B) (Filter.Eventually.of_forall this)).trans ?_
    rw [integral_mul_const, gau_integral ε hε, one_mul]
  have b2 : S ≠ 0 → ‖Ae Φ ε h v‖ ≤ 4 * K * B * (a / |l|) := by
    intro hS
    have hl0 : l ≠ 0 := div_ne_zero hS hm0.ne'
    have hwm : Measurable (wt a l) := by
      unfold wt
      fun_prop
    have hwi : Integrable (fun ζ => wt a l ζ * gau ε ζ) := by
      refine (gau_integrable ε hε).bdd_mul (c := 1) hwm.aestronglyMeasurable (Filter.Eventually.of_forall fun ζ => ?_)
      rw [Real.norm_of_nonneg (wt_nonneg _ _ _)]
      apply inv_le_one_of_one_le₀
      have : 0 ≤ |ζ - l| / a := by positivity
      nlinarith
    rw [GlobalTheory.CompanionTheory.Parseval.GaussRep.Ae_eq_integral_gau Φ ε h v hε hdet]
    have : ∀ ζ, ‖(gau ε ζ : ℂ) * Ad3.psiR (ζ * v) * gz Φ h ζ‖ ≤ (4 * B) * (wt a l ζ * gau ε ζ) := by
      intro ζ
      rw [hnormI]
      have g1 := GlobalTheory.CompanionTheory.Parseval.dualF_weight_le h ζ hdet
      have g2 : ‖gz Φ h ζ‖ ≤ B * (4 * wt a l ζ) :=
        (hg ζ).trans (mul_le_mul_of_nonneg_left g1 hB0)
      calc gau ε ζ * ‖gz Φ h ζ‖ ≤ gau ε ζ * (B * (4 * wt a l ζ)) :=
            mul_le_mul_of_nonneg_left g2 (gau_nonneg ε ζ hε)
        _ = _ := by ring
    refine (norm_integral_le_of_norm_le (hwi.const_mul (4 * B)) (Filter.Eventually.of_forall this)).trans ?_
    rw [integral_const_mul]
    have o := hC₂ ε a l hε ha0 hl0
    have o2 : ∫ ζ, wt a l ζ * gau ε ζ ≤ K * (a / |l|) :=
      o.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    calc 4 * B * ∫ ζ, wt a l ζ * gau ε ζ ≤ 4 * B * (K * (a / |l|)) :=
          mul_le_mul_of_nonneg_left o2 (by positivity)
      _ = _ := by ring
  have e1 : B = C₁ / P * D⁻¹ := by rw [hB]; ring
  have goal2 : C₁ * (1 + 4 * K) * ((max D (|S| / n))⁻¹ / P) = (C₁ / P) * (1 + 4 * K) * (max D (|S| / n))⁻¹ := by
    ring
  rw [goal2]
  have hQ : 0 ≤ C₁ / P := by positivity
  rcases le_total (|S| / n) D with hle | hle
  · rw [max_eq_left hle]
    calc ‖Ae Φ ε h v‖ ≤ C₁ / P * D⁻¹ := by rw [← e1]; exact b1
      _ ≤ _ := by
        have : 0 ≤ C₁ / P * D⁻¹ * (4 * K) := by positivity
        nlinarith
  · rw [max_eq_right hle]
    have hSpos : 0 < |S| / n := lt_of_lt_of_le hD0 hle
    have hS : S ≠ 0 := by
      intro h0; rw [h0, abs_zero, zero_div] at hSpos; exact lt_irrefl _ hSpos
    have hS' : |S| ≠ 0 := abs_ne_zero.2 hS
    have hal : a / |l| = D * (n / |S|) := by
      rw [ha, hl, abs_div, abs_of_pos hm0, ← hnn]
      field_simp
    have e2 : 4 * K * B * (a / |l|) = 4 * K * (C₁ / P) * (n / |S|) := by
      rw [hal, hB]; field_simp
    rw [inv_div]
    calc ‖Ae Φ ε h v‖ ≤ 4 * K * (C₁ / P) * (n / |S|) := by rw [← e2]; exact b2 hS
      _ ≤ _ := by
        have : 0 ≤ C₁ / P * (n / |S|) := by positivity
        nlinarith

end GlobalTheory.CompanionTheory.Parseval.Max
end
end

section
noncomputable section
open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.Parseval

theorem parseval_bound : Ad3.LR.C.ParsB := fun Φ N => by
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.Parseval.Max.parseval_bound_max Φ N
  exact ⟨C, fun ε hε hε1 h v hdet => by simpa [Dk] using hC ε hε hε1 h v hdet⟩


example : Ad3.LR.C.ParsB := parseval_bound

end GlobalTheory.CompanionTheory.Parseval
end
end
