import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableModulusPowOnBoundedUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion

section
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.HoloFamily

theorem abs_le_exp_add_exp_neg (δ y : ℝ) (hδ : 0 < δ) :
    |y| ≤ (Real.exp (δ * y) + Real.exp (-(δ * y))) / δ := by
  rw [le_div_iff₀ hδ]
  have h1 := Real.add_one_le_exp (δ * y)
  have h2 := Real.add_one_le_exp (-(δ * y))
  have e1 := Real.exp_pos (δ * y)
  have e2 := Real.exp_pos (-(δ * y))
  rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith

theorem exp_mul_le_add (a b t y : ℝ) (ha : a ≤ t) (hb : t ≤ b) :
    Real.exp (t * y) ≤ Real.exp (a * y) + Real.exp (b * y) := by
  rcases le_total 0 y with hy | hy
  · have : Real.exp (t * y) ≤ Real.exp (b * y) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb hy)
    have := Real.exp_pos (a * y)
    linarith
  · have : Real.exp (t * y) ≤ Real.exp (a * y) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right ha hy)
    have := Real.exp_pos (b * y)
    linarith

theorem abs_mul_exp_le (σ t y : ℝ) (hσ : 0 < σ) (h1 : 3 * σ / 4 ≤ t) (h2 : t ≤ 5 * σ / 4) :
    |y| * Real.exp (t * y) ≤ (4 / σ) * (Real.exp (σ / 2 * y) + 2 * Real.exp (σ * y)
      + Real.exp (3 * σ / 2 * y)) := by
  have hδ : 0 < σ / 4 := by positivity
  have hA := abs_le_exp_add_exp_neg (σ / 4) y hδ
  have hB := exp_mul_le_add (3 * σ / 4) (5 * σ / 4) t y h1 h2
  have hm := mul_le_mul hA hB (Real.exp_pos _).le
    (div_nonneg (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hδ.le)
  refine hm.trans (le_of_eq ?_)
  have e1 : Real.exp (σ / 4 * y) * Real.exp (3 * σ / 4 * y) = Real.exp (σ * y) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (σ / 4 * y) * Real.exp (5 * σ / 4 * y) = Real.exp (3 * σ / 2 * y) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (-(σ / 4 * y)) * Real.exp (3 * σ / 4 * y) = Real.exp (σ / 2 * y) := by
    rw [← Real.exp_add]; congr 1; ring
  have e4 : Real.exp (-(σ / 4 * y)) * Real.exp (5 * σ / 4 * y) = Real.exp (σ * y) := by
    rw [← Real.exp_add]; congr 1; ring
  have : (Real.exp (σ / 4 * y) + Real.exp (-(σ / 4 * y))) / (σ / 4) *
      (Real.exp (3 * σ / 4 * y) + Real.exp (5 * σ / 4 * y))
      = (4 / σ) * (Real.exp (σ / 4 * y) * Real.exp (3 * σ / 4 * y)
        + Real.exp (σ / 4 * y) * Real.exp (5 * σ / 4 * y)
        + Real.exp (-(σ / 4 * y)) * Real.exp (3 * σ / 4 * y)
        + Real.exp (-(σ / 4 * y)) * Real.exp (5 * σ / 4 * y)) := by
    field_simp
    ring
  rw [this, e1, e2, e3, e4]
  ring

theorem differentiableOn_integral_mul_cexp
    {X : Type} [MeasurableSpace X] (μ : Measure X) (G : X → ℂ) (L : X → ℝ)
    (hG : AEStronglyMeasurable G μ) (hL : Measurable L)
    (hI : ∀ σ : ℝ, 0 < σ → Integrable (fun x => ‖G x‖ * Real.exp (σ * L x)) μ) :
    DifferentiableOn ℂ (fun u : ℂ => ∫ x, G x * Complex.exp (u * (L x : ℂ)) ∂μ)
      {u : ℂ | 0 < u.re} := by
  intro u₀ hu₀
  have hσ : 0 < u₀.re := hu₀
  set σ := u₀.re with hσdef
  have hLc : Measurable fun x => (L x : ℂ) := Complex.measurable_ofReal.comp hL
  have hmeas : ∀ u : ℂ, AEStronglyMeasurable (fun x => G x * Complex.exp (u * (L x : ℂ))) μ :=
    fun u => hG.mul ((Complex.measurable_exp.comp (hLc.const_mul u)).aestronglyMeasurable)
  have hmeas' : ∀ u : ℂ, AEStronglyMeasurable
      (fun x => G x * (L x : ℂ) * Complex.exp (u * (L x : ℂ))) μ :=
    fun u => (hG.mul hLc.aestronglyMeasurable).mul
      ((Complex.measurable_exp.comp (hLc.const_mul u)).aestronglyMeasurable)
  have hnorm : ∀ (u : ℂ) (x : X), ‖Complex.exp (u * (L x : ℂ))‖ = Real.exp (u.re * L x) := by
    intro u x
    rw [Complex.norm_exp]
    simp
  have hF_int : Integrable (fun x => G x * Complex.exp (u₀ * (L x : ℂ))) μ := by
    refine (hI σ hσ).mono' (hmeas u₀) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, hnorm]
  let bound : X → ℝ := fun x => (4 / σ) * (‖G x‖ * Real.exp (σ / 2 * L x)
    + 2 * (‖G x‖ * Real.exp (σ * L x)) + ‖G x‖ * Real.exp (3 * σ / 2 * L x))
  have hbound : Integrable bound μ :=
    (((hI (σ / 2) (by positivity)).add ((hI σ hσ).const_mul 2)).add
      (hI (3 * σ / 2) (by positivity))).const_mul (4 / σ)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (u : ℂ) x => G x * Complex.exp (u * (L x : ℂ)))
    (F' := fun (u : ℂ) x => G x * (L x : ℂ) * Complex.exp (u * (L x : ℂ)))
    (x₀ := u₀) (s := Metric.ball u₀ (σ / 4)) (bound := bound)
    (Metric.ball_mem_nhds u₀ (by positivity))
    (Filter.Eventually.of_forall hmeas) hF_int (hmeas' u₀)
    (Filter.Eventually.of_forall fun x u hu => ?_) hbound
    (Filter.Eventually.of_forall fun x u _ => ?_)
  · exact hmain.2.differentiableAt.differentiableWithinAt
  · have hre : |u.re - σ| < σ / 4 := by
      have h1 : ‖u - u₀‖ < σ / 4 := by simpa [dist_eq_norm] using hu
      have h2 : |(u - u₀).re| ≤ ‖u - u₀‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re] at h2
      exact lt_of_le_of_lt h2 h1
    have hab := abs_lt.mp hre
    have hb := abs_mul_exp_le σ u.re (L x) hσ (by linarith [hab.1]) (by linarith [hab.2])
    have hnG := norm_nonneg (G x)
    calc ‖G x * (L x : ℂ) * Complex.exp (u * (L x : ℂ))‖
        = ‖G x‖ * (|L x| * Real.exp (u.re * L x)) := by
          rw [norm_mul, norm_mul, hnorm, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
      _ ≤ ‖G x‖ * ((4 / σ) * (Real.exp (σ / 2 * L x) + 2 * Real.exp (σ * L x)
            + Real.exp (3 * σ / 2 * L x))) := mul_le_mul_of_nonneg_left hb hnG
      _ = bound x := by simp only [bound]; ring
  · have h1 : HasDerivAt (fun w : ℂ => w * (L x : ℂ)) (L x : ℂ) u := by
      simpa using (hasDerivAt_id u).mul_const (L x : ℂ)
    exact ((h1.cexp).const_mul (G x)).congr_deriv (by ring)

end GlobalTheory.CompanionTheory.HoloFamily
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_laplace_integral_right_half : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (G : X → ℂ) (L : X → ℝ), AEStronglyMeasurable G μ → Measurable L → (∀ σ : ℝ, 0 < σ → Integrable (fun x => ‖G x‖ * Real.exp (σ * L x)) μ) → DifferentiableOn ℂ (fun u : ℂ => ∫ x, G x * Complex.exp (u * (L x : ℂ)) ∂μ) {u : ℂ | 0 < u.re} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.HoloFamily.differentiableOn_integral_mul_cexp
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_modulus_pow_on_bounded_units : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (δ B : ℝ), 0 < δ → Integrable (fun a : Fˣ => Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B} (fun a : Fˣ => (modulus (a : F) : ℝ) ^ δ) a) (multHaar F) := by
  first | exact @GlobalTheory.CompanionTheory.ModulusWeight.integrable_modulus_rpow_indicator | exact GlobalTheory.CompanionTheory.ModulusWeight.integrable_modulus_rpow_indicator | (intros; apply GlobalTheory.CompanionTheory.ModulusWeight.integrable_modulus_rpow_indicator <;> assumption)
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

noncomputable section

namespace GlobalTheory.CompanionTheory.DualHol.Coord

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem det_blk (h : GL (Fin 2) F) :
    (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F).det
      = (h.val).det := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two, Fin.succAbove]

theorem em_coe (h : GL (Fin 2) F) : (GL2LocalData.em h).val =
    !![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] := by
  have hd : (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    rw [det_blk]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero
  unfold GL2LocalData.em
  rw [dif_pos hd]
  rfl

theorem em_mul (g h : GL (Fin 2) F) : GL2LocalData.em (g * h) = GL2LocalData.em g * GL2LocalData.em h := by
  apply Units.ext
  rw [Units.val_mul, em_coe, em_coe, em_coe, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem em_one : GL2LocalData.em (1 : GL (Fin 2) F) = 1 := by
  apply Units.ext
  rw [em_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem em_inv (g : GL (Fin 2) F) : (GL2LocalData.em g)⁻¹ = GL2LocalData.em g⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [← em_mul, mul_inv_cancel, em_one]

theorem tinv_mul' {n : ℕ} (g h : GL (Fin n) F) : GL2LocalData.tinv (g * h) = GL2LocalData.tinv g * GL2LocalData.tinv h := by
  apply Units.ext
  show ((g * h)⁻¹ : GL (Fin n) F).val.transpose =
    (g⁻¹ : GL (Fin n) F).val.transpose * (h⁻¹ : GL (Fin n) F).val.transpose
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem tinv_mem' {n : ℕ} {k : GL (Fin n) F} (hk : k ∈ GLnLocal.integralGL F n) :
    GL2LocalData.tinv k ∈ GLnLocal.integralGL F n := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F n).1 hk
  exact (GLnLocal.mem_integralGL_iff F n).2 ⟨fun i j => h2 j i, fun i j => h1 j i⟩

theorem long_weyl2_mem_integral_GL : (GL2LocalData.w2 : GL (Fin 2) F) ∈ GLnLocal.integralGL F 2 := by
  refine (GLnLocal.mem_integralGL_iff F 2).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F]
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]
  · show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F]
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]

theorem long_weyl3_mem_integral_GL : (GL2LocalData.w3 : GL (Fin 3) F) ∈ GLnLocal.integralGL F 3 := by
  refine (GLnLocal.mem_integralGL_iff F 3).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · show (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) F) i j ∈ 𝒪[F]
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]
  · show (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) F) i j ∈ 𝒪[F]
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]

theorem em_mem {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    GL2LocalData.em k ∈ GLnLocal.integralGL F 3 := by
  have key : ∀ {g : GL (Fin 2) F}, (∀ i j, g.val i j ∈ 𝒪[F]) → ∀ i j, (GL2LocalData.em g).val i j ∈ 𝒪[F] := by
    intro g hg i j
    rw [em_coe]
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem, hg]
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  refine (GLnLocal.mem_integralGL_iff F 3).2 ⟨key h1, ?_⟩
  rw [em_inv]
  exact key h2

theorem diag_pair_inv (x y : Fˣ) : (dg2 x y)⁻¹ = dg2 x⁻¹ y⁻¹ := by
  apply Units.ext
  rfl

theorem long_weyl3_mul_transpose_inv_embed_diag (x y : Fˣ) :
    (GL2LocalData.w3 : GL (Fin 3) F) * GL2LocalData.tinv (GL2LocalData.em (dg2 x y)) = dg 1 y⁻¹ x⁻¹ * GL2LocalData.w3 := by
  apply Units.ext
  have h : (GL2LocalData.tinv (GL2LocalData.em (dg2 x y))).val = (GL2LocalData.em (dg2 x⁻¹ y⁻¹)).val.transpose := by
    show ((GL2LocalData.em (dg2 x y))⁻¹ : GL (Fin 3) F).val.transpose = _
    rw [em_inv, diag_pair_inv]
  rw [Units.val_mul, Units.val_mul, h, em_coe]
  show (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) F) * _ =
    (!![((1 : Fˣ) : F), 0, 0; 0, ((y⁻¹ : Fˣ) : F), 0; 0, 0, ((x⁻¹ : Fˣ) : F)] : Matrix (Fin 3) (Fin 3) F) *
      !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, dg2]

theorem long_weyl2_mul_transpose_inv_diag_pair (x y : Fˣ) :
    (GL2LocalData.w2 : GL (Fin 2) F) * GL2LocalData.tinv (dg2 x y) = dg2 y⁻¹ x⁻¹ * GL2LocalData.w2 := by
  apply Units.ext
  have h : (GL2LocalData.tinv (dg2 x y)).val = (dg2 x⁻¹ y⁻¹).val.transpose := by
    show ((dg2 x y)⁻¹ : GL (Fin 2) F).val.transpose = _
    rw [diag_pair_inv]
  rw [Units.val_mul, Units.val_mul, h]
  show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * _ =
    (!![((y⁻¹ : Fˣ) : F), 0; 0, ((x⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; 1, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, dg2]

theorem coords : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a b : Fˣ) (k : GL (Fin 2) F), k ∈ GLnLocal.integralGL F 2 → ∃ k₃ ∈ GLnLocal.integralGL F 3, ∃ k₂ ∈ GLnLocal.integralGL F 2, (∀ W : GL (Fin 3) F → ℂ, GL2LocalData.dW3 W (GL2LocalData.em (dg2 (a * b) b * k)) = W (dg 1 b⁻¹ (a * b)⁻¹ * k₃)) ∧ (∀ W' : GL (Fin 2) F → ℂ, GL2LocalData.dW2 W' (dg2 (a * b) b * k) = W' (dg2 b⁻¹ (a * b)⁻¹ * k₂)) := by
  intro F _ _ _ _ a b k hk
  refine ⟨GL2LocalData.w3 * GL2LocalData.tinv (GL2LocalData.em k), mul_mem long_weyl3_mem_integral_GL (tinv_mem' (em_mem hk)),
    GL2LocalData.w2 * GL2LocalData.tinv k, mul_mem long_weyl2_mem_integral_GL (tinv_mem' hk), fun W => ?_, fun W' => ?_⟩
  · show W (GL2LocalData.w3 * GL2LocalData.tinv (GL2LocalData.em (dg2 (a * b) b * k))) = _
    rw [em_mul, tinv_mul', ← mul_assoc, long_weyl3_mul_transpose_inv_embed_diag, mul_assoc]
  · show W' (GL2LocalData.w2 * GL2LocalData.tinv (dg2 (a * b) b * k)) = _
    rw [tinv_mul', ← mul_assoc, long_weyl2_mul_transpose_inv_diag_pair, mul_assoc]

end GlobalTheory.CompanionTheory.DualHol.Coord
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_whittaker_iwasawa_coordinates : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a b : Fˣ) (k : GL (Fin 2) F), k ∈ GLnLocal.integralGL F 2 → ∃ k₃ ∈ GLnLocal.integralGL F 3, ∃ k₂ ∈ GLnLocal.integralGL F 2, (∀ W : GL (Fin 3) F → ℂ, GL2LocalData.dW3 W (GL2LocalData.em (dg2 (a * b) b * k)) = W (dg 1 b⁻¹ (a * b)⁻¹ * k₃)) ∧ (∀ W' : GL (Fin 2) F → ℂ, GL2LocalData.dW2 W' (dg2 (a * b) b * k) = W' (dg2 b⁻¹ (a * b)⁻¹ * k₂)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.DualHol.Coord.coords
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

noncomputable section

namespace GlobalTheory.CompanionTheory.DualHol.IwMeas

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem continuous_diag_torus_GL2 : Continuous (fun q : Fˣ × Fˣ => (dg2 q.1 q.2 : GL (Fin 2) F)) := by
  have hv1 : Continuous (fun q : Fˣ × Fˣ => (q.1 : F)) := Units.continuous_val.comp continuous_fst
  have hv2 : Continuous (fun q : Fˣ × Fˣ => (q.2 : F)) := Units.continuous_val.comp continuous_snd
  have hi1 : Continuous (fun q : Fˣ × Fˣ => ((q.1⁻¹ : Fˣ) : F)) :=
    (Units.continuous_iff.1 continuous_id).2.comp continuous_fst
  have hi2 : Continuous (fun q : Fˣ × Fˣ => ((q.2⁻¹ : Fˣ) : F)) :=
    (Units.continuous_iff.1 continuous_id).2.comp continuous_snd
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    show Continuous fun q : Fˣ × Fˣ => (!![(q.1 : F), 0; 0, (q.2 : F)] : Matrix (Fin 2) (Fin 2) F) i j
    fin_cases i <;> fin_cases j <;> first | (simpa using hv1) | (simpa using hv2) | (simpa using continuous_const)
  · refine continuous_matrix fun i j => ?_
    show Continuous fun q : Fˣ × Fˣ =>
      (!![((q.1⁻¹ : Fˣ) : F), 0; 0, ((q.2⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F) i j
    fin_cases i <;> fin_cases j <;> first | (simpa using hi1) | (simpa using hi2) | (simpa using continuous_const)

theorem continuous_tinv {n : Type} [Fintype n] [DecidableEq n] :
    Continuous (GL2LocalData.tinv : GL n F → GL n F) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun g : GL n F => Matrix.transpose (g⁻¹ : GL n F).val
    exact (Units.continuous_iff.1 continuous_id).2.matrix_transpose
  · show Continuous fun g : GL n F => Matrix.transpose g.val
    exact Units.continuous_val.matrix_transpose

theorem em_inv (h : GL (Fin 2) F) : GL2LocalData.em h⁻¹ = (GL2LocalData.em h)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
  have h1 : (h⁻¹).val * h.val = 1 := by rw [← Units.val_mul]; simp
  have e : ∀ i j, (h⁻¹).val i 0 * h.val 0 j + (h⁻¹).val i 1 * h.val 1 j = (1 : Matrix (Fin 2) (Fin 2) F) i j := by
    intro i j
    have := congr_fun (congr_fun h1 i) j
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  rw [Units.val_mul, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.em_val, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.em_val]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, e00, e01, e10, e11]

theorem continuous_em : Continuous (GL2LocalData.em : GL (Fin 2) F → GL (Fin 3) F) := by
  have hv : ∀ i j, Continuous fun h : GL (Fin 2) F => h.val i j := fun i j =>
    (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) F)).matrix_elem i j
  have hi : ∀ i j, Continuous fun h : GL (Fin 2) F => (h⁻¹).val i j := fun i j =>
    (Units.continuous_iff.1 (continuous_id (X := GL (Fin 2) F))).2.matrix_elem i j
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    show Continuous fun h : GL (Fin 2) F => (GL2LocalData.em h).val i j
    simp only [GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.em_val]
    fin_cases i <;> fin_cases j <;> first | (simpa using hv _ _) | (simpa using continuous_const)
  · refine continuous_matrix fun i j => ?_
    show Continuous fun h : GL (Fin 2) F => ((GL2LocalData.em h)⁻¹).val i j
    simp only [← em_inv, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.em_val]
    fin_cases i <;> fin_cases j <;> first | (simpa using hi _ _) | (simpa using continuous_const)

end

theorem measurable_dual_iwasawa : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ), Continuous W → Measurable W' → Measurable (fun p : Fˣ × Fˣ × GL (Fin 2) F => GL2LocalData.dW3 W (GL2LocalData.em (dg2 (p.1 * p.2.1) p.2.1 * p.2.2)) * GL2LocalData.dW2 W' (dg2 (p.1 * p.2.1) p.2.1 * p.2.2)) := by
  intro F _ _ _ _ _ _ W W' hW hW'
  have hΦ : Continuous (fun p : Fˣ × Fˣ × GL (Fin 2) F => (dg2 (p.1 * p.2.1) p.2.1 * p.2.2 : GL (Fin 2) F)) :=
    (continuous_diag_torus_GL2.comp
      ((continuous_fst.mul (continuous_fst.comp continuous_snd)).prodMk
        (continuous_fst.comp continuous_snd))).mul (continuous_snd.comp continuous_snd)
  have h3 : Continuous (fun g : GL (Fin 2) F => GL2LocalData.dW3 W (GL2LocalData.em g)) :=
    hW.comp (continuous_const.mul (continuous_tinv.comp continuous_em))
  have h2 : Continuous (fun g : GL (Fin 2) F => (GL2LocalData.w2 * GL2LocalData.tinv g : GL (Fin 2) F)) :=
    continuous_const.mul continuous_tinv
  have m3 := (h3.comp hΦ).measurable
  have m2 : Measurable (fun g : GL (Fin 2) F => GL2LocalData.dW2 W' g) := hW'.comp h2.measurable
  exact m3.mul (m2.comp hΦ.measurable)

end GlobalTheory.CompanionTheory.DualHol.IwMeas
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_dual_rankin_selberg_integrand : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ), Continuous W → Measurable W' → Measurable (fun p : Fˣ × Fˣ × GL (Fin 2) F => GL2LocalData.dW3 W (GL2LocalData.em (dg2 (p.1 * p.2.1) p.2.1 * p.2.2)) * GL2LocalData.dW2 W' (dg2 (p.1 * p.2.1) p.2.1 * p.2.2)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.DualHol.IwMeas.measurable_dual_iwasawa
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

noncomputable section

namespace GlobalTheory.CompanionTheory.DualHolo

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem mp_eq_exp (a : Fˣ) (s : ℂ) :
    mp a s = Complex.exp (((Real.log (modulus (a : F) : ℝ) : ℝ) : ℂ) * s) := by
  have h0 : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  have h1 : (((modulus (a : F) : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  simp only [mp]
  rw [Complex.cpow_def_of_ne_zero h1, Complex.ofReal_log h0.le]

theorem norm_mp' (a : Fˣ) (z : ℂ) : ‖mp a z‖ = (modulus (a : F) : ℝ) ^ z.re := by
  have h0 : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  simp only [mp]
  exact Complex.norm_cpow_eq_rpow_re_of_pos h0 z

theorem modulus_mul' (a b : Fˣ) :
    (modulus ((a * b : Fˣ) : F) : ℝ) = (modulus (a : F) : ℝ) * (modulus (b : F) : ℝ) := by
  rw [Units.val_mul, modulus_mul]
  push_cast
  rfl

theorem exponents {A B σ ε : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (A * B) ^ (1 - ε) * A ^ (1 / 2 - ε) * A ^ (-(3 / 2) : ℝ) * B ^ (-1 : ℝ) * (A ^ σ * B ^ (2 * σ)) =
      A ^ (σ - 2 * ε) * B ^ (2 * σ - ε) := by
  have e1 : A ^ (σ - 2 * ε) = A ^ (1 - ε) * A ^ (1 / 2 - ε) * A ^ (-(3 / 2) : ℝ) * A ^ σ := by
    rw [← Real.rpow_add hA, ← Real.rpow_add hA, ← Real.rpow_add hA]
    congr 1
    ring
  have e2 : B ^ (2 * σ - ε) = B ^ (1 - ε) * B ^ (-1 : ℝ) * B ^ (2 * σ) := by
    rw [← Real.rpow_add hB, ← Real.rpow_add hB]
    congr 1
    ring
  rw [e1, e2, Real.mul_rpow hA.le hB.le]
  ring

end

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def gI (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ) (p : Fˣ × Fˣ × GL (Fin 2) F) : ℂ :=
  GL2LocalData.dW3 W (GL2LocalData.em (dg2 (p.1 * p.2.1) p.2.1 * p.2.2)) * GL2LocalData.dW2 W' (dg2 (p.1 * p.2.1) p.2.1 * p.2.2) *
    mp p.1 (-(3 / 2)) * mp p.2.1 (-1)

def lI (p : Fˣ × Fˣ × GL (Fin 2) F) : ℝ :=
  Real.log (modulus (p.1 : F) : ℝ) + 2 * Real.log (modulus (p.2.1 : F) : ℝ)

theorem measurable_lI : Measurable (lI (F := F)) := by
  have hl : Measurable (fun a : Fˣ => Real.log (modulus (a : F) : ℝ)) :=
    Real.measurable_log.comp (NNReal.continuous_coe.comp
      (continuous_modulus.comp Units.continuous_val)).measurable
  exact (hl.comp measurable_fst).add ((hl.comp (measurable_fst.comp measurable_snd)).const_mul 2)

theorem measurable_gI {W : GL (Fin 3) F → ℂ} {W' : GL (Fin 2) F → ℂ} (h3 : TemperedBoundGL3 W) (h2 : TemperedBoundGL2 W') :
    Measurable (gI W W') := by
  have hc : ∀ z : ℂ, Measurable (fun a : Fˣ => mp a z) := fun z => by
    have h1 : Continuous (fun a : Fˣ => (((modulus (a : F) : ℝ)) : ℂ)) :=
      Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
        (continuous_modulus.comp Units.continuous_val))
    refine (h1.cpow continuous_const fun a => Or.inl ?_).measurable
    have : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
    simpa using this
  exact ((GlobalTheory.T.measurable_dual_rankin_selberg_integrand F W W' h3.1 h2.1).mul ((hc _).comp measurable_fst)).mul
    ((hc _).comp (measurable_fst.comp measurable_snd))

theorem ae_mem_maximal_compact (ψ : AddChar F Circle) [SFinite ((Ad3.LFS.hG ψ).restrict (GL2LocalData.K2 F))] :
    ∀ᵐ p ∂GL2LocalData.mIw ψ, p.2.2 ∈ GL2LocalData.K2 F := by
  have hKm : MeasurableSet (GL2LocalData.K2 F) := (GLnLocal.isCompact_integralGL F 2).isClosed.measurableSet
  have h0 : ∀ᵐ k ∂((Ad3.LFS.hG ψ).restrict (GL2LocalData.K2 F)), k ∈ GL2LocalData.K2 F := ae_restrict_mem hKm
  have h1 : ∀ᵐ z ∂((multHaar F).prod ((Ad3.LFS.hG ψ).restrict (GL2LocalData.K2 F))), z.2 ∈ GL2LocalData.K2 F :=
    Measure.quasiMeasurePreserving_snd.ae h0
  exact Measure.quasiMeasurePreserving_snd.ae h1

theorem bound_gI {W : GL (Fin 3) F → ℂ} {W' : GL (Fin 2) F → ℂ} {ε σ C₃ B₃ C₂ : ℝ}
    (hb₃ : ∀ (t₁ t₂ t₃ : Fˣ), ∀ k ∈ GLnLocal.integralGL F 3,
      ‖W (dg t₁ t₂ t₃ * k)‖ ≤ C₃ * (modulus ((t₁ / t₃ : Fˣ) : F) : ℝ) ^ (1 - ε) ∧
      (W (dg t₁ t₂ t₃ * k) ≠ 0 →
        (modulus ((t₁ / t₂ : Fˣ) : F) : ℝ) ≤ B₃ ∧ (modulus ((t₂ / t₃ : Fˣ) : F) : ℝ) ≤ B₃))
    (hb₂ : ∀ (x y : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
      ‖W' (dg2 x y * k)‖ ≤ C₂ * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 - ε))
    (p : Fˣ × Fˣ × GL (Fin 2) F) (hp : p.2.2 ∈ GL2LocalData.K2 F) :
    ‖gI W W' p‖ * Real.exp (σ * lI p) ≤ (max C₃ 0 * max C₂ 0) *
      (Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B₃} (fun a : Fˣ => (modulus (a : F) : ℝ) ^ (σ - 2 * ε)) p.1 *
      (Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B₃} (fun a : Fˣ => (modulus (a : F) : ℝ) ^ (2 * σ - ε)) p.2.1 * 1)) := by
  obtain ⟨a, b, k⟩ := p
  obtain ⟨k₃, hk₃, k₂, hk₂, e3, e2⟩ := GlobalTheory.T.dual_whittaker_iwasawa_coordinates F a b k hp
  have hA : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  have hB : (0 : ℝ) < (modulus (b : F) : ℝ) := by exact_mod_cast modulus_pos b.ne_zero
  have q1 : ((1 : Fˣ) / (a * b)⁻¹) = a * b := by simp
  have q2 : ((1 : Fˣ) / b⁻¹) = b := by simp
  have q3 : (b⁻¹ / (a * b)⁻¹ : Fˣ) = a := by
    rw [div_inv_eq_mul, mul_comm a b, inv_mul_cancel_left]
  obtain ⟨n3, s3⟩ := hb₃ 1 b⁻¹ (a * b)⁻¹ k₃ hk₃
  have n2 := hb₂ b⁻¹ (a * b)⁻¹ k₂ hk₂
  rw [q1, modulus_mul'] at n3
  rw [q2, q3] at s3
  rw [q3] at n2
  have hRHS : ∀ x : Fˣ, ∀ δ : ℝ, 0 ≤ Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B₃}
      (fun a : Fˣ => (modulus (a : F) : ℝ) ^ δ) x :=
    fun x δ => Set.indicator_nonneg (fun _ _ => by positivity) x
  simp only [gI, lI, e3, e2]
  set x := W (dg 1 b⁻¹ (a * b)⁻¹ * k₃) with hx
  set y := W' (dg2 b⁻¹ (a * b)⁻¹ * k₂) with hy
  by_cases hx0 : x = 0
  · rw [hx0]
    simp only [zero_mul, norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (hRHS _ _) (mul_nonneg (hRHS _ _) zero_le_one))
  obtain ⟨sb, sa⟩ := s3 hx0
  rw [Set.indicator_of_mem (show a ∈ {a : Fˣ | (modulus (a : F) : ℝ) ≤ B₃} from sa),
    Set.indicator_of_mem (show b ∈ {a : Fˣ | (modulus (a : F) : ℝ) ≤ B₃} from sb), mul_one]
  set A : ℝ := (modulus (a : F) : ℝ) with hAd
  set B : ℝ := (modulus (b : F) : ℝ) with hBd
  have hE : Real.exp (σ * (Real.log A + 2 * Real.log B)) = A ^ σ * B ^ (2 * σ) := by
    rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB, ← Real.exp_add]
    congr 1
    ring
  have hr1 : (-(3 / 2) : ℂ).re = -(3 / 2) := by norm_num
  have hr2 : (-1 : ℂ).re = -1 := by norm_num
  rw [norm_mul, norm_mul, norm_mul, norm_mp', norm_mp', hr1, hr2, hE, ← hAd, ← hBd]
  have m3 : ‖x‖ ≤ max C₃ 0 * (A * B) ^ (1 - ε) :=
    n3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have m2 : ‖y‖ ≤ max C₂ 0 * A ^ (1 / 2 - ε) :=
    n2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hm := mul_le_mul m3 m2 (norm_nonneg _) (by positivity)
  calc ‖x‖ * ‖y‖ * A ^ (-(3 / 2) : ℝ) * B ^ (-1 : ℝ) * (A ^ σ * B ^ (2 * σ))
      ≤ (max C₃ 0 * (A * B) ^ (1 - ε)) * (max C₂ 0 * A ^ (1 / 2 - ε)) * A ^ (-(3 / 2) : ℝ) * B ^ (-1 : ℝ) *
          (A ^ σ * B ^ (2 * σ)) := by gcongr
    _ = (max C₃ 0 * max C₂ 0) * ((A * B) ^ (1 - ε) * A ^ (1 / 2 - ε) * A ^ (-(3 / 2) : ℝ) * B ^ (-1 : ℝ) *
          (A ^ σ * B ^ (2 * σ))) := by ring
    _ = _ := by rw [exponents hA hB]

theorem integrable_gI (ψ : AddChar F Circle) {W : GL (Fin 3) F → ℂ} {W' : GL (Fin 2) F → ℂ}
    (h3 : TemperedBoundGL3 W) (h2 : TemperedBoundGL2 W') (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun p => ‖gI W W' p‖ * Real.exp (σ * lI p)) (GL2LocalData.mIw ψ) := by
  haveI hμ : (Ad3.LFS.hG ψ).IsHaarMeasure := by unfold Ad3.LFS.hG; infer_instance
  have hKc := GLnLocal.isCompact_integralGL F 2
  haveI : IsFiniteMeasure ((Ad3.LFS.hG ψ).restrict (GL2LocalData.K2 F)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
  set ε : ℝ := min (1 / 4) (σ / 4) with hε
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  have hε2 : ε ≤ σ / 4 := min_le_right _ _
  obtain ⟨C₃, B₃, hb₃⟩ := h3.2 ε hε0 hε1
  obtain ⟨C₂, B₂, hb₂⟩ := h2.2 ε hε0 hε1
  have hi₁ := GlobalTheory.T.integrable_modulus_pow_on_bounded_units F (σ - 2 * ε) B₃ (by linarith)
  have hi₂ := GlobalTheory.T.integrable_modulus_pow_on_bounded_units F (2 * σ - ε) B₃ (by linarith)
  have hi₃ : Integrable (fun _ : GL (Fin 2) F => (1 : ℝ)) ((Ad3.LFS.hG ψ).restrict (GL2LocalData.K2 F)) :=
    integrable_const _
  have hprod := (hi₁.mul_prod (hi₂.mul_prod hi₃)).const_mul (max C₃ 0 * max C₂ 0)
  have hmeas : AEStronglyMeasurable (fun p => ‖gI W W' p‖ * Real.exp (σ * lI p)) (GL2LocalData.mIw ψ) :=
    ((measurable_gI h3 h2).norm.mul
      (Real.measurable_exp.comp (measurable_lI.const_mul σ))).aestronglyMeasurable
  refine Integrable.mono' hprod hmeas ?_
  filter_upwards [ae_mem_maximal_compact ψ] with p hp
  rw [Real.norm_of_nonneg (by positivity)]
  exact bound_gI hb₃ (fun x y k hk => (hb₂ x y k hk).1) p hp

theorem iw_eq (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ) (u : ℂ) (p : Fˣ × Fˣ × GL (Fin 2) F) :
    GL2LocalData.iw (GL2LocalData.dW3 W) (GL2LocalData.dW2 W') u p = gI W W' p * Complex.exp (u * (lI p : ℂ)) := by
  simp only [GL2LocalData.iw, gI, lI, mp_eq_exp]
  push_cast
  have e : Complex.exp (((Real.log (modulus (p.1 : F) : ℝ) : ℝ) : ℂ) * (u - 3 / 2)) *
      Complex.exp (((Real.log (modulus (p.2.1 : F) : ℝ) : ℝ) : ℂ) * (2 * u - 1)) =
      Complex.exp (((Real.log (modulus (p.1 : F) : ℝ) : ℝ) : ℂ) * (-(3 / 2))) *
      Complex.exp (((Real.log (modulus (p.2.1 : F) : ℝ) : ℝ) : ℂ) * (-1)) *
      Complex.exp (u * (((Real.log (modulus (p.1 : F) : ℝ) : ℝ) : ℂ) +
        2 * ((Real.log (modulus (p.2.1 : F) : ℝ) : ℝ) : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [mul_assoc _ (Complex.exp _) (Complex.exp _), e]
  ring

theorem holo : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ), TemperedBoundGL3 W → TemperedBoundGL2 W' → DifferentiableOn ℂ (fun u => GL2LocalData.zetaGL3GL2 ψ (GL2LocalData.dW3 W) (GL2LocalData.dW2 W') u) {u : ℂ | 0 < u.re} := by
  intro F _ _ _ _ _ _ ψ W W' h3 h2
  have key := GlobalTheory.T.differentiableOn_laplace_integral_right_half (GL2LocalData.mIw ψ) (gI W W') lI (measurable_gI h3 h2).aestronglyMeasurable
    measurable_lI (integrable_gI ψ h3 h2)
  refine key.congr fun u _ => ?_
  simp only [GL2LocalData.zetaGL3GL2, iw_eq]

end GlobalTheory.CompanionTheory.DualHolo
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_zetaGL3GL2_dual : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ), TemperedBoundGL3 W → TemperedBoundGL2 W' → DifferentiableOn ℂ (fun u => GL2LocalData.zetaGL3GL2 ψ (GL2LocalData.dW3 W) (GL2LocalData.dW2 W') u) {u : ℂ | 0 < u.re} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.DualHolo.holo
end
