import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex

noncomputable section

open MeasureTheory Complex Set
open Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.WmFE

def jj (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := (g 1 1 : ℂ) - (g 1 0 : ℂ) * I

def nn (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := (g 0 1 : ℂ) - (g 0 0 : ℂ) * I

lemma range_val : range (Units.val : ℝˣ → ℝ) = {0}ᶜ := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro h
    exact ⟨Units.mk0 x h, rfl⟩

lemma measEmb_val : MeasurableEmbedding (Units.val : ℝˣ → ℝ) := by
  refine ⟨Units.val_injective, comap_measurable _, ?_⟩
  rintro s ⟨t, ht, rfl⟩
  rw [image_preimage_eq_inter_range, range_val]
  exact ht.inter (measurableSet_singleton 0).compl

lemma integral_mulR (f : ℝ → ℂ) :
    ∫ a : ℝˣ, f a ∂mulR = ∫ x in ({0}ᶜ : Set ℝ), ((|x|⁻¹ : ℝ) : ℂ) * f x := by
  have e := measEmb_val
  have hm : Measurable fun x : ℝ => ENNReal.ofReal |x|⁻¹ := by fun_prop
  unfold mulR
  rw [← e.integral_map, e.map_comap, range_val,
    restrict_withDensity (measurableSet_singleton 0).compl,
    integral_withDensity_eq_integral_toReal_smul hm (by simp)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg x))]





lemma real_whittaker_torus_mul (k : ℕ) (g : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ) (h : 0 < a * g.det) :
    Wm k (d2 a * g) = (((a * g.det) ^ ((2 * (k : ℝ) - 1) / 2) : ℝ) : ℂ) *
      (jj g) ^ (-(2 * (k : ℤ) - 1)) * Complex.exp (-2 * Real.pi * I * ((a : ℂ) * nn g / jj g)) := by
  have hdet : (d2 a * g).det = a * g.det := by
    rw [Matrix.det_mul]
    simp [d2, Matrix.det_fin_two_of]
  have e00 : (d2 a * g) 0 0 = a * g 0 0 := by simp [d2, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (d2 a * g) 0 1 = a * g 0 1 := by simp [d2, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (d2 a * g) 1 0 = g 1 0 := by simp [d2, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (d2 a * g) 1 1 = g 1 1 := by simp [d2, Matrix.mul_apply, Fin.sum_univ_two]
  unfold Wm
  rw [hdet, if_pos h, e00, e01, e10, e11]
  simp only [jj, nn]
  push_cast
  congr 3
  ring


lemma integrableOn_rpow_exp {σ b : ℝ} (hσ : -1 < σ) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ σ * Real.exp (-(b * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := σ) (p := 1) (b := b) hσ one_pos hb
  simpa [Real.rpow_one, neg_mul] using h

end GlobalTheory.CompanionTheory.WmFE
