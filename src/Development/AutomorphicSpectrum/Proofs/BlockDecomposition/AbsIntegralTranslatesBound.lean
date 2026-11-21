import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanTateIntegral
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex

section
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
end
end

section
noncomputable section

open MeasureTheory Complex Set
open Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.AbsWm

open GlobalTheory.CompanionTheory.WmFE (jj nn)

lemma re_I_nn_div (g : Matrix (Fin 2) (Fin 2) ℝ) :
    (I * nn g / jj g).re = g.det / normSq (jj g) := by
  rw [Complex.div_re]
  simp [nn, jj, Matrix.det_fin_two]
  ring

lemma norm_exp_kernel (g : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ) :
    ‖Complex.exp (-2 * Real.pi * I * ((a : ℂ) * nn g / jj g))‖ =
      Real.exp (-(2 * Real.pi * (a * g.det) / normSq (jj g))) := by
  rw [Complex.norm_exp]
  congr 1
  have h : -2 * (Real.pi : ℂ) * I * ((a : ℂ) * nn g / jj g) =
      ((-2 * Real.pi * a : ℝ) : ℂ) * (I * nn g / jj g) := by
    push_cast
    ring
  rw [h, Complex.re_ofReal_mul, re_I_nn_div]
  ring

lemma norm_Wm (k : ℕ) (g : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ) (h : 0 < a * g.det) :
    ‖Wm k (d2 a * g)‖ = (a * g.det) ^ ((2 * (k : ℝ) - 1) / 2) *
      normSq (jj g) ^ (-((2 * (k : ℝ) - 1) / 2)) *
      Real.exp (-(2 * Real.pi * (a * g.det) / normSq (jj g))) := by
  rw [GlobalTheory.CompanionTheory.WmFE.real_whittaker_torus_mul k g a h, norm_mul, norm_mul, norm_exp_kernel, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg h.le _), norm_zpow]
  congr 2
  rw [normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_intCast]
  congr 1
  push_cast
  ring

lemma integrand_eq (k : ℕ) (σ : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hD : 0 < ε * g.det) (x : ℝ) (hx : 0 < x) :
    x⁻¹ * (‖Wm k (d2 (ε * x) * g)‖ * |ε * x| ^ (σ - 1 / 2)) =
      (|g.det| ^ ((2 * (k : ℝ) - 1) / 2) * normSq (jj g) ^ (-((2 * (k : ℝ) - 1) / 2))) *
      (x ^ ((k : ℝ) - 1 + σ - 1) *
        Real.exp (-(2 * Real.pi * |g.det| / normSq (jj g) * x))) := by
  have habs : |ε * x| = x := by
    rcases hε with rfl | rfl <;> simp [abs_of_pos hx]
  have hE : ε * g.det = |g.det| := by
    have h1 : |ε * g.det| = |g.det| := by
      rcases hε with rfl | rfl <;> simp
    rw [← h1, abs_of_pos hD]
  have ha : ε * x * g.det = x * |g.det| := by
    rw [← hE]
    ring
  have hpos : 0 < ε * x * g.det := by
    rw [ha]
    exact mul_pos hx (by rw [← hE]; exact hD)
  have hx1 : x ^ ((k : ℝ) - 1 + σ - 1) =
      x⁻¹ * (x ^ ((2 * (k : ℝ) - 1) / 2) * x ^ (σ - 1 / 2)) := by
    rw [← Real.rpow_add hx, ← Real.rpow_neg_one, ← Real.rpow_add hx]
    congr 1
    ring
  have harg : 2 * Real.pi * (x * |g.det|) / normSq (jj g) =
      2 * Real.pi * |g.det| / normSq (jj g) * x := by
    ring
  rw [norm_Wm k g _ hpos, ha, habs, Real.mul_rpow hx.le (abs_nonneg _), harg, hx1]
  ring



end GlobalTheory.CompanionTheory.AbsWm
end
end
