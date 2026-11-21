import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanTateIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealLocalFunctionalEquation

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
