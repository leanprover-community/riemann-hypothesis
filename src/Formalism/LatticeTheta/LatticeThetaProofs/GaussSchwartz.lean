import Formalism.LatticeTheta.LatticeSummableDecay

open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

namespace Formalism.H

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

lemma gauss_fun_eq (t : ℝ) :
    (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) =
      fun v : V => cexp (-((Real.pi * t : ℝ) : ℂ) * (‖v‖ : ℂ) ^ 2) := by
  funext v
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring



lemma gauss_fourier (t : ℝ) (ht : 0 < t) (w : V) :
    (𝓕 (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) : V → ℂ) w =
      ((t ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) * (Real.exp (-Real.pi * ‖w‖ ^ 2 / t) : ℂ) := by
  have hb : 0 < (((Real.pi * t : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]; exact mul_pos Real.pi_pos ht
  rw [gauss_fun_eq, fourier_gaussian_innerProductSpace hb w]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have e1 : (Real.pi : ℂ) / ((Real.pi * t : ℝ) : ℂ) = ((t⁻¹ : ℝ) : ℂ) := by
    push_cast
    field_simp
  have e2 : ((t⁻¹ : ℝ) : ℂ) ^ ((Module.finrank ℝ V : ℂ) / 2) =
      ((t ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show ((Module.finrank ℝ V : ℂ) / 2) = (((Module.finrank ℝ V : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (inv_nonneg.mpr ht.le), Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_div]
  rw [e1, e2, Complex.ofReal_exp]
  congr 2
  push_cast
  field_simp


theorem schwartz_decay_gaussian : SchwartzDecay V := by
  intro f b
  refine ⟨f.isBigO_cocompact_rpow (-b), ?_⟩
  have h := (FourierTransform.fourier f : 𝓢(V, ℂ)).isBigO_cocompact_rpow (-b)
  rwa [SchwartzMap.fourier_coe] at h


end Formalism.H
