import Mathlib
import GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation
set_option maxSynthPendingDepth 1

open NumberField InfinitePlace NumberField.Units Complex Topology Filter Set
open scoped Real

namespace GroundTheory.Global

noncomputable section

theorem Gammaℂ_residue_zero : Tendsto (fun s ↦ s * Gammaℂ s) (𝓝[≠] 0) (𝓝 2) := by
  have h' : Tendsto (fun s : ℂ ↦ 2 * (2 * (π : ℂ)) ^ (-s)) (𝓝[≠] 0) (𝓝 2) := by
    rw [(by simp : 𝓝 (2 : ℂ) = 𝓝 (2 * (2 * (π : ℂ)) ^ (-(0 : ℂ))))]
    refine Tendsto.mono_left (ContinuousAt.tendsto ?_) nhdsWithin_le_nhds
    exact continuousAt_const.mul ((continuousAt_const_cpow
      (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))).comp (by fun_prop))
  have h := h'.mul tendsto_self_mul_Gamma_nhds_zero
  rw [mul_one] at h
  refine h.congr fun z ↦ ?_
  rw [Gammaℂ]
  ring

variable (K : Type*) [Field K] [NumberField K]





end

end GroundTheory.Global
