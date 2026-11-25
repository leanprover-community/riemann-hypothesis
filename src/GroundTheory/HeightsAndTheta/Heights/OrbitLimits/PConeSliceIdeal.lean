module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StConeSliceIdeal
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartHomogenise
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartZeroSet

@[expose] public section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights
open MvPolynomial _root_.UpperTheory.Reformulated.B.Ydc1

theorem ConeSliceIdeal.proof : ConeSliceIdeal.Statement := by
  intro n C t V hC hV f hf
  have hℓ : (linForm t).IsHomogeneous 1 := IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _
  obtain ⟨G, D, hG, hGf⟩ := ChartHomogenise.exists_homogeneous_sub_mem_span (linForm t) f hℓ
  rw [show f = linForm t * G - (linForm t - 1) * G - (G - f) by ring]
  refine Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mem_sup_left (hV ?_))
    (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))) (Ideal.mem_sup_right hGf)
  refine mem_vanishingIdeal_iff.mpr fun c hc => ?_
  change eval c (linForm t * G) = 0
  rw [map_mul]
  set l := eval c (linForm t)
  by_cases hl : l = 0 <;> simp [mul_eq_zero, hl]
  have hs : eval (l⁻¹ • c) (linForm t) = 1 := by
    rw [eval_smul_of_isHomogeneous hℓ, pow_one, inv_mul_cancel₀ hl]
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hGf
  simpa [map_sub, map_mul, hs, show eval (l⁻¹ • c) f = 0 from
    (mem_vanishingIdeal_iff.mp hf) _ ⟨hC c hc _ (inv_ne_zero hl), hs⟩,
    eval_smul_of_isHomogeneous hG, mul_eq_zero, pow_ne_zero D (inv_ne_zero hl), hl] using congrArg (eval (l⁻¹ • c)) hq

end GroundTheory.Heights₂.Heights
