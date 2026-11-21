import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter
import BuildAid.ForwardExisting

section
open MeasureTheory

namespace GlobalTheory

theorem contDiff_toCLM_of_continuous_oneParameter {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (A : ℝ → W →ₗ[ℝ] W)
    (hc : ∀ w, Continuous fun t => A t w) (hadd : ∀ s t, A (s + t) = (A s).comp (A t)) (h0 : A 0 = LinearMap.id) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => LinearMap.toContinuousLinearMap (A t)) := by
  have hT : Continuous fun t => LinearMap.toContinuousLinearMap (A t) :=
    continuous_clm_apply.2 fun w => by simpa using hc w
  refine contDiff_of_continuous_oneParameter (W →L[ℝ] W) _ hT ?_ ?_
  · ext w; simp [h0]
  · intro s t; ext w; simp [hadd]

end GlobalTheory
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_continuous_oneParameter_finiteDimensional_linear : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (A : ℝ → W →ₗ[ℝ] W),
    (∀ w, Continuous fun t => A t w) → (∀ s t, A (s + t) = (A s).comp (A t)) → A 0 = LinearMap.id →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => LinearMap.toContinuousLinearMap (A t)) := by
  atlas_forward_decl GlobalTheory.contDiff_toCLM_of_continuous_oneParameter
