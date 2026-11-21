import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
import BuildAid.ForwardExisting

section
open MeasureTheory

namespace GlobalTheory.FockFamily

theorem contDiff_blockB_blockD {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)) (hJ : ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) := by
  constructor
  · rw [contDiff_clm_apply_iff]
    intro q
    simpa only [blockB_apply] using (hJ (0, q)).fst
  · rw [contDiff_clm_apply_iff]
    intro q
    simpa only [blockD_apply] using (hJ (0, q)).snd

end GlobalTheory.FockFamily
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_prodLinearMap_upperRight_lowerRight_blocks : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)), (∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) := by
  atlas_forward_decl GlobalTheory.FockFamily.contDiff_blockB_blockD
