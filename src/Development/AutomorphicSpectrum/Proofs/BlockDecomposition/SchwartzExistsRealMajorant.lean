import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNormTheta2TailLeOfLeOne
import BuildAid.ForwardExisting

section
open scoped SchwartzMap

namespace GlobalTheory.CompanionTheory.SchwartzMaj

theorem exists_nonneg_schwartz_majorant (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : SchwartzMap E ℂ) :
    ∃ F : SchwartzMap E ℂ, ∀ x, (F x).im = 0 ∧ ‖f x‖ ≤ (F x).re := by
  obtain ⟨Φ, r, hΦ, hr⟩ := GlobalTheory.CompanionTheory.EisRk1.exists_schwartz_majorant f
  refine ⟨Φ, fun x => ?_⟩
  rw [hΦ x]
  exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact hr x⟩

end GlobalTheory.CompanionTheory.SchwartzMaj
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_exists_real_majorant : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : SchwartzMap E ℂ), ∃ F : SchwartzMap E ℂ, ∀ x, (F x).im = 0 ∧ ‖f x‖ ≤ (F x).re := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SchwartzMaj.exists_nonneg_schwartz_majorant
