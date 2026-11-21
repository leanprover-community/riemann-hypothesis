import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantSmoothProjFanNoSelfIntersections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationFanLogKodairaSpencerIso

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidalCompactificationFan_logKodairaSpencer_iso : GlobalTheory.Published.ToroidalForFanKS := by
  first | exact @GlobalTheory.TorKSField.toroidalForFanKS | exact GlobalTheory.TorKSField.toroidalForFanKS | (intros; apply GlobalTheory.TorKSField.toroidalForFanKS <;> assumption)
end

section
namespace GlobalTheory

open NumberField

theorem toroidalCompactification_holds : GlobalTheory.Published.ToroidalCompactification := by
  intro E _ _ _ H Dw hr l Xo c
  obtain ⟨φs, hs, -⟩ := GlobalTheory.T.exists_invariant_smoothProjFan_noSelfIntersections (max 1 (Module.finrank ℚ E * min Dw.p Dw.q))
  obtain ⟨φ, h₁, h₂, -⟩ := GlobalTheory.PolFan.exists_fine_invariant_fan H hs (le_max_right _ _) ∅ (by simp)
  obtain ⟨Y, -, -, -, -, -, a₁, a₂, a₃, -⟩ := GlobalTheory.Published.ToroidalForFanKS.exists_model_of_fan GlobalTheory.T.toroidalCompactificationFan_logKodairaSpencer_iso hr h₁ h₂ Xo c
  exact ⟨Y, a₁, a₂, a₃⟩

end GlobalTheory
end
