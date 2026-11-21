import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineEqDeRhamOfSmoothLiftComparison

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_eq_deRham_of_smoothLift_comparison : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.CrystallineDeRham := by
  first | exact @GlobalTheory.CrysLift.crystallineDeRham_of_smoothLift | exact GlobalTheory.CrysLift.crystallineDeRham_of_smoothLift | (intros; apply GlobalTheory.CrysLift.crystallineDeRham_of_smoothLift <;> assumption)
end

section
namespace GlobalTheory

theorem abelianDualCrystal_of_dual_of_smoothLift :
    GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianDualCrystal :=
  fun h₁ h₂ => ⟨h₁, GlobalTheory.T.crystalline_eq_deRham_of_smoothLift_comparison h₂⟩

end GlobalTheory
end
