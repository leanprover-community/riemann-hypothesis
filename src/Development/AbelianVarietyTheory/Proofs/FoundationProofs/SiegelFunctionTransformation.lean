import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitModularSSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitModularGroupTSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleOfSl2ActionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularLawOfSAndT

section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem sg_smul (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) (τ : ℍ) (hx : admitted c x) :
    sg c x (γ • τ) = sg c (act x γ) τ :=
  GlobalTheory.T.modular_law_of_s_and_t (admitted c) (sg c) (fun x γ h => GlobalTheory.T.admissible_of_sl2_action c x γ h)
    (fun x τ h => GlobalTheory.T.smoothedSiegelUnit_modularS_smul c x τ h) (fun x τ _ => GlobalTheory.T.smoothedSiegelUnit_modularGroupT_smul c x τ) γ x τ hx

end GlobalTheory.Sieg
end

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_function_transformation : ∀ (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) (τ : ℍ), admitted c x → sg c x (γ • τ) = sg c (act x γ) τ := by
  atlas_forward_decl GlobalTheory.Sieg.sg_smul
