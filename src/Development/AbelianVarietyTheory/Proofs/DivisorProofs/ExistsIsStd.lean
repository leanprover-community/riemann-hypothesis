import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersDividedPowerPolyAlgebraAugIde
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersSplitAugmentationExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAndAugmentationMapStatement

section
set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem PDPoly.exists_isStd : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B),
    ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  intro B _ J δ Q
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_dividedPowers_dividedPowerPolyAlgebra_augIdeal B Q
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.exists_lift_and_augmentation_map B Q).2
  obtain ⟨θ, hθ, hθη⟩ := GlobalTheory.T.exists_dividedPowers_split_augmentation_extension B J δ Q.P ε Q.aug η hε
  refine ⟨θ, ⟨hθ, fun n ↦ ?_⟩⟩
  rw [hθη n _ (Q.e_succ_mem_aug 0), hη]

end GlobalTheory.PDA
end

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dividedPowers_ext_isStd : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B), ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  atlas_forward_decl GlobalTheory.PDA.PDPoly.exists_isStd
