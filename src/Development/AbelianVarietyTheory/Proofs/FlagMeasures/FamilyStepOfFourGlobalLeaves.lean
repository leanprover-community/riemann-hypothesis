import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalMassLeGenericMassConstNineStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentLocalIdentityFamiliesLemmaHStatement

section
namespace GlobalTheory

theorem stepFamC_of_globalLeaves :
    Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric → Formalism.L2.SG.FamDefs.WeightsNG → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric →
      Formalism.L2.SG.FamDefs.ExistNG → Formalism.L2.SG.NGLocModel.StepFamC :=
  fun hG5 hW hG4 hE =>
    Formalism.L2.SG.FamDefs.stepFamC_of (fun D h => GlobalTheory.T.localMass_le_genericMass_const_nine _ _ h) GlobalTheory.T.differentLocalIdentity_familiesLemmaH hG5 hW hG4 hE

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyStep_of_four_globalLeaves : Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric → Formalism.L2.SG.FamDefs.WeightsNG → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric → Formalism.L2.SG.FamDefs.ExistNG → Formalism.L2.SG.NGLocModel.StepFamC := by
  atlas_forward_decl GlobalTheory.stepFamC_of_globalLeaves
