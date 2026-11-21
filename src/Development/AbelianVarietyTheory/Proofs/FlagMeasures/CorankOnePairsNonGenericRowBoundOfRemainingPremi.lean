import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericCorankOnePairsBoundOfSplitFiniteRealRo
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowSplitFiniteArchimedeanPartsOfSteps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowLevelWithAnalyticFactsOfSteps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowAnalyticFactsOfFourSteps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyStepOfFourGlobalLeaves
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTupleNondegenerateGramStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalNongenericBoundRecordFamily

section
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

theorem GlobalTheory.rowNGP_of_leaves (hCB : StepChoiceConstantsC) (hPin : StepPinExists) (hForm : Formalism.L2.SG.NGVanish.FormNGC)
    (hThmB : StepThmBPinnedP) (hG5 : Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) (hW : Formalism.L2.SG.FamDefs.WeightsNG)
    (hG4 : Formalism.L2.SG.FamDefs.ProductStructureNonGeneric) (hEx : Formalism.L2.SG.FamDefs.ExistNG) : RowNGP := by
  obtain ⟨hS0, hNml, hPts, hN1, hX0⟩ := GlobalTheory.RowNGClosed.closedSteps
  have hFam : Formalism.L2.SG.NGLocModel.StepFamC := GlobalTheory.T.familyStep_of_four_globalLeaves hG5 hW hG4 hEx
  have hconds : ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39 := fun D =>
    ((GlobalTheory.local_nongeneric_bound_record_family 39 le_rfl).2.1 D).1
  have hLoc : StepLocGenPinnedC :=
    stepLocGenPinnedC_of_loc (Formalism.L2.SG.NGLocModel.stepLocPinnedC_of_fam hconds hFam)
  have hVan : StepVanishPinned :=
    stepVanishPinned_of_term (Formalism.L2.SG.NGVanish.stepTermVanish_of_form hForm)
  have hAna : StepAnalyticP := GlobalTheory.T.rowAnalyticFacts_of_four_steps hPin hVan hLoc hThmB
  have hMassData : StepAnalyticConstantsP := GlobalTheory.T.existsRowLevelWithAnalyticFacts_of_steps (tieOfCtx_of hX0) hCB hAna
  exact GlobalTheory.T.nonGenericCorankOnePairsBound_of_splitFiniteRealRow (GlobalTheory.T.rowSplitFiniteArchimedeanParts_of_steps hMassData sizes_of_hypotheses (stepClass_of_equiv hS0) hNml hPts
    (stepHeight_of_normOne hN1))
end

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.corankOnePairsNonGenericRowBound_of_remaining_premises : StepChoiceConstantsC → StepPinExists → Formalism.L2.SG.NGVanish.FormNGC → StepThmBPinnedP → Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric → Formalism.L2.SG.FamDefs.WeightsNG → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric → Formalism.L2.SG.FamDefs.ExistNG → RowNGP := by
  atlas_forward_decl GlobalTheory.rowNGP_of_leaves
