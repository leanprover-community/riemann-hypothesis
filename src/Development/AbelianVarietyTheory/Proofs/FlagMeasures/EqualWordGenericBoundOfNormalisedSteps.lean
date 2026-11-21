import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfCutBoundPositive
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericHeightBoundOfLocalEstimates
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticGenericBoundOfChoiceStepPositive
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticConstantGenericBoundOfNormalisedSteps

section
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

theorem rowMainEqP_of_pinned (hCh : PN.NGChain) (hC : StepClassG) (hN : StepNormalsG) (hP : StepPointsG)
    (hO : StepNormOneG) (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hV : StepTermVanishG)
    (hL : StepLocGenPinnedG) (hT : StepThmBGP) : GlobalTheory.SnPos.RowMainEqP :=
  GlobalTheory.T.equalWordGenericBound_of_cutBound_positive hCh Formalism.L2.SG.Pf.MainEqCut.meanAmplitudeGeneric_holds
    (GlobalTheory.T.generic_height_bound_of_local_estimates Formalism.L2.SG.NGCut.sizes_of_hypotheses hC hN hP (stepHeightG_of_normOne hO)
      (GlobalTheory.T.analyticGenericBound_of_choiceStep_positive hTi hB (GlobalTheory.T.analyticConstantGenericBound_of_normalisedSteps hE hV hL hT)))

example : PN.NGChain → StepClassG → StepNormalsG → StepPointsG → StepNormOneG → TieOfCtx → StepChoiceConstantsC →
    StepPinExists → StepTermVanishG → StepLocGenPinnedG → StepThmBGP → GlobalTheory.SnPos.RowMainEqP :=
  rowMainEqP_of_pinned

end GlobalTheory.SnPos
end

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equalWordGenericBound_of_normalisedSteps : PN.NGChain → StepClassG → StepNormalsG → StepPointsG → StepNormOneG → TieOfCtx → StepChoiceConstantsC → StepPinExists → StepTermVanishG → StepLocGenPinnedG → StepThmBGP → GlobalTheory.SnPos.RowMainEqP := by
  atlas_forward_decl GlobalTheory.SnPos.rowMainEqP_of_pinned
