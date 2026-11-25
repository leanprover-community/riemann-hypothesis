module

import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NuQPinExistsHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqFam
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalNongenericBoundRecordFamily
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormChainLemmas
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClassHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNormOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqPoints
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormGramAtOrigin
public import Formalism.PeriodIntegrals.NormGramAtOrigin

@[expose] public section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna

namespace GlobalTheory

theorem closed_steps_gram_vectors : NondegenerateGramTuple := by
  first | exact _root_.Formalism.L2.SG.NGLeaves.nondegenerate_gram_tuple | exact @_root_.Formalism.L2.SG.NGLeaves.nondegenerate_gram_tuple | apply _root_.Formalism.L2.SG.NGLeaves.nondegenerate_gram_tuple <;> assumption

theorem closed_steps_equal_words :
    PN.NGChain ∧ StepClassG ∧ StepPointsG ∧ StepNormOneG ∧ TieOfCtx ∧ StepPinExists ∧
      StepTermVanishG ∧ Formalism.L2.SG.NGVanish.FormNGC ∧
      (Formalism.L2.SG.Pf.MainEqFam.StepFamG → StepLocGenPinnedG) := by
  have hPts : StepPointsG :=
    Formalism.L2.SG.Pf.MainEqPoints.stepPointsG_of_leaves _root_.Formalism.L2.SG.TermOp.Vanish.avgCore
      Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds _root_.Formalism.L2.SG.Pf.chiTrivialC_outright
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds
      (fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')
  have hNorm : StepNormOneG :=
    Formalism.L2.SG.NGCut.LeadingMinorIntegrality.Gen.stepNormOneG_of_leaves _root_.Formalism.L2.SG.TermOp.Vanish.avgCore
      Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds _root_.Formalism.L2.SG.Pf.chiTrivialC_outright
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds
      (fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')
  have hLoc : ∀ D, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39 := fun D =>
    ((GlobalTheory.local_nongeneric_bound_record_family 39 le_rfl).2.1 D).1
  exact ⟨_root_.Formalism.FourierDecayAlt.P.NormChainLemmas.nGChain, Formalism.L2.SG.Pf.stepClassG_holds, hPts, hNorm,
    tieOfCtx_of closed_steps_gram_vectors, Formalism.L2.SG.NGPin.stepPinExists,
    Formalism.L2.SG.Pf.MainEqVanish.stepTermVanishG_of_form Formalism.L2.SG.Pf.formGC_holds,
    Formalism.L2.SG.Pf.formNGC_holds,
    fun hFam => Formalism.L2.SG.Pf.stepLocGenPinnedG_of_loc (Formalism.L2.SG.Pf.stepLocPinnedG_of_fam hLoc hFam)⟩

end GlobalTheory
