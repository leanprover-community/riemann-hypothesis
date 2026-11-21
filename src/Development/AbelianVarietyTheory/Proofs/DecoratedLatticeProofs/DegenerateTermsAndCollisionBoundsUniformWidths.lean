import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DiscreteSeriesDegreeBound
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FinrankLeRankOnAdd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.AutomorphicFormsFiniteUnitaryIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNml
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataChoiceLeaves
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowAmplitudeBoundsUniformSingletonWidth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTermLoopOfStandingHypotheses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsPosTypeP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallOnUnivUnconditional
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InputsOfSubsetWidths
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollSOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankTwoCountBoundsOfRowCountBoundsUniform
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CntOnSingleton
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VanishingGramBoundUniformWindowAndParams
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VanishingGramBoundWindowOfTermPairTypeBound

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem degenerate_and_collisions_uncond : (∀ c : ℝ, On {c} VanishingGramTermsBound) ∧ ∀ c : ℝ, On {c} CollS := by
  have hSM : Formalism.HermitianLatticesTheory.SiegelMassRatio := GlobalTheory.Mass.siegelMassRatio_holds
  have hS : ∀ c : ℝ, SmallOn {c} := fun c =>
    (inputs_of_subset_widths {c} Set.univ (Set.subset_univ _)).2.1 smallOn_univ_unconditional
  have hP : GlobalTheory.TypeAsm.TypeP := GlobalTheory.rowsPos_typeP
  refine ⟨vanishingGramBound_uniformWindow_and_weightData.1 (vanishingGramBoundWindow_of_termPairTypeBound hP), fun c => ?_⟩
  exact collS_on hSM {c} (GlobalTheory.T.rowAmplitudeBoundsUniform_singleton_width c) (corankTwoCountBounds_of_rowCountBoundsUniform {c} (cntOn_singleton hSM c)) (hS c)
    (tieOn_singleton_uncond c)

end GlobalTheory.Core.Deg
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerateTerms_and_collisionBounds_uniform_widths : (∀ c : ℝ, On {c} VanishingGramTermsBound) ∧ ∀ c : ℝ, On {c} CollS := by
  atlas_forward_decl GlobalTheory.Core.Deg.degenerate_and_collisions_uncond
