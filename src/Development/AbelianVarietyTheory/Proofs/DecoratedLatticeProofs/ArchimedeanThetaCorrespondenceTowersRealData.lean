import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesHarishChandraModuleAdmissible

section
open Formalism.BasicNotions

namespace GlobalTheory.TwArch

theorem archOnRecord_closed : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
    ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D :=
  fun hDS hHC D => GlobalTheory.ArchRec.archOnRecord hDS hHC D

end GlobalTheory.TwArch
end

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanThetaCorrespondence_towers_real_data : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D := by
  atlas_forward_decl GlobalTheory.TwArch.archOnRecord_closed
