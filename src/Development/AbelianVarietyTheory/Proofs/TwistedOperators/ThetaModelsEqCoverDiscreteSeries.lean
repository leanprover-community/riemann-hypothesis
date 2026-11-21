import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BarMatrix
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandraStatement

section
open Formalism.BasicNotions

namespace GlobalTheory

theorem modelsAreCoverSeries_of_hypotheses :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
      ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D :=
  GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra

end GlobalTheory
end

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaModels_eq_coverDiscreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D := by
  atlas_forward_decl GlobalTheory.modelsAreCoverSeries_of_hypotheses
