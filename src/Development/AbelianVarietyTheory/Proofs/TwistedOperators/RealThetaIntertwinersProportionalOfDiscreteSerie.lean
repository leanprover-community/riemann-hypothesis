import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocLineOfMatches
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandraStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPlaceThetaObjectsTheoremARPartsStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealLine

theorem itLine_of_discreteSeries :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItLine D := by
  intro hCover hModules D

  rcases GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis hCover hModules with ⟨X, hParam, -, -, -, -, hAR3, -⟩

  have hBridge : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D := GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hCover hModules D
  have hVac : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := GlobalTheory.T.thetaVacuumCharacters_realPlaces D
  exact itLine D X hParam hAR3 hVac hBridge hModules

end GlobalTheory.Chain.RealLine
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realThetaIntertwiners_proportional_of_discreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItLine D := by
  atlas_forward_decl GlobalTheory.Chain.RealLine.itLine_of_discreteSeries
