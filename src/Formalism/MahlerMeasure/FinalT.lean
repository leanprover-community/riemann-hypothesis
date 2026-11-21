import Formalism.MahlerMeasure.MahlerMeasureProofs.BadCrit
import Formalism.MahlerMeasure.MahlerMeasureProofs.MeanGam
import Formalism.MahlerMeasure.FinalM
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamDeg
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamLead
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamInt
import Formalism.MahlerMeasure.CoarseLevelSlackInequalities

section
namespace Formalism.GM.Top
open Formalism.GM
theorem gamDeg : M.GamDeg := gamma_degree_bound
theorem gamLead : M.GamLead := gamma_leading_term
end Formalism.GM.Top
end

section
namespace Formalism.GM.Top
open Formalism.GM
theorem badCrit : M.BadCrit := bad_criterion_holds
end Formalism.GM.Top
end
