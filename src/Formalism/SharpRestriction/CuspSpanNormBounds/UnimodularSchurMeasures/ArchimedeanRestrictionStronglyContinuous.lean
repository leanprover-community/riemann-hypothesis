import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CovolumeIndependentOfFundamentalDomain
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrcTendstoVec

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def RepInf (X : CData) : Prop := ∀ F : X.L2, Continuous fun g : X.I.Ginf => X.R (g, 1) F


end Formalism.MainNotions.LeviCoordinates

end
