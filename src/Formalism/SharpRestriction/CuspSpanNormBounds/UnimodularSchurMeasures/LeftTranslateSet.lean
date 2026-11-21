import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.PjFdegAllPos

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory TopologicalSpace
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

section General

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

def leftTranslateSet (W : Set G) (x : G) : Set G := (fun z => x⁻¹ * z) ⁻¹' W





end General


end Formalism.MainNotions.LeviCoordinates

end
