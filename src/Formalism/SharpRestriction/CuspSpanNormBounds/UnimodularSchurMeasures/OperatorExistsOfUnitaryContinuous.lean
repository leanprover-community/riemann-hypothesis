import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.LeftTranslateSet
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.PjTrInnerPure
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SchurRelationAddSecond
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.PjDensUpper

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma



def StepsB' (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → RepA X ∧ UnimodF X ∧ X.CuspStep


end Formalism.MainNotions.LeviCoordinates

end
