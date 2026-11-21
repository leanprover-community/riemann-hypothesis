import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CuspidalRangeOfReproUnipotent
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkbLeOneAddSq
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkpCoefCont

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma






def cu.Core (X : CData) : Prop :=
  cu.UnipFine X ∧ cu.HaarGrowth X ∧ cu.SizeStep X ∧ X.KernelDiag ∧ UnimodA X


def cu_StepsCore (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → cu.Core X


end Formalism.MainNotions.LeviCoordinates
