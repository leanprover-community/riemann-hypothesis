import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ProjectionStatementOfFinal
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OperatorExistsOfUnitaryContinuous
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.UnitaryRepUnimodularOfFiniteVolume
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelDiagonalOfAbsoluteConvergence

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def cu.End (X : CData) : Prop :=
  cu.UnipFine X ∧ cu.LocGrowth X ∧ (∃ S : CSize X, S.Strata ∧ S.PackCount ∧ S.Inv ∧ S.Lip ∧ S.LowN) ∧ AbsKernelSquareIntegrable X ∧
    UnimodA X

def cu_StepsEnd (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → cu.End X


end Formalism.MainNotions.LeviCoordinates
