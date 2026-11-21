import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPTypicalTangent
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TypicalCurvesOfTypeOfTypicalTangents
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TypicalBasisCoordinates

section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.TypicalCurveBases

theorem typical_curves_tangent_and_bases : TypicalCurveEigenspace ∧ TypicalCurveBasisExists :=
  have h2 : TypicalCurveEigenspace :=
    GlobalTheory.TypicalCurve.typicalCurves_of_type_of_typical_tangents GlobalTheory.PTypicalTangent.exists_pTypical_tangent
  ⟨h2, GlobalTheory.typicalBasis_coordinates h2⟩

end GlobalTheory.TypicalCurveBases
end

section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typicalCurveEigenspace_and_basisExists : TypicalCurveEigenspace ∧ TypicalCurveBasisExists := by
  first | exact @GlobalTheory.TypicalCurveBases.typical_curves_tangent_and_bases | exact GlobalTheory.TypicalCurveBases.typical_curves_tangent_and_bases | (intros; apply GlobalTheory.TypicalCurveBases.typical_curves_tangent_and_bases <;> assumption)
end
