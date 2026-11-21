import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAtFittedPointsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneMapOfRows

set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneMap_of_bundle_setAt_lin_inj_const_formula : _root_.GlobalTheory.BigTop.Fun.BundleCondition → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → GlobalTheory.RowClaim.LinK → GlobalTheory.RowClaim.InjK → GlobalTheory.RowClaim.ConstK → GlobalTheory.RowClaim.Formula2K → _root_.GlobalTheory.BigTop.Fun.LeafUniqueMap @GlobalTheory.BigTop.Fun.Comparison₂ := by
  atlas_forward_decl _root_.GlobalTheory.BigTop.Fun.oneMap_of_bundle_setAt_kernel_conditions
end
