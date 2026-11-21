import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchorBoundStatementStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AnchorHolds

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anchor_bound : _root_.GlobalTheory.CovTop.AnchorCondition := by
  atlas_forward_decl _root_.GlobalTheory.CovTop.anchor_holds_alt
end
