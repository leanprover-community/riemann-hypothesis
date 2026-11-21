import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalExistenceStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CanExHolds

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigOn_canEx : _root_.GlobalTheory.BigOn.Exp.CanonicalExists := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.canEx_holds_alt
end
