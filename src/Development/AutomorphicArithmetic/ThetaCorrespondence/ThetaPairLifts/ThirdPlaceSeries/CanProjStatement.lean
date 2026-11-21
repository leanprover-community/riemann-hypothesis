import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalProjectionStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CanProj

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigOn_canProj : _root_.GlobalTheory.BigOn.Exp.CanonicalProjection₂ := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.canProj_alt
end
