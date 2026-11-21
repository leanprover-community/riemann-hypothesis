import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedExistenceStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdaptEx

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptEx' : _root_.GlobalTheory.BigOn.Exp.AdaptedExistence₂ := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.adaptEx_alt
end
