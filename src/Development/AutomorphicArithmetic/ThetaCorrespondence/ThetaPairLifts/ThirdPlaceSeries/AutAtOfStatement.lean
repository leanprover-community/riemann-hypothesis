import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphyFromSmallExponentStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutAtOf

set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aut_statement_of_small_exponent_statement : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.FrameAut.AutStAlt := by
  atlas_forward_decl _root_.GlobalTheory.FrameAut.autSt_of_smallSt'
end
