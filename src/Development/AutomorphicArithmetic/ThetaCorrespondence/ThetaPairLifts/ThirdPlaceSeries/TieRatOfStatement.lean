import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalityOfTwistRowStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieRatOf

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tieRat_of_twAdm_and_at : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace → _root_.GlobalTheory.BigOn.Exp.CompatibilityRational := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.tieRat_of_alt
end
