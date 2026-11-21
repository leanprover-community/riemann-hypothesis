import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjFixAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FixAtHolds

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_conj_fix_at' : GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwConj.FixedPointCondition := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.TwConj.fixAt_holds_alt
end
