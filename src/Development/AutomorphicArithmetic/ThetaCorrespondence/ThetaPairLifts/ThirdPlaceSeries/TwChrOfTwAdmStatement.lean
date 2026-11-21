import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistCharacterOfArtinStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwChrOfTwAdm

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_character_of_artin' : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter := by
  atlas_forward_decl _root_.GlobalTheory.TwistChr.twChr_of_twAdm_alt
end
