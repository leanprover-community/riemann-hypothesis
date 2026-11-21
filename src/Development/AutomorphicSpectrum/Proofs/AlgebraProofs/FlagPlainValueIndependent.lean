import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPlainValueIndep
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivSupportFibre

section
namespace GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue

open GroundTheory.Heights₂.Heights.NumbersDVR in

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagPlainValueIndependence.Statement :=
  FlagPlainValueIndependence.proof GlobalTheory.T.flag_independence FlagPairCharacterisation.proof VerticalDivisorSupportFibre.proof

end GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_plain_value_independent : GroundTheory.Heights₂.Heights.NumbersDVR.FlagPlainValueIndependence.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue.main
