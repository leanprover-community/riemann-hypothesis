import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelRootIndep
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelValueIndependent

section
namespace GlobalTheory.CompanionTheory.Ar.RootIndep

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelRootIndependence.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelRootIndependence.proof GlobalTheory.T.flag_model_value_independent

end GlobalTheory.CompanionTheory.Ar.RootIndep
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_root_independent : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelRootIndependence.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.RootIndep.main
