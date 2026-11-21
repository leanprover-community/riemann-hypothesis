import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependence

section
namespace GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient.proof GlobalTheory.T.flag_independence

end GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_quotient_statement : GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags.main
