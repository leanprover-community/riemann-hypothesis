import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSubQuotient
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependence

section
namespace GlobalTheory.CompanionTheory.Ar.Num.SubQuotFlags

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.SubQuotient.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.SubQuotient.proof GlobalTheory.T.flag_independence

end GlobalTheory.CompanionTheory.Ar.Num.SubQuotFlags
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_quotient_statement : GroundTheory.Heights₂.Heights.NumbersDVR.SubQuotient.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.SubQuotFlags.main
