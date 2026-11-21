import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFourth
import BuildAid.ForwardExisting

section
namespace GlobalTheory.CompanionTheory.Ggeo

theorem blockProjection_genericPoints_good : GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.Statement :=
  GlobalTheory.CompanionTheory.Ar.PB.BaseCount.generic_points_good_for_intersection

end GlobalTheory.CompanionTheory.Ggeo
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_good_statement : GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ggeo.blockProjection_genericPoints_good
