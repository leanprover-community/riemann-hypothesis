import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcCoords
import BuildAid.ForwardExisting

section
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem dualStackedExcCoords : GroundTheory.Heights₂.Heights.DualStackedExcCoords.Statement :=
  GroundTheory.Heights₂.Heights.DualStackedExcCoords.proof

end GlobalTheory.CompanionTheory.Ar.Giv
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_stacked_exceptional_coords : GroundTheory.Heights₂.Heights.DualStackedExcCoords.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords
