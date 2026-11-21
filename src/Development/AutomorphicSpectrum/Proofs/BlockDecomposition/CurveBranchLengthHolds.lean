import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveBranchLength
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.BranchInverseOffHypersurfaceHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchNormalisationHolds

section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Heights.CurveBranch

theorem curveBranchLength_of_branchNormalisation
    (hB : GroundTheory.Heights₂.Heights.BranchNormalisation.Statement) :
    GroundTheory.Heights₂.Heights.CurveBranchLength.Statement :=
  GroundTheory.Heights₂.Heights.CurveBranchLength.proof GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationLength hB

theorem curveBranchLength : GroundTheory.Heights₂.Heights.CurveBranchLength.Statement :=
  curveBranchLength_of_branchNormalisation GlobalTheory.T.branch_normalisation_holds

end GlobalTheory.CompanionTheory.Heights.CurveBranch
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_branch_length_holds : GroundTheory.Heights₂.Heights.CurveBranchLength.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength
