import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHolds
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchIntDecompose
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBranchChartIntX
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.ParametrisationSheetsConnectedHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHoldsStatement
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBranchInt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamChartInt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartIntCountAdd
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamPieceInt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamCritNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamOffRegularZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularInjectivePieces
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamDensIntegrable
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolydiscLelongLimit

section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar

theorem branchIntDecompose : GroundTheory.Heights₂.Heights.BranchIntDecompose.Statement :=
  GroundTheory.Heights₂.Heights.BranchIntDecompose.proof GlobalTheory.T.branch_proper_at_point_holds
    (GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.proof
      (GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsContainOpen.proof
        GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsFinite.proof
        GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjHomInjective.proof
        GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsOpen.proof
        (GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsExists.proof
          GroundTheory.Heights₂.Heights.ComplexSets.LeadIdealDim.proof
          GroundTheory.Heights₂.Heights.ComplexSets.LinearFormCut.proof
          GroundTheory.Heights₂.Heights.ComplexSets.HomogDimZeroPow.proof))
      GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense.proof)
    GroundTheory.Heights₂.Heights.AutoClose.ChartIntSumOffHyperplane
    GroundTheory.Heights₂.Heights.Swarm.BranchChartInt.proof

end GlobalTheory.CompanionTheory.Ar
end

section
namespace GlobalTheory.CompanionTheory.Ar.SliceBranch

theorem paramChartInt : GroundTheory.Heights₂.Heights.ParamChartInt.Statement :=
  GroundTheory.Heights₂.Heights.ParamChartInt.proof
    (GroundTheory.Heights₂.Heights.ChartIntCountAdd.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact)
    GroundTheory.Heights₂.Heights.ParamPieceInt.proof GroundTheory.Heights₂.Heights.ParamCritNull.proof
    GroundTheory.Heights₂.Heights.ParamOffRegularZero.proof GroundTheory.Heights₂.Heights.RegularInjectivePieces.proof
    GroundTheory.Heights₂.Heights.ParamDensIntegrable.proof

theorem sliceBranchInt : GroundTheory.Heights₂.Heights.SliceBranchInt.Statement :=
  GroundTheory.Heights₂.Heights.SliceBranchInt.proof GlobalTheory.T.branch_proper_at_point_holds paramChartInt

end GlobalTheory.CompanionTheory.Ar.SliceBranch
end

section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Lelong

open GroundTheory.Heights₂.Heights

theorem lelongLimitAtBranches : LelongLimitAtBranches.Statement :=
  LelongLimitAtBranches.proof GlobalTheory.CompanionTheory.Ar.branchIntDecompose GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranchInt
    PolydiscLelongLimit.proof GlobalTheory.CompanionTheory.Ar.Branch.branchProperAtPoint

end GlobalTheory.CompanionTheory.Ar.Lelong
end
