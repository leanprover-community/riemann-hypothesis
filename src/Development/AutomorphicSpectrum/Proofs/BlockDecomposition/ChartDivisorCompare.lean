import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.UniformIntegrabilityProportionalityHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.TargetsProjFullRankMeetsRegular
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorCompare
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartIntegralPoints
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegreChartIntegralHolds

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segre_chart_integral_holds : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral | exact GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral | (intros; apply GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral <;> assumption)
end

section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar

theorem chartDivisorCompare : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.proof GlobalTheory.T.segre_chart_integral_holds
    GroundTheory.Heights₂.Heights.Targets.SegreChartIntegralPoints.proof
    GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorComponents
    GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorLength

end GlobalTheory.CompanionTheory.Ar
end
