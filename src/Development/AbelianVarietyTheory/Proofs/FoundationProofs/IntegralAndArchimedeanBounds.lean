import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassSumDenominatorBoundOfCmThetaHypotheses
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaJetClassSumArchimedeanBoundOfCmTheta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfiedStatement

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaJetClassSum_archimedeanBound_of_cmTheta : (∀ D, Inp D) → ArchSt := by
  first | exact @GlobalTheory.ArchTop.archSt_of_inp | exact GlobalTheory.ArchTop.archSt_of_inp | (intros; apply GlobalTheory.ArchTop.archSt_of_inp <;> assumption)
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem intSt_and_archSt : IntSt ∧ ArchSt :=
  ⟨GlobalTheory.T.classSumDenominatorBound_of_cmThetaHypotheses GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied, GlobalTheory.T.thetaJetClassSum_archimedeanBound_of_cmTheta GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied⟩

end GlobalTheory.NormSum
end
