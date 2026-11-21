import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelIrreducibleBasicOpenConnected
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersSemilocalMaxIdeals
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLengthSum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleMinimal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLength
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForwardLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineDegree
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineSection
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHsymmShift

section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLengthSum.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLengthSum.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLengthSum.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.FibreFinite.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocalRing GroundTheory.Heights₂.Heights.FieldNumbers.FiniteAlgebraLengthSum.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalMaxIdeals
end

section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLength.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLength.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLength.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLengthSum GroundTheory.Heights₂.Heights.FieldNumbers.FibreRelDim.proof GroundTheory.Heights₂.Heights.FieldNumbers.DivCycleMinimal.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalLength
end

section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForwardLocal.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForwardLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForwardLocal.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DivCycleMinimal.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalLength GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocalRing GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLength
end

section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForward.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForward.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForward.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForwardLocal
end

section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ProjectionFormulaDegree.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.CutRational.full GroundTheory.Heights₂.Heights.FieldNumbers.IntNumBase.full GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaContracted.full GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForward
end
