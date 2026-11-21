import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersLocalIntegralClosureFinite
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegreeRatio
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitFiniteSum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeLocalFlat
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.PClopenPieceSheetCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.PUnbranchedPartConnected
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadIsoLoc
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsFurther
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsRest
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleHomLoc
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionForms
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDivVertical
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeLocalLength
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.PIrreducibleBasicOpenConnected
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadStep
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ZeroLeDivCycle

section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFinite.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFinite.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFinite.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalIntegral GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_LocalIntegralClosureFinite GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocNoetherian

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalFlat.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalFlat.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalFlat.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConePolyLocalization

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_DivCycleHomLoc.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingLocal

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualCompare.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.ResidualComparison.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.ResidualComparison.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces GroundTheory.Heights₂.Heights.NumbersDVR.ResidualDisjoint.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualContraction


theorem GroundTheory.Heights₂.Heights.AutoClose.TubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement :=
  @GroundTheory.Heights₂.Heights.TubeEuclMass.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.TubeCollarMass GroundTheory.Heights₂.Heights.AutoClose.TubeDeepMass
end

section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalLength.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalLength.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalLength.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.LocalizedQuotientLength.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalFlat

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFiniteRank.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFiniteRank.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.FibreFinite.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFinite GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocFrac.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpExcessDrop.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpExcessDecreases.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpExcessDecreases.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.ExcessPositive.full GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualCompare GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ExceptionalCompare


theorem GroundTheory.Heights₂.Heights.AutoClose.CutOffLimit : GroundTheory.Heights₂.Heights.CutOffLimit.Statement :=
  @GroundTheory.Heights₂.Heights.CutOffLimit.of_open GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SheetImageAreaSet GroundTheory.Heights₂.Heights.AutoClose.TubeEuclMass

theorem GroundTheory.Heights₂.Heights.AutoClose.StokesOnVariety : GroundTheory.Heights₂.Heights.StokesOnVariety.Statement :=
  @GroundTheory.Heights₂.Heights.StokesOnVariety.of_open GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SheetImageAreaSet GroundTheory.Heights₂.Heights.AutoClose.TubeEuclMass
end
