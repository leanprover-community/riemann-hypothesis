module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StStokesOnChart
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffLimit
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOffDiscriminant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFibreNonempty
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalResidueLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocLocalize
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocResidue
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreNonempty
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalResidueLength
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersLocalIntegralClosureFinite
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelIrreducibleBasicOpenConnected

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem StokesOnChart.proof (hD : ComplexSets.DiscriminantCover.Statement) (hL : CutOffLimit.Statement) :
    StokesOnChart.Statement :=
  fun n d J A f g φ hJ hdim hAf hf hg hφ hc =>
    StokesOnVariety.chartInt_eq hD StokesOffDiscriminant.proof hL n d J A f g φ hJ hdim hAf hf hg hφ hc

end GroundTheory.Heights₂.Heights
end -- clump:auto
end -- clump:auto

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_FibreNonempty.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.FibreNonempty.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.FibreNonempty.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocalRing

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalResidueLength.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalResidueLength.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalResidueLength.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocResidue.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocLocalize.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.StokesOnChart : GroundTheory.Heights₂.Heights.StokesOnChart.Statement :=
  @GroundTheory.Heights₂.Heights.StokesOnChart.proof _root_.GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full GroundTheory.Heights₂.Heights.AutoClose.CutOffLimit
end -- clump:auto
end -- clump:auto
