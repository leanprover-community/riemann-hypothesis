module

public import Development.WeilBound.CoreStatements.ThetaDilations.IsOpenCoset
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScalingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureLinearChangeStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilRepresentationQuadraticDatumStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MobiusActionUpperHalfPlaneStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SL2BruhatDecompositionIdentitiesStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanGaussianFourierStatement

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

variable {F : Type} [Field F] [NumberField F]

def uA (a : Fˣ) : (A F)ˣ := Units.map (algebraMap F (A F) : F →* A F) a

end PositivityTheory.PlacePermOperatorBicommutantSpan
