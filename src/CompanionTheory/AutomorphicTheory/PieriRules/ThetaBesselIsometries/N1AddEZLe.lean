module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.N1AddEZLe
public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ImportsBisTer
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorWeightedBesselGapStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ExistsRegularRepBesselBigCellVectorEqBesselImpor
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingUniformConstantStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselNormSqEqBigCellNormSqAltImports
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.NumericalFamilyShapeGaps
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepExteriorPowerStandardRep
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FixesWedgeAndForm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermCmpWedgeEqDet

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SuppliedPieri

theorem n1_add_eZ_le {n : ℕ} (ν : Fin n → ℤ) (I : Finset (Fin n)) : n1 (ν + eZ I) ≤ n1 ν + I.card :=
  _root_.GlobalTheory.SuppliedPieri.n1_add_eZ_le ν I

theorem JF_zero {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (g : B.Mat k r) :
    B.JF D 0 g = 0 :=
  _root_.GlobalTheory.SuppliedPieri.JF_zero D g

end GlobalTheory.SuppliedPieri
