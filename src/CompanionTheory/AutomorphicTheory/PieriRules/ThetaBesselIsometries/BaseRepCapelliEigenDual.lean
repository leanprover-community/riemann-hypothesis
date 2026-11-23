module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BaseRepCapelliEigenDual
public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ImportsBisTer
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapDecayStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingUniformConstantStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CapelliKFiniteCoefficient
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselPeriodAdjointPairStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ExistsRegularRepBesselBigCellVectorEqBesselImpor
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselNormSqEqBigCellNormSqAltImports
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.AemeasurableBesselNormIntegrandBigCellImports
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsFamilyFunctionalsStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGapsStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.NumericalFamilyShapeGaps
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CoefZero

theorem continuousOn_of_ckOn {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞}
    {f : B.Mat k r → E} (h : B.CkOn m (B.GV k r) f) : ContinuousOn f (B.GV k r) :=
  _root_.GlobalTheory.CoefZero.continuousOn_of_ckOn h

end GlobalTheory.CoefZero
