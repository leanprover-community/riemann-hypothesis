module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalGammaFactorExponentialForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FunctionalEquationFromContinuation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EulerProductAdjointEqStandard
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableAbsNormRpowHeightOneSpectrum

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

end Loc

