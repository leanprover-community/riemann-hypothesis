module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DelEps.GaussBridge

open GroundTheory.LocalField (valBall unitFiltrationUnits addCharConductor quasiCharConductor
  IsUnramifiedChar unifUnit unitsModRep unitsModFiltration unitsModCoset gaussSum)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

variable {χ : Fˣ →* ℂˣ} {ψ : AddChar F Circle}

end GlobalTheory.DelEps.GaussBridge

