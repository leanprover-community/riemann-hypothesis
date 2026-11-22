module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FunExt

section Cyc

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def CycAt (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) : Prop :=
  IsGalois K L ∧ (Module.finrank K L).Prime ∧ u.under (𝓞 K) = v ∧
    ∀ u' : HeightOneSpectrum (𝓞 L), u'.under (𝓞 K) = v → u' = u

end Cyc

section Loc

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

end Loc

section Ind

variable (K : Type) {L Ω : Type} [Field K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]

end Ind

end GlobalTheory.FunExt

end
