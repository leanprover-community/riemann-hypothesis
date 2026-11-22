module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdmissibleLocalComponentDefiniteUnitary
public import Mathlib.RingTheory.Teichmuller
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsotypicOfJointlyInjectiveIntoIsotypic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsTensorDualEmbeddingOfHasWeightAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnderChosenPlaceAndIsSplitAtOfDecompLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PlaceEmbeddingsBijectiveInfinitePlaces
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNonzeroFormFixedByLevelOfUnramified

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} (n : ℕ) {V : s.Lev} (Q : QData V)

variable {n Q}

end

