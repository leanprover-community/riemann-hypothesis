module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotSemistableIndependentOfInducingEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbeddingStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneMonodromyUpperTriangular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TridiagonalWeilDeligne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneTriangularizable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicWeilCharProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ContinuousCharacterCompactUnitValues
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepValuesInFiniteExtension
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepresentationModelOverFiniteExtension
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharFil
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Lev

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br

variable {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r R : G K Ω →* GL (Fin n) (Qbar l)} {π : CuspSub K n}

end UpperTheory.V.Lev

end
