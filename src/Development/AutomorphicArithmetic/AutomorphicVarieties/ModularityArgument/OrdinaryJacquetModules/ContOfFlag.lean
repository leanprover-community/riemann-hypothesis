module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.ExtChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcrossOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.CompatTOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.QuadraticCharpolySplitting.ThruLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.QuadraticCharpolySplitting.RcChars
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportTwistNuCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardFiberEqOfSumEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaConv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharDR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PstExact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCount
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ForallFieldIffForallSubgroup
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdPstCycRepNeTrivWD

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open GlobalTheory.Pst GlobalTheory.TripleGal Module
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

namespace UpperTheory.V.Z.Ord.OrdinaryPolarizedFromFlag

section Tri

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

end Tri

section Loc

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}

end Loc

end UpperTheory.V.Z.Ord.OrdinaryPolarizedFromFlag

end
