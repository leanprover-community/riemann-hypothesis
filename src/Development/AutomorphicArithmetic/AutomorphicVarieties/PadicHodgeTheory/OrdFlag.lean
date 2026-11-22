module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharDR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.InertiaEigenvectorExtendsOfDistinctCharacters
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsInvariantVectorOfFiniteImageAveraging
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsFrobeniusFixedPeriod
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsInvariantOfDpstPhiFixedOfNonnegWeights
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeRhamRationalTwistByCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeRhamRationalOfConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeRhamRationalOfExtensionByCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCommonEigenline
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdPstCycRepNeTrivWD
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices

open GlobalTheory.Pst Polynomial Module Matrix Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)

end SlopeTestRemainingChoices

section Main

open GlobalTheory.Pst Polynomial Module Matrix Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)

end Main

