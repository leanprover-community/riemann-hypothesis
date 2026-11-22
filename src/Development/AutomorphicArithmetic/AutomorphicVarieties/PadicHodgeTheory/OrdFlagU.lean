module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharDR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCommonEigenvectorOfCharpolySplitCharacters
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.EqZeroOfTwistedCommuteOfDistinctCharacters
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsWeilInvariantInDpstOfWeilDeligneInvariant
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsInvariantOfDpstPhiFixedOfNonnegWeights
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeRhamRationalTwistByCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeRhamRationalOfConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeRhamRationalOfExtensionByCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCommonEigenline
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdPstCycRepNeTrivWD
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent

@[expose] public section

section Phi
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O]
  [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw)
  (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

variable (ρ : Representation LL ↥(GK Bw.Kw) V)

variable [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]

end

end Phi

section Priv
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

end Priv

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

