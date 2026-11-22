module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.LocCFT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LamFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.DenseBox
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycInertia
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section Ball

variable {l : ℕ} [Fact l.Prime]

end Ball

section Grp

variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]

variable {I : Subgroup Γ} {d : ℕ} (A : W.LocAb l Γ I d)

end Grp

section Loc

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion F)ˣ}

end Loc

