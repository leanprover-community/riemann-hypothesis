module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IsoSep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ExistsNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpNat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt

@[expose] public section

section General

open UpperTheory.V.Hi Polynomial

variable {G M : Type} [Group G] (I : Iwa G) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)

end General

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance high] UpperTheory.V.W.coefLocal

