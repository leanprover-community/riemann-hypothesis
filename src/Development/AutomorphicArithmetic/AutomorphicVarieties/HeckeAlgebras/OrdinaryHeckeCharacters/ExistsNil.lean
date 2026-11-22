module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.EqOfTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PropCker
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqMult
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqEmbed

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Hi.OrdB

open GlobalTheory.PRep

section General

variable {G V : Type} [CommGroup G] [AddCommGroup V] [Module ℂ V]

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace.SeparableSpace G]

end General

section Abs

variable {G M : Type} [Group G] (I : Iwa G) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ G M) (c : ℕ)
  (φ : I.T →* ℂˣ)

end Abs

section Num

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

end Num

end UpperTheory.V.Hi.OrdB

