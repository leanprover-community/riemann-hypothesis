module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesSatakeParameters

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Hi.PsIrr

open GlobalTheory.SplitRead

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end UpperTheory.V.Hi.PsIrr

