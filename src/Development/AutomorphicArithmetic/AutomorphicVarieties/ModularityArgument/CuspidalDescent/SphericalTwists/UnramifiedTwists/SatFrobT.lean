module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonFactorRecCompatible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FieldPointLiftsGenericFibre

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.W.SatakeFrobeniusEigenvalues

open Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped commutatorElement

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end UpperTheory.V.Z.Desc.W.SatakeFrobeniusEigenvalues

