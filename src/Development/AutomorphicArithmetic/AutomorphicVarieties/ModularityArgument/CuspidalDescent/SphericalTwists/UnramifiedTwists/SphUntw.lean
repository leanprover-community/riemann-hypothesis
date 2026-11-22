module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.GdLaws
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportCharacters
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MongeAmpereChartDensityIntegral
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MonodromyVanishesWeilTwistIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfHasSatGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbeddingProdIrrSupport

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC

open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.W

section WD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end WD

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Loc

end UpperTheory.V.Z.Desc.W
