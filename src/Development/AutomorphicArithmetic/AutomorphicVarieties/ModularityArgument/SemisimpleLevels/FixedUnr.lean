module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonomialOfCountZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedCharOfCuspidalSpherical
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameter
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedIwahoriNeBotOfTwist

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end
