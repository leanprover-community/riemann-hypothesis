module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsMonoOdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBC0OfQuadBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteralStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotSemistableOfPotCrystallineDecompositionGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BhattScholzeCoefficientsOfPadicIntLattices
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DdRLeFilAndInfFilEqBotOfHodgeTateMult

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.Pst GlobalTheory.PstCoeff UpperTheory.V.Loc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

section Sat

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end Sat

end UpperTheory.V.Af

end
