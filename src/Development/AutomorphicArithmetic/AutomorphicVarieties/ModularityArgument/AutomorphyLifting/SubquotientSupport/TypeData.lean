module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.ExistsRec
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NzOfSteps
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CuspidalSupport2
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.DeterminantVector
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Isotypic₂
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ProductIrreducible2
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PProdRc
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarInertia
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SphericalUnramified
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSumList
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.UnramifiedTwist
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PUntwistRc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWeilDeligneEqDiagonalInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BernsteinZelevinskyFinitenessHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralAndGoodOfIsSpherical

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ UpperTheory.NonzeroTypeTheory UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.T2

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}

end UpperTheory.V.Z.Win.T2
