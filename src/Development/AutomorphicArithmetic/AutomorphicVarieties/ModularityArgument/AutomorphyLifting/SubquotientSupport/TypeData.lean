import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.ExistsRec
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NzOfSteps
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CuspidalSupport2
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.DeterminantVector
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Isotypic₂
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ProductIrreducible2
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PProdRc
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarInertia
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SphericalUnramified
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSumList
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.UnramifiedTwist
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PUntwistRc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BernsteinZelevinskyFinitenessHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralAndGoodOfIsSpherical

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ UpperTheory.NonzeroTypeTheory UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.T2

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
  {rc : IrrGL (w.adicCompletion E) → WD h}







end UpperTheory.V.Z.Win.T2

