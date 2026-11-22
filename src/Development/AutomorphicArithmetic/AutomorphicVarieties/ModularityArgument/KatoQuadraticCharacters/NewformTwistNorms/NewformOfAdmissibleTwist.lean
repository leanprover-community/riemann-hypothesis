module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinReciprocityMapUnique
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharConjInvariant
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicSolutionParallel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SignAtInfinityOfParallelWeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LevelQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.JumpsOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.TwNewform

instance (priority := high + 1) torsionFree (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

end GlobalTheory.Ord2.TwNewform

namespace GlobalTheory.Ord2


end GlobalTheory.Ord2

end

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

end
