module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolvableEquivalenceOfBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SdDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsContragredientCuspSub

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol

namespace UpperTheory.V.Z.Bc

def ExRTwo : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (π : TR.CuspSub F 2) (χ : HChar F), π.IsRegAlg → π.Polarized χ →
    ∃ r : G F Ω →* GL (Fin 2) (Qbar l), Continuous r ∧ AttR ι r π

end UpperTheory.V.Z.Bc
