module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree

@[expose] public section

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.Aut

def IsQi (K : Type) [Field K] [NumberField K] : Prop := Module.finrank ℚ K = 2 ∧ ∃ i : K, i * i = -1

end UpperTheory.V.Aut

end
