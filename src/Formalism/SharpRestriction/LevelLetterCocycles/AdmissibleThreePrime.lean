module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.AdmissibleThreePrime

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

def TheoremThreePrime (D : D7) : Prop := ArithmeticCylinders.TheoremThreePrime D

abbrev redF (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) :
    G D.host.E D.nd.Om →* GL (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i)) :=
  mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ

end Formalism.MainNotions.AdmissibleThreePrime
