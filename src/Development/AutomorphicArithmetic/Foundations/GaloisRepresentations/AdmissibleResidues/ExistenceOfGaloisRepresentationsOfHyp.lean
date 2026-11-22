module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsGalRepOfOfIso
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistenceOfGaloisRepresentationsOfHyp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.ExLib

end UpperTheory.GalN.V

namespace UpperTheory.V.Af

variable {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {R : G K Ω →* GL (Fin n) (Qbar l)} {π : CuspSub K n}

end UpperTheory.V.Af

end
