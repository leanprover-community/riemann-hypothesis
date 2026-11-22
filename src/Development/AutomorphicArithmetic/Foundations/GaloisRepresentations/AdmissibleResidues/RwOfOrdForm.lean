module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ROrdAway
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Rwwd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharPolCharCongr

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

