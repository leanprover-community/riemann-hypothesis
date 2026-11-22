module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsSpehOne
public import Mathlib

@[expose] public section

open UpperTheory.V.Af UpperTheory.V.Af.Gu

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

