module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestriction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
