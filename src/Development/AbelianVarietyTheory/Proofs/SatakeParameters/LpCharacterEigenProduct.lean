module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.DetSp

open Polynomial TensorProduct Module

variable {E : Type*} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

end GlobalTheory.WeilDeligne.DetSp

namespace GlobalTheory.WeilDeligne

end GlobalTheory.WeilDeligne
