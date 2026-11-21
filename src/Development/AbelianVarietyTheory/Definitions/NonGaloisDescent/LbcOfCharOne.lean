import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Lbc
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ScholzeFunctorialExtension

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FunExt.LbcModel

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} {u : HeightOneSpectrum (𝓞 L)}




end GlobalTheory.FunExt.LbcModel
