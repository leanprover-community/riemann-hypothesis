import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DeligneLocalConstants
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLocalLanglands

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.MeasTest

section Tate

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ψ : AddChar k Circle} {χ : kˣ →* ℂˣ} {t : ℝ}





end Tate

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}



def powFam : EpsMeasFamily A := fun _ _ _ _ _ _ _ _ t x => WD.unitOf (t : ℂ) ^ x.lpDim





end GlobalTheory.LocLanglands.MeasTest

end
