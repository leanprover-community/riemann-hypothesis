import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.Whittaker GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.LocalLanglandsExistence₂

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_place (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    ∃ A : ValuationSubring (AlgebraicClosure E), IsPlaceOver A w :=
  ⟨_, isPlaceOver_placeOf _ w⟩


theorem eq_lpZero {x : WD h} (hx : x.lpDim = 0) : x = WD.lpZero h := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  obtain rfl : n = 0 := by simpa using hx
  exact WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩






end GlobalTheory.LocLanglands.LocalLanglandsExistence₂

end
