import Mathlib
import GroundTheory.GlobalFields.Artin.Induction
import GroundTheory.GlobalFields.Artin.OneDimL
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.LocalFields.BrauerInduction
import GroundTheory.GlobalFields.Artin.OneDimExistence
import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams

section
set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain NumberField IntermediateField Filter Topology Set

namespace GroundTheory.Global

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

variable (K L) in
open Classical in

def continuedArtinL (f : Gal(L/K) → ℂ) : ℂ → ℂ :=
  if h : ∃ F : ℂ → ℂ, MeromorphicNFOn F univ ∧ ∀ s : ℂ, 1 < s.re → F s = artinL K L f s then
    h.choose else 0

section Subgroup

variable (H : Subgroup Gal(L/K))

def fixedFieldChar (l : H →* ℂˣ) : Gal(L/fixedField H) →* ℂˣ :=
  l.comp (Artin.fixedFieldMulEquiv H).symm.toMonoidHom

end Subgroup

section Product

variable [Fintype Gal(L/K)] {ι : Type*} [Fintype ι] {H : ι → Subgroup Gal(L/K)} [∀ i, Fintype (H i)]
  (c : ι → ℤ) (l : ∀ i, H i →* ℂˣ)

end Product

section Virtual

variable [Fintype Gal(L/K)]

open GroundTheory.LocalField

end Virtual

end GroundTheory.Global
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain NumberField IntermediateField Filter Topology Set Complex

namespace GroundTheory.Global

open GroundTheory.LocalField

section Group

variable {G : Type*} [Group G] [Fintype G]




end Group

namespace HeckeCharacter

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup


end HeckeCharacter

section Hecke

universe u

theorem eq_one_of_heckeCharacterOfChar_eq_one {K L : Type u} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] (χ : Gal(L/K) →* ℂˣ) (h : heckeCharacterOfChar χ = 1) :
    χ = 1 := by
  ext σ
  obtain ⟨c, hc⟩ := reciprocityMap_surjective (K := K) (L := ↥(charField χ))
    (AlgEquiv.restrictNormalHom (charField χ) σ)
  have h1 := heckeCharacterOfChar_apply χ c
  rw [h, hc, charBar_restrictNormalHom] at h1
  simpa using h1.symm

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]


end Hecke

end GroundTheory.Global
end
end
