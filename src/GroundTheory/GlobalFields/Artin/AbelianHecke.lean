import Mathlib
import GroundTheory.GlobalFields.Artin.Brauer
import GroundTheory.GlobalFields.Artin.OneDimExistence
import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams
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
