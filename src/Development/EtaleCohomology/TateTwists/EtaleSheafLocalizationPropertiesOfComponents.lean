import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf : Prop :=
  ∀ (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)), (∀ (U : Scheme.{0}) (y : Sec ((presheafToSheaf Scheme.etaleTopology _).obj P) U), Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology P).app (op V)).hom x = Sec.res g y) ∧ (∀ (U : Scheme.{0}) (x : P.obj (op U)), ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) ∧ ∀ (F : Shv R) (φ : P ⟶ F.obj), ∃! ψ : (presheafToSheaf Scheme.etaleTopology _).obj P ⟶ F, toSheafify Scheme.etaleTopology P ≫ ψ.hom = φ
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ShfLocPf

theorem etale_sheaf_sections_eq_of_locally_eq : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := by
  intro R _ P
  refine ⟨?_, ?_, ?_⟩
  · intro U y
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) y, ?_⟩
    intro V g hg
    obtain ⟨t, ht⟩ := hg
    exact ⟨t, ht⟩
  · intro U x hx
    have h : ((toSheafify Scheme.etaleTopology P).app (op U)).hom x =
        ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0 := by rw [hx, map_zero]
    refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) x 0 h, ?_⟩
    intro V g hg
    have hg' : (P.map g.op).hom x = (P.map g.op).hom 0 := hg
    rw [hg', map_zero]
  · intro F φ
    refine ⟨ObjectProperty.homMk (sheafifyLift Scheme.etaleTopology φ F.property), ?_, ?_⟩
    · exact toSheafify_sheafifyLift Scheme.etaleTopology φ F.property
    · intro ψ hψ
      ext1
      exact sheafifyLift_unique Scheme.etaleTopology φ F.property ψ.hom hψ

end LateralTheory.EtaleFoundations.ShfLocPf
end

section
namespace LateralTheory.Fin.EtaleSheafificationSectionsLocallyFromPresheaf
theorem etale_sheaf_localization_properties_of_components : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := by
  apply LateralTheory.EtaleFoundations.ShfLocPf.etale_sheaf_sections_eq_of_locally_eq
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := etale_sheaf_localization_properties_of_components
end LateralTheory.Fin.EtaleSheafificationSectionsLocallyFromPresheaf
end
