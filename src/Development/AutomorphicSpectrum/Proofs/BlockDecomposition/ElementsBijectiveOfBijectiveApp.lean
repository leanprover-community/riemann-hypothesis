import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import BuildAid.ForwardExisting

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.Cech

theorem elMor_bijective_of_bijective {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R) (h : ∀ T, Function.Bijective (p.app T)) (n : ℕ) : Function.Bijective ((elMor p F).hom.f n) := by
  haveI : ∀ T, IsIso (p.app T) := fun T => (isIso_iff_bijective _).2 (h T)
  haveI : IsIso p := NatIso.isIso_of_isIso_app p
  have e1 : ∀ x, (elMor (inv p) F).pullC n ((elMor p F).pullC n x) = x := fun x => by
    have e : (inv p ≫ p : E ⟶ E) = 𝟙 E := IsIso.inv_hom_id p
    exact congrArg (fun a => (elMor a F).pullC n x) e
  have e2 : ∀ x, (elMor p F).pullC n ((elMor (inv p) F).pullC n x) = x := fun x => by
    have e : (p ≫ inv p : E' ⟶ E') = 𝟙 E' := IsIso.hom_inv_id p
    exact congrArg (fun a => (elMor a F).pullC n x) e
  exact Function.bijective_iff_has_inverse.2 ⟨(elMor (inv p) F).pullC n, e1, e2⟩

end GlobalTheory.CompanionTheory.Cech
end

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elements_bijective_of_bijective_app : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R), (∀ T, Function.Bijective (p.app T)) → ∀ n, Function.Bijective ((elMor p F).hom.f n) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Cech.elMor_bijective_of_bijective
