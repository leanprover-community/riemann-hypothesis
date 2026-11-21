import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFinite

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory

theorem finite_lift_fractionField (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (Z P : Scheme.{0}) (p : Z ⟶ P) (ξ₀ : Sp R ⟶ P) (y : Sp (FractionRing R) ⟶ Z)
    (hp : IsFinite p) (hy : y ≫ p = jK R ≫ ξ₀) :
    ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ∧ ξ ≫ p = ξ₀ := by
  first
  | exact @_root_.GlobalTheory.RetractionLiftSection.lift_finite
  | exact _root_.GlobalTheory.RetractionLiftSection.lift_finite
  | (apply _root_.GlobalTheory.RetractionLiftSection.lift_finite <;> assumption)
  | (intros; apply _root_.GlobalTheory.RetractionLiftSection.lift_finite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RetractionLiftSection.lift_finite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RetractionLiftSection.lift_finite ..)

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_morphism_valuative_lifting_normal_domain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (Z P : Scheme.{0}) (p : Z ⟶ P) (ξ₀ : Sp R ⟶ P) (y : Sp (FractionRing R) ⟶ Z), IsFinite p → y ≫ p = jK R ≫ ξ₀ → ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ∧ ξ ≫ p = ξ₀ := by
  atlas_forward_decl GlobalTheory.finite_lift_fractionField
