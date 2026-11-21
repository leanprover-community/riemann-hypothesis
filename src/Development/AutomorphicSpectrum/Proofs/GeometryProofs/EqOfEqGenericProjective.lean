import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.MorphismEqOfGenericPointEq
import BuildAid.ForwardExisting

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem maps_eq_of_eq_at_generic : ∀ (R : Type) [CommRing R] (Z W : Scheme.{0}) [IsIntegral Z] (s : W ⟶ Sp R) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (f g : Z ⟶ W), IsProjOver s → (∀ q : Z, genPt ξ ⤳ q) → ξ ≫ f = ξ ≫ g → f = g :=
  @PositivityTheory.UnitarySelfGeneration.morphism_eq_of_generic_point_eq

end GlobalTheory.CompanionTheory.Ar
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_eq_generic_projective : ∀ (R : Type) [CommRing R] (Z W : Scheme.{0}) [IsIntegral Z] (s : W ⟶ Sp R) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (f g : Z ⟶ W), IsProjOver s → (∀ q : Z, genPt ξ ⤳ q) → ξ ≫ f = ξ ≫ g → f = g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.maps_eq_of_eq_at_generic
