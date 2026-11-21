import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TensorFinite

variable {S : Scheme.{0}}

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in

theorem _root_.GlobalTheory.TensorFinite.isFinite_of_comp {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) [IsSeparated Y.hom]
    (h : IsFinite (f ≫ g).left) : IsFinite f.left := by
  haveI : IsFinite (f.left ≫ g.left) := by rwa [← Over.comp_left]
  haveI : IsSeparated g.left :=
    MorphismProperty.of_postcomp (W := @IsSeparated) (W' := ⊤) (f := g.left) (g := Z.hom)
      (hg := trivial) (hfg := by rw [Over.w g]; infer_instance)
  exact IsFinite.of_comp f.left g.left

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in

theorem _root_.GlobalTheory.TensorFinite.isFinite_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y') (hf : IsFinite f.left)
    (hg : IsFinite g.left) : IsFinite (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullback_map (P := @IsFinite) hf hg (Over.w f).symm (Over.w g).symm






end GlobalTheory.TensorFinite
