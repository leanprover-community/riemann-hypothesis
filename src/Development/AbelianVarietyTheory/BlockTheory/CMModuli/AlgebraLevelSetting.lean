module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.AlgebraLevelSetting

section Levels

variable {S S₁ S₂ : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

variable {P : CP G} {X : Type} [AddCommGroup X] {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S}
  {G₁ : Over S₁} [GrpObj G₁] [IsCommMonObj G₁] {F₁ : G₁.left ⟶ G.left} {h₁ : F₁ ≫ G.hom = G₁.hom ≫ f₁}
  {G₂ : Over S₂} [GrpObj G₂] [IsCommMonObj G₂] {F₂ : G₂.left ⟶ G.left} {h₂ : F₂ ≫ G.hom = G₂.hom ≫ f₂}

variable {B : Over S} [GrpObj B] [IsCommMonObj B]

namespace Level.Red

variable {L₁ : Level P X f₁ G₁ F₁ h₁} {M : CP B} (r : L₁.Red M)

end Level.Red

end Levels

section Formal

variable {R : Type} [CommRing R] (I : Ideal R) {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  {X : Type} [AddCommGroup X]

abbrev Lv (e : ℕ) : Scheme.{0} := Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))

abbrev pr (e : ℕ) (G : Over (Spec (CommRingCat.of R))) : (thickObj R I e G).left ⟶ G.left :=
  pullback.fst G.hom (thick R I e)

structure FormalTorus (i₀ : splitTorus (Lv I 0) X ⟶ thickObj R I 0 G) where

  i : ∀ e : ℕ, splitTorus (Lv I e) X ⟶ thickObj R I e G
  hom : ∀ e, IsMonHom (i e)
  zero : i 0 = i₀
  compat : ∀ e, TorusCompat (thickTrans R I e) (thickMap R I e G) (i e) (i (e + 1))

variable {I}

variable [IsCommMonObj G]

instance (priority := high) isCommMonObj_thickObj (e : ℕ) : IsCommMonObj (thickObj R I e G) := inferInstance

variable (I)

variable {I} {P : CP G} {i₀ : splitTorus (Lv I 0) X ⟶ thickObj R I 0 G}

attribute [instance] Alg.grp Alg.comm

end Formal

attribute [instance] HidaSetting.grp HidaSetting.comm HidaSetting.addX HidaSetting.freeX HidaSetting.finX

namespace HidaSetting

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (S : HidaSetting V)

end HidaSetting

end GlobalTheory.IndefiniteRowSideFullHecke.AlgebraLevelSetting
end
