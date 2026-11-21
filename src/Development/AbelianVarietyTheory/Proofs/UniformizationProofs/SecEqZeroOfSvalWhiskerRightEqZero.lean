import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem app_whiskerRight_injective_of_flat :
    ∀ (S : Scheme.{0}) (B T T' : Over S) [Flat B.hom] [IsAffine T.left] [IsAffine T'.left] (φ : T' ⟶ T), Function.Injective φ.left.appTop.hom → ∀ U : (T ⊗ B).left.Opens, Function.Injective ((φ ▷ B).left.app U).hom := by
  intro S B T T' _ _ _ φ hφ U
  have hd : IsSchemeTheoreticallyDominant φ.left := by
    refine ⟨Scheme.IdealSheafData.ext_of_isAffine ?_⟩
    rw [Scheme.Hom.ker_apply]
    simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    rw [← RingHom.injective_iff_ker_eq_bot]
    exact hφ
  have pb : IsPullback (pullback.fst T'.hom B.hom) (φ ▷ B).left φ.left (pullback.fst T.hom B.hom) := by
    refine (IsPullback.of_right (h₁₁ := (φ ▷ B).left) (v₁₁ := pullback.fst T'.hom B.hom)
      (h₂₁ := φ.left) (v₁₂ := pullback.fst T.hom B.hom) ?_ (Over.whiskerRight_left_fst φ)
      (IsPullback.of_hasPullback T.hom B.hom).flip).flip
    rw [Over.whiskerRight_left_snd, Over.w]
    exact (IsPullback.of_hasPullback T'.hom B.hom).flip
  have : IsSchemeTheoreticallyDominant (φ ▷ B).left := .of_isPullback pb
  have : QuasiCompact (φ ▷ B).left := MorphismProperty.of_isPullback pb inferInstance
  exact (φ ▷ B).left.app_injective U

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sec_eq_zero_of_sval_eq_zero_of_app_injective {X Y Z : Scheme.{0}} (r : Z ⟶ Y)
    (hr : ∀ U : Y.Opens, Function.Injective (r.app U).hom) (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε))
    (h : ∀ (z : Z) (J), Good L z J → sval d r z J = 0) (j : K → L.ι) : d.f j = 0 := by
  apply hr (LB.wchart L φ j)
  refine fn_ext fun z hz => ?_
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have hz' : r z ∈ LB.wchart L φ j := hz
  have e₁ : gs r z (LB.wchart L φ j) (d.f j) = 0 :=
    (sec_trans d r z hz' (Good.mem hI φ r)).trans ((congrArg _ (h z I hI)).trans (mul_zero _))
  have e₂ : gs r z (LB.wchart L φ j) 0 = 0 := by
    rw [gs_eq r z _ hz', map_zero, map_zero]
  refine (gs_pull (𝟙 Z) r z _ hz' _).trans (Eq.trans ?_ (gs_pull (𝟙 Z) r z _ hz' _).symm)
  rw [Category.id_comp]
  exact e₁.trans e₂.symm

theorem sec_eq_zero_of_sval_whiskerRight_eq_zero :
    ∀ (S : Scheme.{0}) (B T T' : Over S) [Flat B.hom] [IsAffine T.left] [IsAffine T'.left] (ψ : T' ⟶ T), Function.Injective ψ.left.appTop.hom → ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → ((T ⊗ B).left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (z : (T' ⊗ B).left) (J), Good L z J → sval d (ψ ▷ B).left z J = 0) → ∀ j, d.f j = 0 := by
  intro S B T T' _ _ _ ψ hψ X L hL K _ φ ε d h j
  exact sec_eq_zero_of_sval_eq_zero_of_app_injective (ψ ▷ B).left
    (app_whiskerRight_injective_of_flat S B T T' ψ hψ) L hL φ ε d h j

end GlobalTheory
end
