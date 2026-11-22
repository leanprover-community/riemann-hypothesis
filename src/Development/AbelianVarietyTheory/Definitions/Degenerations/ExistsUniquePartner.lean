module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SameB
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN
open GlobalTheory.UU
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
  {D : DegPre R} {D' : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G'] [IsCommMonObj G']

structure Cmp (φ : R →+* V) (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) where

  pb : IsGrpPullback G' G (spMap φ) F

  wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)

  wL_map : IsCPMap U'.P U.P (spMap φ) F pb.1.w wL

  β : D'.P.A.left ⟶ D.P.A.left

  pbB : IsGrpPullback D'.P.A D.P.A (spMap φ) β

  v : LB.Iso D'.P.L (D.P.L.pull β)

  v_gen : v.IsGen

  xe : D'.X ≃+ D.X

  c_pr : ∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left

  lev : ∀ (e : ℕ) (Z : Scheme.{0}) (x' : Z ⟶ (thickObj V I' e G').left) (x : Z ⟶ (thickObj R I e G).left),
    x ≫ (fstG I e G).left = x' ≫ (fstG I' e G').left ≫ F →
    x' ≫ (U'.gt e).pG.left ≫ β = x ≫ (U.gt e).pG.left ∧
    ∀ (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' →
      (∀ χ : D'.X, val ((U.gt e).t (xe χ)) x z J = val ((U'.gt e).t χ) x' z J' *
        ∏ k : Fin 4, gw v (x' ≫ D'.Oφ (U'.gt e).pG χ k) z (J (x' ≫ D'.Oφ (U'.gt e).pG χ k ≫ β))
          (J' (x' ≫ D'.Oφ (U'.gt e).pG χ k)) ^ Oinvε k) ∧
      ∀ (k : U.P.L.L.ι) (k' : U'.P.L.L.ι), (fstG I e G).left (x z) ∈ U.P.L.L.U k → (fstG I' e G').left (x' z) ∈ U'.P.L.L.U k' →
        gw v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG.left)) (J' (x' ≫ (U'.gt e).pG.left)) *
            gw (U'.w e) x' z (J' (x' ≫ (U'.gt e).pG.left)) (fun _ => k') =
          gw (U.w e) x z (J (x ≫ (U.gt e).pG.left)) (fun _ => k) * gw wL (x' ≫ (fstG I' e G').left) z k k'

  map_le : I.map φ ≤ I' := by first | assumption | exact (Ideal.map_id _).le

def Under {D₀ : DegData R I} (U : PreU I D₀.toPre A G) (U₀ : UnifPre I D₀ A G) : Prop :=
  U.gen = U₀.gen ∧ U.P.L = U₀.LG ∧ HEq U.P.c U₀.cubG ∧ HEq U.P.sym U₀.symG ∧ U.gt = U₀.gt ∧ HEq U.w U₀.w

abbrev withPsi (D : DegPre R) (psi : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1)))
    (h : ∀ χ, (psi χ).IsGen) : DegPre R := setPsi D psi h

namespace Cmp

omit [IsDomain R] in
theorem spMap_ringHom_id : spMap (RingHom.id R) = 𝟙 _ := by
  simp [spMap]

theorem grpPullback_id {S : Scheme.{0}} (H : Over S) [GrpObj H] {f : S ⟶ S} (hf : f = 𝟙 S) :
    IsGrpPullback H H f (𝟙 H.left) := by
  subst hf
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  have hq : (𝟙 H : H ⟶ H).left ≫ H.hom = H.hom ≫ 𝟙 S := by simp
  have e₁ : x₀ = toBase hq x := Over.OverMorphism.ext hx
  have e₂ : y₀ = toBase hq y := Over.OverMorphism.ext hy
  rw [e₁, e₂, ← toBase_mul_of_isMonHom (𝟙 H) hq]
  rfl

theorem mono_fstG (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) : Mono (fstG I e G).left := by
  have hs : Function.Surjective (Ideal.Quotient.mk (I ^ (e + 1))) := Ideal.Quotient.mk_surjective
  have : Epi (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))) := ConcreteCategory.epi_of_surjective _ hs
  have : Mono (thick R I e) := Scheme.Spec.map_mono (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))).op
  exact (inferInstance : Mono (pullback.fst G.hom (thick R I e)))

variable {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left}

end Cmp

end GlobalTheory.LN
end
