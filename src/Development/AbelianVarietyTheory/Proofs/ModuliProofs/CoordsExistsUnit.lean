import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotMemBasicOpenOfGeom
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.AwayLiftCompFromZeroRingHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointsVanishingIdealRadicalHomogeneous
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZM GlobalTheory.IndefiniteRowSideFullHecke.ThetaCosetLabels

noncomputable section
namespace GlobalTheory.ThetaObjCompare
attribute [local instance] MvPolynomial.gradedAlgebra

section Coords
open MvPolynomial HomogeneousIdeal
variable {σ B R R' : Type} [CommRing B] [CommRing R] [CommRing R'] {y : Sp R ⟶ PJ σ B} {β : B →+* R} {v w : σ → R}

theorem map_irrelevant_iff (β : B →+* R) (v : σ → R) :
    (irrelevant (homogeneousSubmodule σ B)).toIdeal.map (eval₂Hom β v) = ⊤ ↔ Ideal.span (Set.range v) = ⊤ := by
  suffices h : (irrelevant (homogeneousSubmodule σ B)).toIdeal.map (eval₂Hom β v) = Ideal.span (Set.range v) by rw [h]
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun F hF => ?_) (Ideal.span_le.2 ?_)
  · have h0 : homogeneousComponent 0 F = 0 := by
      have := (mem_irrelevant_iff _ F).1 hF
      rwa [GradedRing.proj_apply, ← decomposition.decompose'_apply] at *
    have h1 : F ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ B)) := by
      rw [← Set.image_univ, mem_ideal_span_X_image]
      intro m hm
      by_contra hc
      have : m = 0 := by ext i; by_contra hi; exact hc ⟨i, trivial, hi⟩
      subst this
      rw [homogeneousComponent_zero, map_eq_zero_iff _ (C_injective _ _)] at h0
      exact mem_support_iff.1 hm h0
    refine (Ideal.span_le.2 ?_ : _ ≤ Ideal.comap (eval₂Hom β v) (Ideal.span (Set.range v))) h1
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_comap.2 (by rw [eval₂Hom_X']; exact Ideal.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    rw [← eval₂Hom_X' β v i]
    exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem _ one_pos (isHomogeneous_X B i))

theorem hasCoords_iff : HasCoords y β v ↔ ∃ h, y = ProjPoint.ofHom (homogeneousSubmodule σ B) (eval₂Hom β v) h := by
  refine ⟨fun ⟨h, e⟩ => ⟨?_, e⟩, fun ⟨h, e⟩ => ⟨_, e⟩⟩
  have := ProjPoint.map_irrelevant_comp _ h (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  rwa [← RingHom.comp_assoc, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, RingHom.id_comp] at this


theorem exists_hasCoords (β : B →+* R) (hv : Ideal.span (Set.range v) = ⊤) : ∃ y : Sp R ⟶ PJ σ B, HasCoords y β v :=
  ⟨_, hasCoords_iff.2 ⟨(map_irrelevant_iff β v).2 hv, rfl⟩⟩

theorem coords_eq {y' : Sp R ⟶ PJ σ B} (h : HasCoords y β v) (h' : HasCoords y' β v) : y = y' :=
  h.2.trans h'.2.symm






end Coords

section Terms
variable {g M : ℕ} {I B : Type} [CommRing B] {ζ : Bˣ} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}

theorem isMonHom_mul {G : Over S} [GrpObj G] [IsCommMonObj G] (f h : G ⟶ G) [IsMonHom f] [IsMonHom h] :
    IsMonHom (f * h) where
  one_hom := by rw [MonObj.comp_mul, IsMonHom.one_hom, IsMonHom.one_hom, MonObj.one_eq_one, _root_.mul_one]
  mul_hom := by
    have e : ∀ k : G ⟶ G, [IsMonHom k] → (k ⊗ₘ k) ≫ μ[G] = (fst G G ≫ k) * (snd G G ≫ k) := fun k _ => by
      rw [MonObj.mul_eq_mul, MonObj.comp_mul]
      simp
    rw [MonObj.comp_mul, IsMonHom.mul_hom, IsMonHom.mul_hom, e, e, MonObj.mul_eq_mul, MonObj.comp_mul]
    simp only [← Category.assoc, tensorHom_fst, tensorHom_snd, MonObj.comp_mul]
    exact mul_mul_mul_comm _ _ _ _


theorem ev_comm {X' : ThObj g M I ζ s'} {X : ThObj g M I ζ s} {f : S' ⟶ S} {φ : X'.P.A.left ⟶ X.P.A.left}
    (h : IsGrpPullback X'.P.A X.P.A f φ) (he : ∀ i, (X'.endo i).left ≫ φ = φ ≫ (X.endo i).left) (t : EndTerm I) :
    (X'.ev t).left ≫ φ = φ ≫ (X.ev t).left := by
  let Φ : Over.mk (X'.P.A.hom ≫ f) ⟶ X.P.A := Over.homMk φ h.1.w
  suffices H : pushHom h X'.P.A (X'.ev t) = Φ ≫ X.ev t from congrArg (fun z => z.left) H
  induction t with
  | var i => exact Over.OverMorphism.ext (he i)
  | one => exact Over.OverMorphism.ext ((Category.id_comp φ).trans (Category.comp_id φ).symm)
  | add t t' H H' => exact (map_mul _ (X'.ev t) (X'.ev t')).trans (by rw [H, H']; exact (MonObj.comp_mul _ _ _).symm)
  | neg t H => exact (map_inv _ (X'.ev t)).trans (by rw [H]; exact (GrpObj.comp_inv _ _).symm)
  | mul t t' H H' =>
    have e : (X'.ev t).left ≫ φ = φ ≫ (X.ev t).left := congrArg (fun z => z.left) H
    have e' : (X'.ev t').left ≫ φ = φ ≫ (X.ev t').left := congrArg (fun z => z.left) H'
    refine Over.OverMorphism.ext ?_
    show ((X'.ev t').left ≫ (X'.ev t).left) ≫ φ = φ ≫ (X.ev t').left ≫ (X.ev t).left
    rw [Category.assoc, e, ← Category.assoc, e', Category.assoc]

end Terms

end GlobalTheory.ThetaObjCompare
end
