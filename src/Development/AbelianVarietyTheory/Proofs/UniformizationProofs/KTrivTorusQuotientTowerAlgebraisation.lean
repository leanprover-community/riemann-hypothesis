import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TwistedPowTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOfGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKIffTrivialTwist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivOfGeneric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionGeometricPointOfField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OverPointsExtOfInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemOfCubWeilOrthogonal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqAbelianPartDimAddTorusRank
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFormalTorusPointsSemiAbelianModel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartImageOneMulInv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartImageEqOneIffTorusPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNRatioTwist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAffineWeightUnits
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.dim_eq_abelianPart_dim_add_torus_rank : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (g' : ℕ), (SmoothOfRelativeDimension g' (t.l 0).Q.B.hom → A.g = g' + Module.finrank ℤ s.X) ∧ ∀ a : t.Alg, SmoothOfRelativeDimension g' a.B.hom → A.g = g' + Module.finrank ℤ s.X := by
  first | exact @GlobalTheory.UU.Tower.dim_eq_add_finrank | exact GlobalTheory.UU.Tower.dim_eq_add_finrank | (intros; apply GlobalTheory.UU.Tower.dim_eq_add_finrank <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_formalTorus_points_semiAbelian_model : AllSet fun {V} _ _ _ {_} {G} _ _ s => ∀ (t : Tower s) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∃ ι' : (Multiplicative s.X →* Wˣ) →* (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G), Function.Injective ι' ∧ ∀ (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (a : Multiplicative s.X →* Wˣ), x = ι' a ↔ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ s.X).left), τ ≫ (splitTorus (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)))) s.X).hom ≫ thick V _ e = r ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) → (∀ χ, τ.appTop.hom (charUnit _ s.X χ).val = scal r (a (Multiplicative.ofAdd χ)).val) → τ ≫ (t.l e).Q.i.left ≫ (fstG _ e G).left = r ≫ x.left := by
  first | exact @GlobalTheory.UU.exists_formalTorus_points | exact GlobalTheory.UU.exists_formalTorus_points | (intros; apply GlobalTheory.UU.exists_formalTorus_points <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.PointImage

def levelHom {R W : Type} [CommRing R] [CommRing W] (f : R →+* W) (I : Ideal R) (n : ℕ) :
    R ⧸ I ^ n →+* W ⧸ (I.map f) ^ n :=
  Ideal.quotientMap _ f (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)

theorem isPushout_level {R W : Type} [CommRing R] [CommRing W] (f : R →+* W) (I : Ideal R) (n : ℕ) :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))
      (CommRingCat.ofHom (Ideal.Quotient.mk ((I.map f) ^ n))) (CommRingCat.ofHom (levelHom f I n)) := by
  have w : CommRingCat.ofHom f ≫ CommRingCat.ofHom (Ideal.Quotient.mk ((I.map f) ^ n)) =
      CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)) ≫ CommRingCat.ofHom (levelHom f I n) := rfl
  have hk : ∀ s : PushoutCocone (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))),
      ∀ a ∈ (I.map f) ^ n, s.inl.hom a = 0 := by
    intro s a ha
    rw [← Ideal.map_pow] at ha
    have : (I ^ n).map f ≤ RingHom.ker s.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      have h := congrArg (fun φ => φ.hom y) s.condition
      change s.inl.hom (f y) = s.inr.hom (Ideal.Quotient.mk _ y) at h
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy, map_zero] at h
      exact h
    exact this ha
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk w
    (fun s => CommRingCat.ofHom (Ideal.Quotient.lift _ s.inl.hom (hk s))) (fun s => rfl)
    (fun s => ?_) (fun s m h _ => ?_)⟩⟩
  · apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    exact congrArg CommRingCat.Hom.hom s.condition
  · apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    exact congrArg CommRingCat.Hom.hom h

theorem isPullback_level {R W : Type} [CommRing R] [CommRing W] (f : R →+* W) (I : Ideal R) (e : ℕ) :
    IsPullback (adicLevelι (I.map f) (e + 1)) (Spec.map (CommRingCat.ofHom (levelHom f I (e + 1))))
      (Spec.map (CommRingCat.ofHom f)) (thick R I e) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_level f I (e + 1))

theorem thick_mono' (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) : Mono (thick R I e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

theorem existsUnique_image {R W : Type} [CommRing R] [CommRing W] [IsLocalRing W] (f : R →+* W)
    (I : Ideal R) [IsAdicComplete (I.map f) W] {G B : Scheme.{0}}
    (pG : G ⟶ Spec (CommRingCat.of R)) (pB : B ⟶ Spec (CommRingCat.of R))
    {P : ℕ → Scheme.{0}} (fst : ∀ e, P e ⟶ G)
    (snd : ∀ e, P e ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (hP : ∀ e, IsPullback (fst e) (snd e) pG (thick R I e))
    (τ : ∀ e, P e ⟶ P (e + 1)) (hm : ∀ e, τ e ≫ fst (e + 1) = fst e)
    (φ : ∀ e, P e ⟶ B) (hφ : ∀ e, φ e ≫ pB = snd e ≫ thick R I e)
    (hc : ∀ e, τ e ≫ φ (e + 1) = φ e)
    (x : Spec (CommRingCat.of W) ⟶ G) (hx : x ≫ pG = Spec.map (CommRingCat.ofHom f)) :
    ∃! b : Spec (CommRingCat.of W) ⟶ B, b ≫ pB = Spec.map (CommRingCat.ofHom f) ∧
      ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ P e),
        xe ≫ fst e = r ≫ x → xe ≫ φ e = r ≫ b := by
  have hw : ∀ e, (adicLevelι (I.map f) (e + 1) ≫ x) ≫ pG =
      Spec.map (CommRingCat.ofHom (levelHom f I (e + 1))) ≫ thick R I e := fun e => by
    rw [← (isPullback_level f I e).w, Category.assoc, hx]
  choose y hy hy2 using fun e => (hP e).exists_lift _ _ (hw e)
  have hmono : ∀ e, Mono (fst e) := fun e =>
    (MorphismProperty.monomorphisms Scheme).of_isPullback (hP e).flip (thick_mono' R I e)
  have hfam : IsAdicFamily (I.map f) (fun e => y e ≫ φ e) := by
    intro e
    have : adicLevelMap (I.map f) (Nat.le_succ (e + 1)) ≫ y (e + 1) = y e ≫ τ e := by
      rw [← cancel_mono (fst (e + 1)), Category.assoc, hy,
        adicLevelMap_ι_assoc, Category.assoc, hm, hy]
    change _ ≫ y (e + 1) ≫ φ (e + 1) = y e ≫ φ e
    rw [← hc e, ← Category.assoc, this, Category.assoc]
  obtain ⟨g, ⟨hg, hg'⟩, hu⟩ := existsUnique_over_of_isAdicFamily (Spec.map (CommRingCat.ofHom f))
    pB hfam (fun e => by
      rw [(isPullback_level f I e).w, ← hy2, Category.assoc, hφ, Category.assoc])
  refine ⟨g, ⟨hg, fun e Z r xe h => ?_⟩, fun b hb => ?_⟩
  · have hr : r ≫ Spec.map (CommRingCat.ofHom f) = (xe ≫ snd e) ≫ thick R I e := by
      rw [← hx, ← Category.assoc, ← h, Category.assoc, (hP e).w, Category.assoc]
    obtain ⟨l, hl, -⟩ := (isPullback_level f I e).exists_lift _ _ hr
    have hxe : xe = l ≫ y e := by
      rw [← cancel_mono (fst e), h, ← hl, Category.assoc, Category.assoc, hy]
    rw [hxe, ← hl, Category.assoc, Category.assoc, hg']
  · exact hu b ⟨hb.1, fun e => (hb.2 e _ _ (y e) (hy e)).symm⟩

theorem main : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, ∃! b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ x
  obtain ⟨g, ⟨hg, hg'⟩, hu⟩ := existsUnique_image (algebraMap V W) (IsLocalRing.maximalIdeal V)
    G.hom a.B.hom (P := fun e => (thickObj V (IsLocalRing.maximalIdeal V) e G).left)
    (fun e => (fstG _ e G).left) (fun e => (thickObj V (IsLocalRing.maximalIdeal V) e G).hom)
    (fun e => IsPullback.of_hasPullback G.hom (thick V _ e)) (fun e => thickMap V _ e G)
    (fun e => (pullback.lift_fst _ _ _).trans (Category.comp_id _))
    (fun e => (t.l e).Q.q.left ≫ a.b e)
    (fun e => by
      obtain ⟨h, -⟩ := a.b_pb e
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
    (fun e => by rw [← a.b_β e, ← Category.assoc, ← t.β_q e, Category.assoc])
    x.left (Over.w x)
  exact ⟨Over.homMk g hg, hg', fun b hb => Over.OverMorphism.ext (hu b.left ⟨Over.w b, hb⟩)⟩

end GlobalTheory.UU.PointImage
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_abelianPart_image_adicComplete_point : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, ∃! b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) := by
  atlas_forward_decl GlobalTheory.UU.PointImage.main
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.abelianPart_image_one_mul_inv : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [Algebra V W] (x x' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b b' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G)).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B)).left) ∧ ((∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b').left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x * x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b * b').left) ∧ (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x⁻¹).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b⁻¹).left)) := by
  first | exact @GlobalTheory.UU.image_one_mul_inv | exact GlobalTheory.UU.image_one_mul_inv | (intros; apply GlobalTheory.UU.image_one_mul_inv <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.abelianPart_image_eq_one_iff_torus_point : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B)).left) ↔ ∃ c : Multiplicative s.X →* Wˣ, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ s.X).left), τ ≫ (splitTorus (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))) s.X).hom ≫ thick V _ e = r ≫ (Spec.map (CommRingCat.ofHom (algebraMap V W))) → (∀ χ, τ.appTop.hom (charUnit _ s.X χ).val = scal r (c (Multiplicative.ofAdd χ)).val) → τ ≫ (t.l e).Q.i.left ≫ (fstG _ e G).left = r ≫ (x).left) := by
  first | exact @GlobalTheory.UU.image_eq_one_iff_torus_point | exact GlobalTheory.UU.image_eq_one_iff_torus_point | (intros; apply GlobalTheory.UU.image_eq_one_iff_torus_point <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.ImagePairing

theorem eq_map_of_isCPMap {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'}
    [GrpObj G'] [IsCommMonObj G'] {P : CP G} {P' : CP G'} {F : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) {N : ℕ} {T' : Over S'} {T : Over S} (r : T'.left ⟶ T.left)
    (hr : r ≫ T.hom = T'.hom ≫ f) {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : x'.left ≫ F = r ≫ x.left)
    (hy : y'.left ≫ F = r ≫ y.left) {ζ' ζ} (h' : CubWeil P'.c N x' y' ζ') (h₀ : CubWeil P.c N x y ζ) :
    ζ' = Units.map r.appTop.hom.toMonoidHom ζ := by
  let ρ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk r hr
  have a := cubWeil_map S S' f G G' P P' F hw w h N T' x' y' ζ' h'
  have ex : toBase hw x' = ρ ≫ x := Over.OverMorphism.ext hx
  have ey : toBase hw y' = ρ ≫ y := Over.OverMorphism.ext hy
  rw [ex, ey] at a
  exact a.unique (h₀.comp ρ)

theorem pow_eq_one_of_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] {N : ℕ} {T' : Over S'}
    {T : Over S} (r : T'.left ⟶ T.left) (hr : r ≫ T.hom = T'.hom ≫ f) {x' : T' ⟶ (Over.pullback f).obj G}
    {x : T ⟶ G} (hx : x'.left ≫ pullback.fst G.hom f = r ≫ x.left) (h : x ^ N = 1) : x' ^ N = 1 := by
  let ρ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk r hr
  let β : (T' ⟶ (Over.pullback f).obj G) →* (Over.mk (T'.hom ≫ f) ⟶ G) :=
    MonoidHom.mk' (toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f) pullback.condition)
      (toBase_mul_pullback G f T')
  have ex : β x' = ρ ≫ x := Over.OverMorphism.ext hx
  have e : β (x' ^ N) = β 1 := by rw [map_pow, map_one, ex, ← MonObj.comp_pow, h, MonObj.comp_one]
  refine Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) e) ?_)
  exact (Over.w (x' ^ N)).trans (Over.w (1 : T' ⟶ (Over.pullback f).obj G)).symm

theorem fn_eq_of_thick {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    (a b : Γ(Spec (CommRingCat.of R), ⊤))
    (h : ∀ e, (thick R I e).appTop.hom a = (thick R I e).appTop.hom b) : a = b := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  have key : ∀ (e : ℕ) (c : Γ(Spec (CommRingCat.of R), ⊤)),
      Ideal.Quotient.mk (I ^ (e + 1)) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) =
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (e + 1)))).hom.hom ((thick R I e).appTop.hom c) := fun e c =>
    (congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))).symm
  have := IsHausdorff.StrictMono.funext' I (a := fun n => n + 1) (strictMono_id.add_const 1)
    (f := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a)
    (g := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b)
    (fun n _ => (key n a).trans ((congrArg _ (h n)).trans (key n b).symm))
  exact congrFun this ()

theorem exists_thick_hom {V W : Type} [CommRing V] [CommRing W] [Algebra V W] (I : Ideal V) (e : ℕ) :
    ∃ φ : Spec (CommRingCat.of (W ⧸ (I.map (algebraMap V W)) ^ (e + 1))) ⟶ Spec (CommRingCat.of (V ⧸ I ^ (e + 1))),
      thick W (I.map (algebraMap V W)) e ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) = φ ≫ thick V I e := by
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap V W) ?_)), ?_⟩
  · rw [← Ideal.map_pow]; exact Ideal.le_comap_map
  · simp only [thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]

theorem cubWeil_image : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ (N : ℕ) (x x' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b b' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B) (ζ), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b').left) → b ^ N = 1 → b' ^ N = 1 → CubWeil s.P.c N x x' ζ → CubWeil a.M.c N b b' ζ := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ N x x' b b' ζ hx hx' hb hb' h
  obtain ⟨ξ, hξ, -⟩ := existsUnique_cubWeil a.M.c hb hb'
  suffices e : ζ = ξ from e ▸ hξ
  refine Units.ext (fn_eq_of_thick ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) _ _ fun e => ?_)
  obtain ⟨φ, hφ⟩ := exists_thick_hom (W := W) (IsLocalRing.maximalIdeal V) e
  let r := thick W ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) e
  have lifts : ∀ y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G,
      ∃ ye : Over.mk φ ⟶ thickObj V (IsLocalRing.maximalIdeal V) e G,
        ye.left ≫ pullback.fst G.hom (thick V _ e) = r ≫ y.left := fun y =>
    ⟨Over.homMk (pullback.lift (r ≫ y.left) φ ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (Over.w y)).trans hφ)))
      (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _⟩
  obtain ⟨y, hy⟩ := lifts x
  obtain ⟨y', hy'⟩ := lifts x'
  obtain ⟨θ, hθ, -⟩ := existsUnique_cubWeil (t.l e).Pe.c
    (pow_eq_one_of_pullback (T' := Over.mk φ) (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))))
      _ r hφ hy h.1)
    (pow_eq_one_of_pullback (T' := Over.mk φ) (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))))
      _ r hφ hy' h.2.1)
  obtain ⟨w, hw⟩ := (t.l e).lev
  obtain ⟨hp, v, hv⟩ := a.b_pb e
  have e₁ := eq_map_of_isCPMap hw (T' := Over.mk φ)
    (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) r hφ hy hy' hθ h
  obtain ⟨u, -, hu⟩ := hv.exists_comp (t.l e).D.map (by
    rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w, Category.id_comp])
  have e₂ := eq_map_of_isCPMap hu (T' := Over.mk φ)
    (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) r
    (hφ.trans (congrArg (φ ≫ ·) (Category.id_comp _).symm)) (hx e _ r y.left hy) (hx' e _ r y'.left hy') hθ hξ
  exact congrArg Units.val (e₁.symm.trans e₂)

end GlobalTheory.UU.ImagePairing
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.cubicalWeilPairing_eq_abelianPart_image : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ (N : ℕ) (x x' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b b' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B) (ζ), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b').left) → b ^ N = 1 → b' ^ N = 1 → CubWeil s.P.c N x x' ζ → CubWeil a.M.c N b b' ζ := by
  first | exact @GlobalTheory.UU.ImagePairing.cubWeil_image | exact GlobalTheory.UU.ImagePairing.cubWeil_image | (intros; apply GlobalTheory.UU.ImagePairing.cubWeil_image <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.AffineFactorExists

theorem exists_affine_factor {F : Type} [Field F] {X : Scheme.{0}}
    (x : Spec (CommRingCat.of F) ⟶ X) :
    ∃ (A : CommRingCat.{0}) (ι : Spec A ⟶ X) (_ : IsOpenImmersion ι) (φ : A ⟶ CommRingCat.of F),
      Spec.map φ ≫ ι = x := by
  obtain ⟨i, z, hz⟩ := X.affineCover.exists_eq (x default)
  let ι : Spec _ ⟶ X := X.affineCover.f i
  have hι : IsOpenImmersion ι := inferInstanceAs (IsOpenImmersion (X.affineCover.f i))
  have hr : Set.range x ⊆ Set.range ι := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = default := Subsingleton.elim _ _
    exact ⟨z, hz⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift ι x hr)
  exact ⟨_, ι, hι, φ, by rw [hφ, IsOpenImmersion.lift_fac]⟩

theorem exists_factor_fractionRing {V A F : Type} [CommRing V] [CommRing A] [Field F]
    [Algebra V A] [Algebra V F] (φ : A →ₐ[V] F) (s : Set A) (hs : Algebra.adjoin V s = ⊤)
    (W : Subalgebra V F)
    (h : ∀ a ∈ s, ∃ u ∈ W, ∃ v ∈ W, v ≠ (0 : F) ∧ φ a * v = u) :
    ∃ (j : FractionRing W →+* F) (φ' : A →+* FractionRing W),
      j.comp (algebraMap W (FractionRing W)) = algebraMap W F ∧ j.comp φ' = φ.toRingHom := by
  have hinj : Function.Injective (algebraMap W F) := Subtype.val_injective
  let j : FractionRing W →+* F := IsFractionRing.lift hinj
  have hj : ∀ w : W, j (algebraMap W (FractionRing W) w) = w := fun w =>
    IsFractionRing.lift_algebraMap hinj w
  have hmem : ∀ a : A, φ a ∈ j.range := by
    intro a
    have ha : a ∈ Algebra.adjoin V s := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨u, hu, v, hv, hv0, e⟩ := h a ha
      refine ⟨algebraMap W _ ⟨u, hu⟩ / algebraMap W _ ⟨v, hv⟩, ?_⟩
      rw [map_div₀, hj, hj, div_eq_iff hv0, e]
    | algebraMap r =>
      exact ⟨algebraMap W _ (algebraMap V W r), by rw [hj, AlgHom.commutes]; rfl⟩
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let e : FractionRing W ≃+* j.range :=
    RingEquiv.ofBijective j.rangeRestrict
      ⟨j.rangeRestrict.injective, j.rangeRestrict_surjective⟩
  refine ⟨j, e.symm.toRingHom.comp (φ.toRingHom.codRestrict j.range hmem), RingHom.ext hj, ?_⟩
  ext a
  exact congrArg Subtype.val (e.apply_symm_apply ⟨φ a, hmem a⟩)

theorem exists_finset_extends (V F : Type) [CommRing V] [Field F] [Algebra V F]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [IsProper f]
    (x : Spec (CommRingCat.of F) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V F))) :
    ∃ t : Finset F, ∀ W : Subalgebra V F, ValuationRing W →
      (∀ x ∈ t, ∃ a ∈ W, ∃ b ∈ W, b ≠ (0 : F) ∧ x * b = a) →
      ∃ y : Spec (CommRingCat.of W) ⟶ X,
        y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V W)) ∧
        Spec.map (CommRingCat.ofHom (algebraMap W F)) ≫ y = x := by
  classical
  obtain ⟨A, ι, hι, φ, hφ⟩ := exists_affine_factor x
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (ι ≫ f)
  have hft : ψ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hψ]
    infer_instance
  have hcomp : ψ ≫ φ = CommRingCat.ofHom (algebraMap V F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, ← Category.assoc, hφ, hx]
  letI : Algebra V A := ψ.hom.toAlgebra
  have hft' : Algebra.FiniteType V A := hft
  obtain ⟨s, hs⟩ := hft'.out
  let φa : A →ₐ[V] F :=
    { φ.hom with commutes' := fun r => congrArg (fun g => g.hom r) hcomp }
  refine ⟨s.image φ.hom, fun W hW ht => ?_⟩
  obtain ⟨j, φ', hj, hφ'⟩ := exists_factor_fractionRing φa s hs W
    (fun a ha => ht _ (Finset.mem_image_of_mem _ ha))
  have hE : ValuativeCriterion.Existence f := by
    have : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at this
    exact this.1
  have hring : ψ ≫ CommRingCat.ofHom φ' =
      CommRingCat.ofHom (algebraMap V W) ≫
        CommRingCat.ofHom (algebraMap W (FractionRing W)) := by
    ext r
    apply j.injective
    have h1 := RingHom.congr_fun hφ' (ψ.hom r)
    have h2 := RingHom.congr_fun hj (algebraMap V W r)
    exact (h1.trans (φa.commutes r)).trans h2.symm
  have w : (Spec.map (CommRingCat.ofHom φ') ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap W (FractionRing W))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V W)) := by
    rw [Category.assoc, ← hψ, ← Spec.map_comp, ← Spec.map_comp, hring]
  obtain ⟨l, hl₁, hl₂⟩ :=
    (hE { R := W, K := FractionRing W, commSq := ⟨w⟩, .. }).exists_lift
  dsimp only at hl₁ hl₂
  refine ⟨l, hl₂, ?_⟩
  have e₁ : CommRingCat.ofHom (algebraMap W F) =
      CommRingCat.ofHom (algebraMap W (FractionRing W)) ≫ CommRingCat.ofHom j := by
    rw [← hj]; rfl
  have e₂ : φ = CommRingCat.ofHom φ' ≫ CommRingCat.ofHom j := by
    ext a
    exact (RingHom.congr_fun hφ' a).symm
  rw [e₁, Spec.map_comp, Category.assoc, hl₁, ← Category.assoc, ← Spec.map_comp, ← e₂, hφ]

end GlobalTheory.AffineFactorExists
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_finset_point_extends_valuationSubalgebra (V F : Type) [CommRing V] [Field F]
    [Algebra V F] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [IsProper f]
    (x : Spec (CommRingCat.of F) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V F))) :
    ∃ t : Finset F, ∀ W : Subalgebra V F, ValuationRing W →
      (∀ x ∈ t, ∃ a ∈ W, ∃ b ∈ W, b ≠ 0 ∧ x * b = a) →
      ∃ y : Spec (CommRingCat.of W) ⟶ X,
        y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V W)) ∧
        Spec.map (CommRingCat.ofHom (algebraMap W F)) ≫ y = x := by
  first
  | exact @_root_.GlobalTheory.AffineFactorExists.exists_finset_extends
  | exact _root_.GlobalTheory.AffineFactorExists.exists_finset_extends
  | (apply _root_.GlobalTheory.AffineFactorExists.exists_finset_extends <;> assumption)
  | (intros; apply _root_.GlobalTheory.AffineFactorExists.exists_finset_extends <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AffineFactorExists.exists_finset_extends <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AffineFactorExists.exists_finset_extends ..)

theorem exists_finset_points_extend_valuationSubalgebra : ∀ (V F : Type) [CommRing V] [Field F] [Algebra V F] (B : Over (Spec (CommRingCat.of V))) [IsProper B.hom] (s : Set (Spec (CommRingCat.of F) ⟶ B.left)), s.Finite → (∀ x ∈ s, x ≫ B.hom = (Spec.map (CommRingCat.ofHom (algebraMap V F)))) → ∃ t : Finset F, ∀ W : Subalgebra V F, ValuationRing W → (∀ x ∈ t, ∃ a ∈ W, ∃ b ∈ W, b ≠ 0 ∧ x * b = a) → ∀ x ∈ s, ∃ y : Spec (CommRingCat.of W) ⟶ B.left, y ≫ B.hom = (Spec.map (CommRingCat.ofHom (algebraMap V W))) ∧ (Spec.map (CommRingCat.ofHom (algebraMap W F))) ≫ y = x := by
  intro V F _ _ _ B _ s hs hx
  classical
  choose t ht using fun x : s =>
    exists_finset_point_extends_valuationSubalgebra V F B.hom x.1 (hx x.1 x.2)
  haveI := hs.fintype
  refine ⟨Finset.univ.biUnion t, fun W hW h x hxs => ht ⟨x, hxs⟩ W hW fun a ha => h a ?_⟩
  exact Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, ha⟩

end GlobalTheory
end

section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianPartLift

section General
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem exists_torus_lift [Module.Free ℤ X] {Z' Z : Over S} (ρ : Z' ⟶ Z)
    (h : ∀ a : Γ(Z'.left, ⊤)ˣ, ∃ r : Γ(Z.left, ⊤)ˣ, ρ.left.appTop.hom r.val = a.val)
    (t : Z' ⟶ splitTorus S X) : ∃ t' : Z ⟶ splitTorus S X, ρ ≫ t' = t := by
  let e := Module.Free.chooseBasis ℤ X
  choose r hr using h
  let l : X →ₗ[ℤ] Additive Γ(Z.left, ⊤)ˣ := e.constr ℤ fun k => Additive.ofMul (r (chV t (e k)))
  let m : X →ₗ[ℤ] Additive Γ(Z'.left, ⊤)ˣ :=
    (MonoidHom.toAdditiveRight (splitTorusPointsEquiv S X Z' t)).toIntLinearMap
  let n : Additive Γ(Z.left, ⊤)ˣ →ₗ[ℤ] Additive Γ(Z'.left, ⊤)ˣ :=
    (MonoidHom.toAdditive (Units.map ρ.left.appTop.hom.toMonoidHom)).toIntLinearMap
  have hl : n ∘ₗ l = m := e.ext fun k => by
    rw [LinearMap.comp_apply, Module.Basis.constr_basis]
    exact congrArg Additive.ofMul (Units.ext (hr _))
  let t' := (splitTorusPointsEquiv S X Z).symm (AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom)
  have ht' : ∀ χ, chV t' χ = Additive.toMul (l χ) := fun χ => by
    rw [chV, MulEquiv.apply_symm_apply]; rfl
  refine ⟨t', (splitTorusPointsEquiv S X Z').injective (MonoidHom.ext fun χ => Units.ext ?_)⟩
  have e₁ : (chV (ρ ≫ t') (Multiplicative.toAdd χ)).val = ρ.left.appTop.hom (chV t' (Multiplicative.toAdd χ)).val := by
    rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]
  refine e₁.trans ?_
  rw [ht']
  exact congrArg (fun a => (Additive.toMul a).val) (LinearMap.congr_fun hl (Multiplicative.toAdd χ))

theorem units_lift {A A' : Type} [CommRing A] [CommRing A'] [IsLocalRing A] [IsLocalRing A'] (f : A →+* A')
    (hf : Function.Surjective f) (a : Γ(Spec (CommRingCat.of A'), ⊤)ˣ) :
    ∃ r : Γ(Spec (CommRingCat.of A), ⊤)ˣ, (Spec.map (CommRingCat.ofHom f)).appTop.hom r.val = a.val := by
  have : IsLocalHom f := IsLocalHom.of_surjective f hf
  obtain ⟨c, hc⟩ := hf ((Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom a.val)
  have hu : IsUnit c := IsUnit.of_map f c (hc ▸ a.isUnit.map _)
  refine ⟨(hu.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).unit, ?_⟩
  rw [IsUnit.unit_spec]
  have e := congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  rw [← e, hc]
  exact congrArg (fun q => q.hom a.val) (Scheme.ΓSpecIso (CommRingCat.of A')).hom_inv_id

theorem exists_lift_extending [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    {A A' : Type} [CommRing A] [CommRing A'] [IsLocalRing A] [IsLocalRing A'] (f : A →+* A')
    (hf : Function.Surjective f) (b : Spec (CommRingCat.of A) ⟶ Q.B.left) (y : Spec (CommRingCat.of A') ⟶ G.left)
    (hy : y ≫ Q.q.left = Spec.map (CommRingCat.ofHom f) ≫ b) :
    ∃ g : Spec (CommRingCat.of A) ⟶ G.left, g ≫ Q.q.left = b ∧ Spec.map (CommRingCat.ofHom f) ≫ g = y := by
  have := Q.q_hom
  have := Q.i_hom
  let b' : Over.mk (b ≫ Q.B.hom) ⟶ Q.B := Over.homMk b rfl
  let y' : Over.mk (y ≫ G.hom) ⟶ G := Over.homMk y rfl
  let ρ : Over.mk (y ≫ G.hom) ⟶ Over.mk (b ≫ Q.B.hom) := Over.homMk (Spec.map (CommRingCat.ofHom f)) (by
    change Spec.map (CommRingCat.ofHom f) ≫ b ≫ Q.B.hom = y ≫ G.hom
    rw [← Category.assoc, ← hy, Category.assoc, Over.w])
  have hy' : y' ≫ Q.q = ρ ≫ b' := Over.OverMorphism.ext hy
  obtain ⟨g, hg⟩ := Q.exists_lift b'
  have h₁ : (y' * (ρ ≫ g)⁻¹) ≫ Q.q = toUnit _ ≫ η[Q.B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hg, hy', mul_inv_cancel, Hom.one_def]
  obtain ⟨t, ht⟩ := exists_torus_lift ρ (units_lift f hf) (Q.isKernel.lift _ _ h₁)
  have h₃ : (t ≫ Q.i) ≫ Q.q = 1 := by
    rw [Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (t ≫ toUnit _) (toUnit _)]
  have a₁ : ((t ≫ Q.i) * g) ≫ Q.q = b' := by rw [MonObj.mul_comp, h₃, _root_.one_mul, hg]
  have a₂ : ρ ≫ ((t ≫ Q.i) * g) = y' := by
    rw [MonObj.comp_mul, ← Category.assoc, ht, IsPullback.lift_fst, inv_mul_cancel_right]
  exact ⟨((t ≫ Q.i) * g).left, congrArg (fun q => q.left) a₁, congrArg (fun q => q.left) a₂⟩

end General

open GlobalTheory.FormalPoint

theorem main : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B, ∃ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ b
  let I := IsLocalRing.maximalIdeal V
  let φ := algebraMap V W
  let J := I.map φ
  have hJ : J ≠ ⊤ := ne_top_of_isHausdorff J
  have hloc := isLocalRing_quotient_pow hJ
  have hbw : b.left ≫ a.B.hom = Spec.map (CommRingCat.ofHom φ) := Over.w b
  have pb : ∀ e, IsPullback (a.b e) (t.l e).Q.B.hom a.B.hom (thick V I e) := fun e => (a.b_pb e).1.1
  have w : ∀ e, (adicLevelι J (e + 1) ≫ b.left) ≫ a.B.hom = levelMap I φ e ≫ thick V I e := fun e =>
    (Category.assoc _ _ _).trans ((congrArg _ hbw).trans (levelMap_thick I φ e).symm)
  let c : ∀ e, Spec (CommRingCat.of (W ⧸ J ^ (e + 1))) ⟶ (t.l e).Q.B.left := fun e => (pb e).lift _ _ (w e)
  have c₁ : ∀ e, c e ≫ a.b e = adicLevelι J (e + 1) ≫ b.left := fun e => (pb e).lift_fst _ _ _
  have c₂ : ∀ e, c e ≫ (t.l e).Q.B.hom = levelMap I φ e := fun e => (pb e).lift_snd _ _ _
  have mth : ∀ e, Mono (thick V I e) := fun e => have := isClosedImmersion_red (I ^ (e + 1)); inferInstance
  have mono : ∀ e, Mono (a.b e) := fun e =>
    (MorphismProperty.monomorphisms _).of_isPullback (pb e).flip (mth e)
  have cc : ∀ e, c e ≫ t.β e = adicLevelMap J (Nat.le_succ (e + 1)) ≫ c (e + 1) := fun e => by
    have := mono (e + 1)
    rw [← cancel_mono (a.b (e + 1)), Category.assoc, Category.assoc, a.b_β, c₁, c₁, adicLevelMap_ι_assoc]
  let P := fun e => {x : Spec (CommRingCat.of (W ⧸ J ^ (e + 1))) ⟶ (thickObj V I e G).left //
    x ≫ (t.l e).Q.q.left = c e}
  have base : Nonempty (P 0) := by
    obtain ⟨g, hg⟩ := (t.l 0).Q.exists_lift (Over.homMk (c 0) rfl : Over.mk (c 0 ≫ (t.l 0).Q.B.hom) ⟶ (t.l 0).Q.B)
    exact ⟨⟨g.left, congrArg (fun q => q.left) hg⟩⟩
  have step : ∀ e (x : P e), ∃ x' : P (e + 1),
      adicLevelMap J (Nat.le_succ (e + 1)) ≫ x'.1 = x.1 ≫ thickMap V I e G := fun e x => by
    obtain ⟨g, h₁, h₂⟩ := exists_lift_extending (t.l (e + 1)).Q (Ideal.Quotient.factorPow J (Nat.le_succ (e + 1)))
      (Ideal.Quotient.factor_surjective _) (c (e + 1)) (x.1 ≫ thickMap V I e G)
      (by rw [Category.assoc, ← t.β_q, ← Category.assoc, x.2, cc])
    exact ⟨⟨g, h₁⟩, h₂⟩
  choose nx hnx using step
  let x : ∀ e, P e := fun e => Nat.rec base.some nx e
  have hx : ∀ e, adicLevelMap J (Nat.le_succ (e + 1)) ≫ (x (e + 1)).1 = (x e).1 ≫ thickMap V I e G :=
    fun e => hnx e (x e)
  have tm : ∀ e, thickMap V I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left := fun e =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have fam : IsAdicFamily J fun e => (x e).1 ≫ (fstG I e G).left := fun e => by
    rw [← Category.assoc, hx, Category.assoc, tm]
  have fw : ∀ e, (fstG I e G).left ≫ G.hom = (thickObj V I e G).hom ≫ thick V I e := fun e => pullback.condition
  obtain ⟨g, ⟨g₁, g₂⟩, -⟩ := existsUnique_over_of_isAdicFamily (Spec.map (CommRingCat.ofHom φ)) G.hom fam fun e => by
    rw [Category.assoc, fw, ← Over.w (t.l e).Q.q, Category.assoc, ← Category.assoc, (x e).2, ← Category.assoc, c₂]
    exact levelMap_thick I φ e
  refine ⟨Over.homMk g g₁, fun e Z r xe h => ?_⟩
  replace h : xe ≫ (fstG I e G).left = r ≫ g := h
  obtain ⟨l, rfl⟩ := exists_factor_level I φ r (xe ≫ (thickObj V I e G).hom) (by
    rw [Category.assoc, ← fw, ← Category.assoc, h, Category.assoc, g₁])
  have : Mono (fstG I e G).left := have := mth e; (inferInstance : Mono (pullback.fst G.hom (thick V I e)))
  have hxe : xe = l ≫ (x e).1 := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc, Category.assoc, g₂]
  rw [hxe, Category.assoc, Category.assoc, ← c₁, ← Category.assoc (x e).1, (x e).2]

end GlobalTheory.AbelianPartLift
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.TorsionLift

theorem exists_char_root {X M : Type} [AddCommGroup X] [CommGroup M] {I : Type} (β : Module.Basis I ℤ X)
    (N : ℕ) (c : Multiplicative X →* M) (h : ∀ i, ∃ u : M, u ^ N = c (Multiplicative.ofAdd (β i))) :
    ∃ d : Multiplicative X →* M, d ^ N = c := by
  choose u hu using h
  let l : X →ₗ[ℤ] Additive M := β.constr ℤ (fun i => Additive.ofMul (u i))
  refine ⟨AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom, ?_⟩
  have : N • l = (MonoidHom.toAdditiveRight c).toIntLinearMap := by
    refine β.ext fun i => ?_
    simp only [l, LinearMap.smul_apply, Module.Basis.constr_basis, ← ofMul_pow, hu]
    rfl
  refine MonoidHom.ext fun x => ?_
  have h2 := congrArg Additive.toMul (LinearMap.congr_fun this x.toAdd)
  rw [LinearMap.smul_apply, toMul_nsmul] at h2
  exact h2

theorem exists_big (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V] (F : Type) [Field F] [IsAlgClosed F] [Algebra V F]
    [FaithfulSMul V F] [Algebra.IsAlgebraic V F] (W₁ : Subalgebra V F) [Module.Finite V W₁] (N : ℕ) (hN : 1 ≤ N)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {J : Type} [Finite J]
    (c : J → (Multiplicative X →* (W₁)ˣ)) :
    ∃ (W : Subalgebra V F) (_ : IsLocalRing W) (h : W₁ ≤ W),
      IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W ∧ IsLocalHom (algebraMap V W) ∧
      (∀ z : F, z ^ N = 1 → z ∈ W) ∧
      ∀ j, ∃ d : Multiplicative X →* (W)ˣ,
        d ^ N = (Units.map (Subalgebra.inclusion h).toRingHom.toMonoidHom).comp (c j) := by
  classical
  let β := Module.Free.chooseBasis ℤ X
  have hz : ∀ j i, ∃ z : F, z ^ N = ((c j (Multiplicative.ofAdd (β i))).val : F) :=
    fun j i => IsAlgClosed.exists_pow_nat_eq _ hN
  choose z hz using hz
  obtain ⟨g, hg⟩ := (Module.Finite.fg_top (R := V) (M := W₁))
  have := Fintype.ofFinite J
  let s : Finset F := (g.image Subtype.val ∪ Polynomial.nthRootsFinset N 1) ∪
    (Finset.univ.image fun p : J × Module.Free.ChooseBasisIndex ℤ X => z p.1 p.2)
  obtain ⟨W, hW, -, hc, -, -, hl, -, hint⟩ := GlobalTheory.exists_complete_dvr_finite_subalgebra V F s
  have hI : ∀ w : W₁, IsIntegral V (w : F) := fun w =>
    (Algebra.IsIntegral.isIntegral (R := V) w).map W₁.val
  have hle : W₁ ≤ W := by
    intro w hw
    have : (⟨w, hw⟩ : W₁) ∈ Submodule.span V (g : Set W₁) := hg ▸ Submodule.mem_top
    have h2 : Submodule.span V (g : Set W₁) ≤ (Subalgebra.toSubmodule W).comap W₁.val.toLinearMap := by
      rw [Submodule.span_le]
      intro a ha
      exact hint a (by simp only [s, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl ⟨a, ha, rfl⟩)) (hI a)
    exact h2 this
  refine ⟨W, inferInstance, hle, hc, hl, ?_, fun j => exists_char_root β N _ fun i => ?_⟩
  · intro x hx
    refine hint x ?_ (IsIntegral.of_pow hN (by rw [hx]; exact isIntegral_one))
    simp only [s, Finset.mem_union]
    exact Or.inl (Or.inr ((Polynomial.mem_nthRootsFinset hN 1).2 hx))
  · have hm : z j i ∈ W := by
      refine hint _ ?_ (IsIntegral.of_pow hN (by rw [hz]; exact hI _))
      simp only [s, Finset.mem_union, Finset.mem_image]
      exact Or.inr ⟨(j, i), Finset.mem_univ _, rfl⟩
    have he : (⟨z j i, hm⟩ : W) ^ N =
        (((Units.map (Subalgebra.inclusion hle).toRingHom.toMonoidHom).comp (c j)) (Multiplicative.ofAdd (β i))).val :=
      Subtype.ext (hz j i)
    have hu : IsUnit (⟨z j i, hm⟩ : W) := by
      rw [← isUnit_pow_iff (n := N) (by omega), he]; exact Units.isUnit _
    refine ⟨hu.unit, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, hu.unit_spec, he]

section
variable {V : Type} [CommRing V]

abbrev PT (V W : Type) [CommRing V] [CommRing W] [Algebra V W] : Over (Spec (CommRingCat.of V)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))

def ptMap {W W' : Type} [CommRing W] [CommRing W'] [Algebra V W] [Algebra V W'] (ψ : W →ₐ[V] W') :
    PT V W' ⟶ PT V W :=
  Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ψ.comp_algebraMap)

theorem scal_comp_specMap {W W' : Type} [CommRing W] [CommRing W'] (ψ : W →+* W') {Z : Scheme.{0}}
    (r : Z ⟶ Spec (CommRingCat.of W')) (w : W) :
    scal (r ≫ Spec.map (CommRingCat.ofHom ψ)) w = scal r (ψ w) := by
  unfold scal
  rw [Scheme.Hom.comp_appTop]
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)
  have h2 := congrArg (fun f => f.hom w) this
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 ⊢
  rw [h2]
end

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] {s : HidaSetting V A G}

def Im (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [Algebra V W] (x : PT V W ⟶ G) (b : PT V W ⟶ a.B) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left

def Tp (t : Tower s) (W : Type) [CommRing W] [Algebra V W] (x : PT V W ⟶ G) (c : Multiplicative s.X →* Wˣ) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ s.X).left), τ ≫ (splitTorus (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))) s.X).hom ≫ thick V _ e = r ≫ (Spec.map (CommRingCat.ofHom (algebraMap V W))) → (∀ χ, τ.appTop.hom (charUnit _ s.X χ).val = scal r (c (Multiplicative.ofAdd χ)).val) → τ ≫ (t.l e).Q.i.left ≫ (fstG _ e G).left = r ≫ (x).left

theorem Im.pull {t : Tower s} {a : t.Alg} {W W' : Type} [CommRing W] [Algebra V W] [CommRing W'] [Algebra V W']
    (ψ : W →ₐ[V] W') {x : PT V W ⟶ G} {b : PT V W ⟶ a.B} (h : Im t a W x b) :
    Im t a W' (ptMap ψ ≫ x) (ptMap ψ ≫ b) := by
  intro e Z r xe hxe
  have := h e Z (r ≫ (ptMap ψ).left) xe (by rw [hxe, Category.assoc]; rfl)
  rw [this, Category.assoc]; rfl

theorem Tp.pull {t : Tower s} {W W' : Type} [CommRing W] [Algebra V W] [CommRing W'] [Algebra V W']
    (ψ : W →ₐ[V] W') {x : PT V W ⟶ G} {c : Multiplicative s.X →* Wˣ} (h : Tp t W x c) :
    Tp t W' (ptMap ψ ≫ x) ((Units.map ψ.toRingHom.toMonoidHom).comp c) := by
  intro e Z r τ h1 h2
  have := h e Z (r ≫ (ptMap ψ).left) τ (by
      rw [h1, Category.assoc]; exact congrArg (r ≫ ·) (Over.w (ptMap ψ)).symm)
    (fun χ => (h2 χ).trans (scal_comp_specMap ψ.toRingHom r _).symm)
  rw [this, Category.assoc]; rfl

theorem Im.pow {t : Tower s} {a : t.Alg} {W : Type} [CommRing W] [Algebra V W]
    {x : PT V W ⟶ G} {b : PT V W ⟶ a.B} (h : Im t a W x b) (n : ℕ) : Im t a W (x ^ n) (b ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact (GlobalTheory.UU.image_one_mul_inv V A G s t a W x x b b).1
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ((GlobalTheory.UU.image_one_mul_inv V A G s t a W _ x _ b).2 ih h).1

theorem correct {t : Tower s} {a : t.Alg} {W : Type} [CommRing W] [IsLocalRing W] [Algebra V W]
    (hc : IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W) (hl : IsLocalHom (algebraMap V W))
    {x : PT V W ⟶ G} {b : PT V W ⟶ a.B} (h : Im t a W x b) (N : ℕ) (d : Multiplicative s.X →* Wˣ)
    (hd : Tp t W (x ^ N) (d ^ N)) : ∃ y : PT V W ⟶ G, y ^ N = 1 ∧ Im t a W y b := by
  obtain ⟨κ, -, hk⟩ := GlobalTheory.UU.exists_formalTorus_points V A G s t W hc hl
  have h1 : x ^ N = κ (d ^ N) := (hk _ _).2 hd
  have h2 : Im t a W (κ d) 1 :=
    (GlobalTheory.UU.image_eq_one_iff_torus_point V A G s t a W hc hl (κ d)).2 ⟨d, (hk _ _).1 rfl⟩
  have h3 : Im t a W (κ d)⁻¹ 1⁻¹ := ((GlobalTheory.UU.image_one_mul_inv V A G s t a W _ _ _ _).2 h2 h2).2
  have h4 : Im t a W (x * (κ d)⁻¹) (b * 1⁻¹) := ((GlobalTheory.UU.image_one_mul_inv V A G s t a W _ _ _ _).2 h h3).1
  rw [inv_one, _root_.mul_one] at h4
  refine ⟨_, ?_, h4⟩
  rw [mul_pow, h1, inv_pow, map_pow, mul_inv_cancel]

theorem finiteRing_sq_sub_mul_sq_eq_of_card (t : Tower s) (a : t.Alg) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F]
    [Algebra.IsAlgebraic (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (N : ℕ) (hN : 1 ≤ N)
    (hfin : Finite {x : TF (R := V) F ⟶ a.B // x ^ N = 1}) :
    ∃ (W : Subalgebra V F) (_ : IsLocalRing W),
      IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W ∧ IsLocalHom (algebraMap V W) ∧
      (∀ z : F, z ^ N = 1 → z ∈ W) ∧ ∀ x : TF (R := V) F ⟶ a.B, x ^ N = 1 →
        ∃ (y : PT V W ⟶ G) (b : PT V W ⟶ a.B), y ^ N = 1 ∧ Im t a W y b ∧
          Spec.map (CommRingCat.ofHom W.val.toRingHom) ≫ b.left = x.left := by
  obtain ⟨h1, h2, h3⟩ := s.cdvr
  have hfs : FaithfulSMul V F := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq V (FractionRing V) F]
    exact (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _)
  have halg : Algebra.IsAlgebraic V F := (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := FractionRing V)).2 inferInstance
  have hp := a.isAb.proper
  have hTF : (TF (R := V) F).hom = Spec.map (CommRingCat.ofHom (algebraMap V F)) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨T, hT⟩ := GlobalTheory.exists_finset_points_extend_valuationSubalgebra V F a.B
    (Set.range fun x : {x : TF (R := V) F ⟶ a.B // x ^ N = 1} => x.1.left) (Set.finite_range _)
    (by rintro _ ⟨x, rfl⟩; exact (Over.w x.1).trans hTF)
  obtain ⟨W₁, hW₁, -, hc₁, hf₁, -, hl₁, hfr, -⟩ := GlobalTheory.exists_complete_dvr_finite_subalgebra V F T
  have hb : ∀ x : {x : TF (R := V) F ⟶ a.B // x ^ N = 1}, ∃ b : PT V W₁ ⟶ a.B,
      Spec.map (CommRingCat.ofHom W₁.val.toRingHom) ≫ b.left = x.1.left := fun x => by
    obtain ⟨y, hy, hy'⟩ := hT W₁ inferInstance hfr _ ⟨x, rfl⟩
    exact ⟨Over.homMk y hy, hy'⟩
  choose b hb using hb
  let q : TF (R := V) F ⟶ PT V W₁ := Over.homMk (Spec.map (CommRingCat.ofHom W₁.val.toRingHom))
    ((Over.w (ptMap W₁.val)).trans hTF.symm)
  have hbN : ∀ x, b x ^ N = 1 := fun x => by
    have hq : q ≫ b x = x.1 := Over.OverMorphism.ext (hb x)
    refine GlobalTheory.over_points_ext_of_injective _ a.B W₁ F W₁.val.toRingHom Subtype.val_injective _ _ _ ?_
    have : q ≫ (b x ^ N) = q ≫ 1 := by rw [MonObj.comp_pow, MonObj.comp_one, hq, x.2]
    exact congrArg (·.left) this
  have hy : ∀ x, ∃ y : PT V W₁ ⟶ G, Im t a W₁ y (b x) := fun x =>
    GlobalTheory.AbelianPartLift.main V A G s t a W₁ hc₁ hl₁ (b x)
  choose y hy using hy
  have hc : ∀ x, ∃ c, Tp t W₁ (y x ^ N) c := fun x =>
    (GlobalTheory.UU.image_eq_one_iff_torus_point V A G s t a W₁ hc₁ hl₁ _).1 (by
      have := (hy x).pow N
      rw [hbN] at this
      exact this)
  choose c hc using hc
  obtain ⟨W, hW, hle, hcW, hlW, hz, hd⟩ := exists_big V F W₁ N hN c
  refine ⟨W, hW, hcW, hlW, hz, fun x hx => ?_⟩
  obtain ⟨d, hd⟩ := hd ⟨x, hx⟩
  have h5 := (hc ⟨x, hx⟩).pull (Subalgebra.inclusion hle)
  rw [← hd, MonObj.comp_pow] at h5
  obtain ⟨y', hy1, hy2⟩ := correct hcW hlW ((hy ⟨x, hx⟩).pull (Subalgebra.inclusion hle)) N d h5
  refine ⟨y', _, hy1, hy2, ?_⟩
  rw [← hb ⟨x, hx⟩]
  change Spec.map _ ≫ Spec.map _ ≫ _ = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem torsion_lift : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (N : ℕ), 1 ≤ N → ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : W →+* F), Function.Injective φ ∧ φ.comp (algebraMap V W) = (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)) ∧ IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W ∧ IsLocalHom (algebraMap V W) ∧ (∀ z : F, z ^ N = 1 → z ∈ φ.range) ∧ ∀ x : TF (R := V) F ⟶ a.B, x ^ N = 1 → ∃ (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B), y ^ N = 1 ∧ (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (y).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) ∧ (Spec.map (CommRingCat.ofHom φ)) ≫ b.left = x.left := by
  intro hcard V _ _ _ A G _ _ s t a F _ _ _ _ N hN
  letI : Algebra V F := ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))).toAlgebra
  haveI : IsScalarTower V (FractionRing V) F := IsScalarTower.of_algebraMap_eq' rfl
  have hch : CharZero V := s.cdvr.2.2
  haveI : CharZero F := charZero_of_injective_ringHom (f := algebraMap V F)
    ((algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _))
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim V a.B a.isAb
  have hn := GlobalTheory.card_torsion_geometricPoint_of_field hcard _ a.B a.isAb g hg F (TF (R := V) F).hom N
    (Nat.cast_ne_zero.2 (by omega))
  have hfin : Finite {x : TF (R := V) F ⟶ a.B // x ^ N = 1} :=
    Nat.finite_of_card_ne_zero (hn.trans_ne (pow_ne_zero _ (by omega)))
  obtain ⟨W, hW, h1, h2, h3, h4⟩ := finiteRing_sq_sub_mul_sq_eq_of_card t a F N hN hfin
  exact ⟨W, inferInstance, hW, inferInstance, W.val.toRingHom, Subtype.val_injective, rfl, h1, h2,
    fun z hz => ⟨⟨z, h3 z hz⟩, rfl⟩, h4⟩

end GlobalTheory.TorsionLift
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_lift_abelianPart_finite_extension : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (N : ℕ), 1 ≤ N → ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : W →+* F), Function.Injective φ ∧ φ.comp (algebraMap V W) = (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)) ∧ IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W ∧ IsLocalHom (algebraMap V W) ∧ (∀ z : F, z ^ N = 1 → z ∈ φ.range) ∧ ∀ x : TF (R := V) F ⟶ a.B, x ^ N = 1 → ∃ (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B), y ^ N = 1 ∧ (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (y).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) ∧ (Spec.map (CommRingCat.ofHom φ)) ≫ b.left = x.left := by
  first | exact @GlobalTheory.TorsionLift.torsion_lift | exact GlobalTheory.TorsionLift.torsion_lift | (intros; apply GlobalTheory.TorsionLift.torsion_lift <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.NondegGen

theorem card_hom_lattice (X U : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [CommGroup U] :
    Nat.card (Multiplicative X →* U) = Nat.card U ^ Module.finrank ℤ X := by
  have e1 : (Multiplicative X →* U) ≃ (X →ₗ[ℤ] Additive U) :=
    (MonoidHom.toAdditiveRight).trans (addMonoidHomLequivInt ℤ).toEquiv
  have e2 := ((Module.finBasis ℤ X).constr ℤ (M' := Additive U)).toEquiv
  rw [Nat.card_congr (e1.trans e2.symm), Nat.card_fun, Nat.card_congr (Additive.toMul : Additive U ≃ U)]
  simp

theorem card_roots (W F : Type) [CommRing W] [Field F] [IsAlgClosed F] (φ : W →+* F) (hφ : Function.Injective φ)
    (N : ℕ) (hN : (N : F) ≠ 0) (h : ∀ z : F, z ^ N = 1 → z ∈ φ.range) : Nat.card (rootsOfUnity N W) = N := by
  haveI : NeZero (N : F) := ⟨hN⟩
  haveI : NeZero N := ⟨fun e => hN (by simp [e])⟩
  refine Eq.trans (Nat.card_congr ?_) (HasEnoughRootsOfUnity.natCard_rootsOfUnity F N)
  refine (Equiv.ofBijective (restrictRootsOfUnity φ N) ⟨fun a b e => ?_, fun z => ?_⟩)
  · have := congrArg (fun u : rootsOfUnity N F => ((u : Fˣ) : F)) e
    simp only [restrictRootsOfUnity_coe_apply] at this
    exact Subtype.ext (Units.ext (hφ this))
  · have hz : ((z : Fˣ) : F) ^ N = 1 := (mem_rootsOfUnity' N _).1 z.2
    obtain ⟨w, hw⟩ := h _ hz
    have hw1 : w ^ N = 1 := hφ (by rw [map_pow, hw, hz, map_one])
    refine ⟨rootsOfUnity.mkOfPowEq w hw1, Subtype.ext (Units.ext ?_)⟩
    rw [restrictRootsOfUnity_coe_apply]
    exact hw

theorem card_hom_torsion (X W : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [CommRing W] (N : ℕ) :
    Nat.card (powMonoidHom N : (Multiplicative X →* Wˣ) →* _).ker =
      Nat.card (rootsOfUnity N W) ^ Module.finrank ℤ X := by
  rw [← card_hom_lattice]
  refine Nat.card_congr ⟨fun c => c.1.codRestrict _ fun x => ?_, fun c => ⟨(rootsOfUnity N W).subtype.comp c, ?_⟩,
    fun c => rfl, fun c => rfl⟩
  · exact DFunLike.congr_fun (MonoidHom.mem_ker.1 c.2) x
  · exact MonoidHom.mem_ker.2 (MonoidHom.ext fun x => (c x).2)

theorem card_torsion_ext {GW BF C : Type} [CommGroup GW] [Group BF] [CommGroup C] (N : ℕ) (τ : GW →* BF)
    (j : C →* GW) (hj : Function.Injective j) (hker : ∀ y, τ y = 1 ↔ ∃ c, y = j c)
    (hs : ∀ x, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ τ y = x) :
    Nat.card (powMonoidHom N : GW →* GW).ker =
      Nat.card (powMonoidHom N : C →* C).ker * Nat.card {x : BF // x ^ N = 1} := by
  let f := τ.comp (powMonoidHom N : GW →* GW).ker.subtype
  have h1 : Nat.card f.ker * Nat.card f.range = Nat.card (powMonoidHom N : GW →* GW).ker := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [← h1]
  congr 1
  · symm
    refine Nat.card_congr (Equiv.ofBijective (fun c => ⟨⟨j c.1, ?_⟩, (hker _).2 ⟨c.1, rfl⟩⟩) ⟨fun a b e => ?_, fun y => ?_⟩)
    · show j c.1 ^ N = 1
      rw [← map_pow]
      exact (congrArg j c.2).trans (map_one j)
    · exact Subtype.ext (hj (congrArg (fun u => u.1.1) e))
    · obtain ⟨c, hc⟩ := (hker y.1.1).1 y.2
      refine ⟨⟨c, hj ?_⟩, Subtype.ext (Subtype.ext hc.symm)⟩
      show j (c ^ N) = _
      rw [map_pow, ← hc, map_one]
      exact y.1.2
  · refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ⟨?_, fun hx => ?_⟩)
    · rintro ⟨y, rfl⟩
      show τ y.1 ^ N = 1
      rw [← map_pow]
      exact (congrArg τ y.2).trans (map_one τ)
    · obtain ⟨y, hy, e⟩ := hs x hx
      exact ⟨⟨y, hy⟩, e⟩

theorem eq_one_of_cubWeil_one {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}
    {c : CubicalStr G L} {N : ℕ} {T : Over S} {y : T ⟶ G} {ζ} (h : CubWeil c N 1 y ζ) : ζ = 1 := by
  have h2 := (GlobalTheory.UU.cubWeil_basic S G L c N T).2.1 1 1 y ζ ζ h h
  rw [_root_.mul_one] at h2
  exact mul_eq_left.1 (h2.unique h)

end GlobalTheory.UU.NondegGen

open GlobalTheory.UU.NondegGen in

theorem GlobalTheory.UU.cubWeil_nondegenerate_generic :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun {V} _ _ _ {_} {_} _ _ s => ∀ (t : Tower s) (a : t.Alg) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (N : ℕ), 1 ≤ N → ∀ x : TF (R := V) F ⟶ a.B, x ^ N = 1 → (∀ y : TF (R := V) F ⟶ a.B, y ^ N = 1 → CubWeil a.M.c N x y 1) → x = 1 := by
  intro hcard hL V _ _ _ A G _ _ s t a F _ _ _ _ N hN x hx horth
  obtain ⟨W, _, _, _, φ, hφ, hcomp, hW, hloc, hroots, hlift⟩ := GlobalTheory.T.torsion_lift_abelianPart_finite_extension hcard V A G s t a F N hN
  haveI : CharZero V := s.cdvr.2.2
  haveI : CharZero F := charZero_of_injective_ringHom
    (f := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)))
    ((algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _))
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  haveI := s.semi.separated
  haveI := a.isAb.proper
  let SW : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))
  let σ : TF (R := V) F ⟶ SW := Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
    show Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomp])
  choose ρf hρ hρu using fun y : SW ⟶ G => GlobalTheory.T.existsUnique_abelianPart_image_adicComplete_point V A G s t a W hW hloc y
  let ρ : (SW ⟶ G) →* (SW ⟶ a.B) := MonoidHom.mk' ρf fun y y' =>
    (hρu _ _ ((GlobalTheory.T.abelianPart_image_one_mul_inv V A G s t a W y y' (ρf y) (ρf y')).2 (hρ y) (hρ y')).1).symm
  obtain ⟨ι', hι, hιs⟩ := GlobalTheory.T.exists_formalTorus_points_semiAbelian_model V A G s t W hW hloc
  let pG : (SW ⟶ G) →* (TF (R := V) F ⟶ G) := preHom σ
  let pB : (SW ⟶ a.B) →* (TF (R := V) F ⟶ a.B) := preHom σ
  have hpG : Function.Injective pG := fun y y' e =>
    GlobalTheory.over_points_ext_of_injective _ G W F φ hφ _ y y' (congrArg (fun q => q.left) e)
  have hpB : Function.Injective pB := fun y y' e =>
    GlobalTheory.over_points_ext_of_injective _ a.B W F φ hφ _ y y' (congrArg (fun q => q.left) e)
  let τ := pB.comp ρ
  have hker : ∀ y, τ y = 1 ↔ ∃ c, y = ι' c := fun y => by
    have e1 : τ y = 1 ↔ ρ y = 1 := map_eq_one_iff pB hpB
    have e2 := GlobalTheory.T.abelianPart_image_eq_one_iff_torus_point V A G s t a W hW hloc y
    rw [e1]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := e2.1 (by have := hρ y; rw [show ρf y = 1 from h] at this; exact this)
      exact ⟨c, (hιs y c).2 hc⟩
    · rintro ⟨c, hc⟩
      exact (hρu y 1 (e2.2 ⟨c, (hιs y c).1 hc⟩)).symm
  have hs : ∀ x : TF (R := V) F ⟶ a.B, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ τ y = x := fun x hx => by
    obtain ⟨y, b, hy, hb, e⟩ := hlift x hx
    refine ⟨y, hy, ?_⟩
    have : ρ y = b := (hρu y b hb).symm
    show pB (ρ y) = x
    rw [this]
    exact Over.OverMorphism.ext e
  obtain ⟨g', hg'⟩ := GlobalTheory.AbelianDim.exists_relDim V a.B a.isAb
  have hdim := (GlobalTheory.T.dim_eq_abelianPart_dim_add_torus_rank V A G s t g').2 a hg'
  have hB : Nat.card {x : TF (R := V) F ⟶ a.B // x ^ N = 1} = N ^ (2 * g') :=
    GlobalTheory.card_torsion_geometricPoint_of_field hcard _ a.B a.isAb g' hg' F _ N hNF
  have hC := card_hom_torsion s.X W N
  rw [card_roots W F φ hφ N hNF hroots] at hC
  have hH := card_torsion_ext N τ ι' hι hker hs
  rw [hC, hB] at hH
  have hρN : ∀ y : SW ⟶ G, y ^ N = 1 → ρ y ^ N = 1 := fun y hy => by rw [← map_pow, hy, map_one]

  have hpair : ∀ y y' : SW ⟶ G, y ^ N = 1 → y' ^ N = 1 → CubWeil a.M.c N (τ y) (τ y') 1 →
      CubWeil s.P.c N (pG y) (pG y') 1 := fun y y' hy hy' h => by
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil s.P.c hy hy'
    have h1 := (GlobalTheory.T.cubicalWeilPairing_eq_abelianPart_image V A G s t a W hW hloc N y y' (ρ y) (ρ y') ζ (hρ y) (hρ y') (hρN y hy) (hρN y' hy') hζ).comp σ
    have h2 := hζ.comp σ
    rw [h1.unique h] at h2
    exact h2
  have hτN : ∀ y : SW ⟶ G, y ^ N = 1 → τ y ^ N = 1 := fun y hy => by rw [← map_pow, hy, map_one]
  obtain ⟨y, hy, rfl⟩ := hs x hx
  have hmem := GlobalTheory.UU.mem_of_cubWeil_orthogonal hL V A G s F N hN
    ((powMonoidHom N : (Multiplicative s.X →* Wˣ) →* _).ker.map (pG.comp ι'))
    ((powMonoidHom N : (SW ⟶ G) →* _).ker.map pG) ?_ ?_ ?_ ?_ (pG y) (by rw [← map_pow, hy, map_one]) ?_
  · obtain ⟨c, -, hc⟩ := hmem
    exact (hker y).2 ⟨c, (hpG hc).symm⟩
  · rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow]
    exact (congrArg _ hc).trans (map_one _)
  · rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow]
    exact (congrArg _ hc).trans (map_one _)
  · rw [Subgroup.card_map_of_injective (f := pG.comp ι') (hpG.comp hι), Subgroup.card_map_of_injective hpG, hH, hC, hdim]
    ring
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨y', hy', rfl⟩
    have hcN : ι' c ^ N = 1 := by
      rw [← map_pow]
      exact (congrArg _ hc).trans (map_one _)
    refine hpair (ι' c) y' hcN hy' ?_
    rw [(hker _).2 ⟨c, rfl⟩]
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil a.M.c (one_pow N) (hτN y' hy')
    rwa [eq_one_of_cubWeil_one hζ] at hζ
  · rintro _ ⟨y', hy', rfl⟩
    exact hpair y y' hy hy' (horth _ (hτN y' hy'))
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.Principal

theorem finite_points {S : Scheme.{0}} (H : Over S) [IsFinite H.hom] {K : Type} [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ S) : Finite (Over.mk t ⟶ H) := by
  have hfin := ((pullback.snd H.hom t).finite_preimage_singleton (IsLocalRing.closedPoint K)).to_subtype
  let σ : (Over.mk t ⟶ H) → (Spec (CommRingCat.of K) ⟶ pullback H.hom t) := fun x =>
    pullback.lift x.left (𝟙 _) ((Over.w x).trans (Category.id_comp _).symm)
  have h₁ : ∀ x, σ x ≫ pullback.fst H.hom t = x.left := fun x => pullback.lift_fst _ _ _
  have h₂ : ∀ x, σ x ≫ pullback.snd H.hom t = 𝟙 _ := fun x => pullback.lift_snd _ _ _
  refine Finite.of_injective (fun x => (⟨σ x (IsLocalRing.closedPoint K),
    Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _⟩ :
      (pullback.snd H.hom t) ⁻¹' {IsLocalRing.closedPoint K})) fun a b hab => ?_
  have e : σ a = σ b :=
    ext_of_apply_closedPoint_eq (K := K) (pullback.snd H.hom t) (h₂ a) (h₂ b) (congrArg Subtype.val hab)
  exact Over.OverMorphism.ext ((h₁ a).symm.trans (e ▸ h₁ b))

theorem exists_pow_eq_one (hG : GlobalFnsSt) {R : Type} [CommRing R] {B : Over (Spec (CommRingCat.of R))} [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) {L : LB B.left} (hLB : L.IsLB) (hL : RelAmple B L)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (x : Over.mk t ⟶ B) (hx : InK B L x) : ∃ N : ℕ, 1 ≤ N ∧ x ^ N = 1 := by
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hLB).1 hL
  have hP : IsProjBy B.hom := ⟨_, isLB_pw hLB _, n, s, hs⟩
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L hLB
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG R B hB hP L (pw L 0) hLB hO
  have hfin : IsFinite H.hom :=
    GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG R B hB L (pw L 0) hLB hO hL H j hj hH
  have hrep : ∀ x : Over.mk t ⟶ B, InK B L x ↔ ∃ y : Over.mk t ⟶ H, y ≫ j = x :=
    fun x => (hK _ rfl _ x).trans (hH _ x)
  have := finite_points H t
  have : Finite (kSubgroup B hLB (Over.mk t)) :=
    Finite.of_surjective (fun y : Over.mk t ⟶ H => (⟨y ≫ j, (hrep _).2 ⟨y, rfl⟩⟩ : kSubgroup B hLB (Over.mk t)))
      fun z => ((hrep z.1).1 z.2).imp fun _ h => Subtype.ext h
  exact ⟨Nat.card (kSubgroup B hLB (Over.mk t)), Nat.card_pos,
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : kSubgroup B hLB (Over.mk t))))⟩

theorem exists_gen_of_inK {S : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} (hLB : L.IsLB)
    {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk t ⟶ B) (hx : InK B L x) :
    ∃ u : LB.Gen (translDiff B L x), u.IsGen := by
  obtain ⟨V, hpV, c, hc⟩ := hx (IsLocalRing.closedPoint K)
  refine GlobalTheory.TwistTranslate.gen_of_pull_top hLB _ (fun z => ?_) c hc
  have e : ∀ p q : Spec (CommRingCat.of K), p = q := fun p q => Subsingleton.elim p q
  change (fst (Over.mk t) B).left z ∈ V
  rw [e ((fst (Over.mk t) B).left z) (IsLocalRing.closedPoint K)]
  exact hpV

theorem kTriv_alg : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L := by
  intro hc laws V _ _ _ A G _ _ s t a
  have hdvr : IsDiscreteValuationRing V := s.cdvr.1
  have hchar : CharZero V := s.cdvr.2.2
  refine GlobalTheory.KTrivGeneric.kTriv_of_generic laws.globalFns V a.B a.isAb a.M.L a.M.c a.ample fun x hx => ?_
  obtain ⟨N, hN, hxN⟩ := exists_pow_eq_one laws.globalFns a.isAb a.M.L.isLB a.ample _ x hx
  exact GlobalTheory.UU.cubWeil_nondegenerate_generic hc laws V A G s t a (AlgebraicClosure (FractionRing V)) N hN x hxN fun y hy =>
    GlobalTheory.UU.KerPair.cubWeil_of_gen laws.globalFns _ a.B a.isAb a.M.L a.M.c N _ x y hxN hy
      (exists_gen_of_inK a.M.L.isLB _ x hx)

end GlobalTheory.UU.Principal
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kTriv_torusQuotientTower_algebraisation : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L := by
  atlas_forward_decl GlobalTheory.UU.Principal.kTriv_alg
end
