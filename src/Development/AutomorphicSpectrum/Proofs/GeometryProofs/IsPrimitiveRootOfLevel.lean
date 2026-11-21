import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptGoodReductionDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptProjectiveModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLabelBases
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelCoverStHolds

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeExists

theorem coordTie_reindex {o : Type} [CommRing o] {X : Scheme.{0}} {Ω : Type} [Field Ω] [Algebra o Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ κ' : Type} {x : κ → Ω} (h : CoordTie o ξ x) (e : κ' → κ)
    (he : Function.Surjective e) (x' : κ' → Ω) (hx : ∀ c, x' c = x (e c)) : CoordTie o ξ x' := by
  obtain rfl : x' = fun c => x (e c) := funext hx
  have hc : ∀ c p, InChart ξ (fun c => x (e c)) c p ↔ InChart ξ x (e c) p := fun c p =>
    and_congr Iff.rfl (he.forall (p := fun c' => x c' / x (e c) ∈ regAt ξ p)).symm
  refine ⟨h.gen, fun p => ?_, fun c h0 => ?_, fun c h0 a => ?_⟩
  · obtain ⟨c, hp⟩ := h.cover p
    obtain ⟨c, rfl⟩ := he c
    exact ⟨c, (hc c p).2 hp⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) h0
    exact ⟨U, hU, fun q => (hq q).trans (exists_congr fun _ => (hc c _).symm)⟩
  · have : (Set.range fun j => x (e j) / x (e c)) = Set.range fun j => x j / x (e c) :=
      he.range_comp fun j => x j / x (e c)
    simpa only [hc, this] using h.ring (e c) h0 a

theorem exists_lift_torsion {S S' Z : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (b : Z ⟶ S') (a : Z ⟶ S) (hab : a = b ≫ f) (n : ℕ)
    (g : Over.mk a ⟶ G) (hg : g ^ n = 1) : ∃ g' : Over.mk b ⟶ G', g'.left ≫ φ = g.left ∧ g' ^ n = 1 := by
  subst hab
  let P : (Over.mk b ⟶ G') → (Over.mk (b ≫ f) ⟶ G) := fun x => Over.homMk (x.left ≫ φ) (by
    have := Over.w x
    simp only [Over.mk_hom] at this
    simp only [Category.assoc, Over.mk_hom, h.1.w]
    rw [← Category.assoc, this])
  have hP : ∀ x, (P x).left = x.left ≫ φ := fun _ => rfl
  let Φ : (Over.mk b ⟶ G') →* (Over.mk (b ≫ f) ⟶ G) := MonoidHom.mk' P fun x y =>
    Over.OverMorphism.ext ((hP _).trans (h.2 (Over.mk b) x y (P x) (P y) rfl rfl).symm)
  have hinj : Function.Injective Φ := fun x y hxy => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg CommaMorphism.left hxy) ((Over.w x).trans (Over.w y).symm))
  let g' : Over.mk b ⟶ G' := Over.homMk (h.1.lift g.left b (Over.w g)) (h.1.lift_snd _ _ _)
  have hg' : g'.left ≫ φ = g.left := h.1.lift_fst _ _ _
  refine ⟨g', hg', hinj ?_⟩
  have : Φ g' = g := Over.OverMorphism.ext hg'
  rw [map_pow, this, hg, map_one]

theorem fullTorsion_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ S'}
    {N n : ℕ} (hn : n ∣ N) (ht : FullTorsion G' ξ N) : FullTorsion G (ξ ≫ f) n := by
  intro k _ i g hg
  obtain ⟨g', e, hg'⟩ := exists_lift_torsion h (spMap i ≫ ξ) _ (Category.assoc _ _ _).symm n g hg
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨x, hx⟩ := ht k i g' (by rw [pow_mul, hg', one_pow])
  refine ⟨Over.homMk (x.left ≫ φ) ?_, ?_⟩
  · have := Over.w x
    simp only [Over.mk_hom] at this
    simp only [Category.assoc, Over.mk_hom, h.1.w]
    rw [← Category.assoc, this]
  · rw [← e, hx]
    exact Category.assoc _ _ _

theorem finite_of_dominates {X Y : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y} (hξ : IsCptGen ξ) (f : X ⟶ Y) [IsFinite f] {i : Ω₀ →+* Ω}
    (h : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) : i.Finite := by
  have h1 : LocallyQuasiFinite (Spec.map (Scheme.stalkClosedPointTo ξ)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).2
      (.of_finite (RingHom.Finite.of_surjective _ hξ.bij.2))
  have h2 : LocallyQuasiFinite ξ := by
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    infer_instance
  have h3 : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom i) ≫ ξ₀) := by
    rw [← h]
    infer_instance
  have h4 : i.QuasiFinite :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite) (φ := CommRingCat.ofHom i)).1
      (LocallyQuasiFinite.of_comp _ ξ₀)
  algebraize [i]
  exact .of_quasiFinite




end GlobalTheory.CompanionTheory.Ar.HodgeExists
