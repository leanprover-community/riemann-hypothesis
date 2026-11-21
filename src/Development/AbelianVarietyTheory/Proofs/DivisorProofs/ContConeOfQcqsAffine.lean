import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfEtaleCohomologyEquivalenceDiagramStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousCofilteredAffineLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackSchBc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfEtaleCohomologyEquivalenceDiagram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCohomologyContinuousOnConeOfLevelwiseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSurjectiveCechDescentCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCechNerveAugmentationIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contCone_of_whisker : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (I' : Type) [SmallCategory I'] [IsCofiltered I'] (L : I' ⥤ I) (G : I ⥤ Spc) (c : Cone G), (∀ i, ∃ i', Nonempty (L.obj i' ⟶ i)) → ContCone R F (c.whisker L) → ContCone R F c := by
  intro R _ F I _ _ I' _ _ L G c hL hc n
  obtain ⟨h1, h2⟩ := hc n
  refine ⟨fun x => ?_, fun i y hy => ?_⟩
  · obtain ⟨i', y, hy⟩ := h1 x
    exact ⟨L.obj i', y, hy⟩
  · obtain ⟨i', ⟨f⟩⟩ := hL i
    have hy' : pull R ((c.whisker L).π.app i') F n (pull R (G.map f) F n y) = 0 := by
      change pull R (c.π.app (L.obj i')) F n (pull R (G.map f) F n y) = 0
      rw [← pull_comp, c.w f]
      exact hy
    obtain ⟨k', g, hg⟩ := h2 i' _ hy'
    refine ⟨L.obj k', L.map g ≫ f, ?_⟩
    rw [Functor.map_comp, pull_comp]
    exact hg

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologyContinuousOnCone_of_whisker : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (I' : Type) [SmallCategory I'] [IsCofiltered I'] (L : I' ⥤ I) (G : I ⥤ Spc) (c : Cone G), (∀ i, ∃ i', Nonempty (L.obj i' ⟶ i)) → ContCone R F (c.whisker L) → ContCone R F c := by
  first | (exact @GlobalTheory.EtC.contCone_of_whisker) | (exact GlobalTheory.EtC.contCone_of_whisker) | (intros; apply GlobalTheory.EtC.contCone_of_whisker  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem exists_affine_etale_surjective :
    ∀ (W : Scheme.{0}) [CompactSpace W], ∃ (V : Scheme.{0}) (f : V ⟶ W), IsAffine V ∧ Etale f ∧ Surjective f := by
  intro W _
  let 𝒰 := W.affineCover.finiteSubcover
  refine ⟨∐ 𝒰.X, Sigma.desc 𝒰.f, inferInstance, ?_, inferInstance⟩
  have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ ↦ inferInstance

end GlobalTheory
end

section
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

private theorem eqv_of_isIso' (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (f : E ⟶ E') [IsIso f] : Eqv R f F := by
  intro n
  refine ⟨fun x y hxy => ?_, fun x => ⟨pull R (inv f) F n x, ?_⟩⟩
  · have hx := pull_comp R (inv f) f F n x
    have hy := pull_comp R (inv f) f F n y
    rw [IsIso.inv_hom_id, pull_id] at hx hy
    rw [hx, hy, hxy]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem contCone_bc_affine : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffineHom (G.obj i).hom) → ∀ (W : Scheme.{0}) (r : W ⟶ S), IsAffine W → ContCone R F ((bc (sch.map r)).mapCone c) := by
  intro R _ F hF S I _ _ G c hc hG W r hW
  haveI : IsConnected I := IsCofiltered.isConnected I
  obtain ⟨e, -⟩ := bc_sch_iso S W r
  let P : Over S ⥤ Scheme.{0} := Over.pullback r ⋙ Over.forget W
  have hlim : IsLimit (P.mapCone c) := isLimitOfPreserves P hc
  have haff : ∀ i, IsAffine ((G ⋙ P).obj i) := by
    intro i
    change IsAffine (pullback (G.obj i).hom r)
    haveI := hG i
    exact isAffine_of_isAffineHom (pullback.snd (G.obj i).hom r)
  have h1 : ContCone R F (sch.mapCone (P.mapCone c)) := GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit R F hF I (G ⋙ P) (P.mapCone c) hlim haff
  let α : (G ⋙ P) ⋙ sch ⟶ G ⋙ bc (sch.map r) :=
    { app := fun i => e.hom.app (G.obj i)
      naturality := fun i j f => e.hom.naturality (G.map f) }
  refine (ContCone.iff_of_eqv R F I _ _ (sch.mapCone (P.mapCone c)) ((bc (sch.map r)).mapCone c) α (e.hom.app c.pt)
    (fun i => e.hom.naturality (c.π.app i)) (fun i => eqv_of_isIso' R F _) (eqv_of_isIso' R F _)).1 h1

end GlobalTheory.EtC
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuity_baseChange_affine_cofiltered_limit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffineHom (G.obj i).hom) → ∀ (W : Scheme.{0}) (r : W ⟶ S), IsAffine W → ContCone R F ((bc (sch.map r)).mapCone c) := by
  atlas_forward_decl GlobalTheory.EtC.contCone_bc_affine
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.BcLevel

def bcIsoOfIso {E E' : Spc} {S : Scheme.{0}} (α : E ≅ E') (p : E' ⟶ sch.obj S) : bc (α.hom ≫ p) ≅ bc p :=
  haveI : ∀ U, IsIso ((bcMap α.hom p).app U) := fun U => by
    dsimp only [bcMap]; exact pullback.map_isIso _ _ _ _ _ _ _ _ _
  haveI : IsIso (bcMap α.hom p) := NatIso.isIso_of_isIso_app _
  asIso (bcMap α.hom p)

def dq {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) : disc.obj (E.obj k) ⟶ sch.obj S :=
  disc.map (p.app k)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.BcLevel.isPullback_lv {E : _root_.GlobalTheory.EtC.Spc} {S : Scheme.{0}}
    (p : E ⟶ _root_.GlobalTheory.EtC.sch.obj S) (k : SimplexCategoryᵒᵖ) (U : Over S) :
    IsPullback (_root_.GlobalTheory.EtC.disc.map ((pullback.fst p (_root_.GlobalTheory.EtC.sch.map U.hom)).app k) : _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).obj k) ⟶ _root_.GlobalTheory.EtC.disc.obj (E.obj k))
      (_root_.GlobalTheory.EtC.disc.map ((pullback.snd p (_root_.GlobalTheory.EtC.sch.map U.hom)).app k) : _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).obj k) ⟶ _root_.GlobalTheory.EtC.sch.obj U.left)
      (_root_.GlobalTheory.EtC.BcLevel.dq p k) (_root_.GlobalTheory.EtC.sch.map U.hom) := by
  have h := (IsPullback.of_hasPullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).map
    ((evaluation SimplexCategoryᵒᵖ _root_.GlobalTheory.EtC.PSh).obj k)
  exact h.map _root_.GlobalTheory.EtC.disc

def lvIso {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) (U : Over S) :
    disc.obj ((pullback p (sch.map U.hom)).obj k) ≅ pullback (dq p k) (sch.map U.hom) :=
  (isPullback_lv p k U).isoPullback

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.BcLevel.lv_nat {E : _root_.GlobalTheory.EtC.Spc} {S : Scheme.{0}}
    (p : E ⟶ _root_.GlobalTheory.EtC.sch.obj S) (k : SimplexCategoryᵒᵖ) {U V : Over S} (g : U ⟶ V) :
    (_root_.GlobalTheory.EtC.disc.map (((_root_.GlobalTheory.EtC.bc p).map g).app k) : _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).obj k) ⟶ _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map V.hom)).obj k)) ≫
      (_root_.GlobalTheory.EtC.BcLevel.lvIso p k V).hom = (_root_.GlobalTheory.EtC.BcLevel.lvIso p k U).hom ≫ (_root_.GlobalTheory.EtC.bc (_root_.GlobalTheory.EtC.BcLevel.dq p k)).map g := by
  have hV₁ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k V).isoPullback_hom_fst
  have hV₂ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k V).isoPullback_hom_snd
  have hU₁ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k U).isoPullback_hom_fst
  have hU₂ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k U).isoPullback_hom_snd
  unfold _root_.GlobalTheory.EtC.BcLevel.lvIso
  dsimp only [_root_.GlobalTheory.EtC.bc]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]
    erw [hV₁, pullback.lift_fst, Category.comp_id, hU₁]
    rw [← Functor.map_comp, ← NatTrans.comp_app, pullback.lift_fst, Category.comp_id]
  · rw [Category.assoc, Category.assoc]
    erw [hV₂, pullback.lift_snd, ← Category.assoc, hU₂]
    change _ = _root_.GlobalTheory.EtC.disc.map _ ≫
      _root_.GlobalTheory.EtC.disc.map ((_root_.GlobalTheory.EtC.sch.map g.left).app k)
    rw [← Functor.map_comp]
    erw [← Functor.map_comp]
    congr 1
    rw [← NatTrans.comp_app]
    erw [← NatTrans.comp_app, pullback.lift_snd]

def bcDiscIso {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) :
    bc p ⋙ (evaluation _ PSh).obj k ⋙ disc ≅ bc (dq p k) :=
  NatIso.ofComponents (lvIso p k) (fun g => lv_nat p k g)

theorem bc_level : ∀ (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) (X : Scheme.{0}) (r : X ⟶ S)
    (e : yoneda.obj X ≅ E.obj k), e.hom ≫ p.app k = yoneda.map r →
    Nonempty (bc (sch.map r) ≅ bc p ⋙ (evaluation _ PSh).obj k ⋙ disc) := by
  intro S E p k X r e h
  have heq : sch.map r = (disc.mapIso e : sch.obj X ≅ disc.obj (E.obj k)).hom ≫ dq p k := by
    change disc.map (yoneda.map r) = disc.map e.hom ≫ disc.map (p.app k)
    rw [← h]
    exact disc.map_comp _ _
  rw [heq]
  exact ⟨bcIsoOfIso _ (dq p k) ≪≫ (bcDiscIso p k).symm⟩

end GlobalTheory.EtC.BcLevel
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.CcStep

theorem cc_step : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), (∀ k : SimplexCategoryᵒᵖ, ∃ (X : Scheme.{0}) (r : X ⟶ S) (e : yoneda.obj X ≅ E.obj k), e.hom ≫ p.app k = yoneda.map r ∧ ContCone R F ((bc (sch.map r)).mapCone c)) → ContCone R F ((bc p).mapCone c) := by
  intro R _ F S E p I _ _ G c h
  apply GlobalTheory.T.isCohomologyContinuousOnCone_of_levelwise R F I (G ⋙ bc p) ((bc p).mapCone c)
  intro k
  obtain ⟨X, r, e, he, hc⟩ := h k
  obtain ⟨φ⟩ := GlobalTheory.EtC.BcLevel.bc_level S E p k X r e he
  have hiso := (GlobalTheory.EtC.eqv_basic R F).1
  refine (GlobalTheory.EtC.ContCone.iff_of_eqv R F I (G ⋙ bc (sch.map r)) ((G ⋙ bc p) ⋙ (evaluation _ PSh).obj k ⋙ disc)
    ((bc (sch.map r)).mapCone c) (((evaluation _ PSh).obj k ⋙ disc).mapCone ((bc p).mapCone c))
    (Functor.whiskerLeft G φ.hom) (φ.hom.app c.pt) ?_ ?_ ?_).1 hc
  · intro i
    exact φ.hom.naturality (c.π.app i)
  · intro i
    exact hiso _ _ _ inferInstance
  · exact hiso _ _ _ inferInstance

end GlobalTheory.EtC.CcStep
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologyContinuous_base_change_of_levels : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), (∀ k : SimplexCategoryᵒᵖ, ∃ (X : Scheme.{0}) (r : X ⟶ S) (e : yoneda.obj X ≅ E.obj k), e.hom ≫ p.app k = yoneda.map r ∧ ContCone R F ((bc (sch.map r)).mapCone c)) → ContCone R F ((bc p).mapCone c) := by
  first | (exact @GlobalTheory.EtC.CcStep.cc_step) | (exact GlobalTheory.EtC.CcStep.cc_step) | (intros; apply GlobalTheory.EtC.CcStep.cc_step <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem bc_cechAug_eqv : ∀ (R : Type) [CommRing R] (F : Shv R) (S W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W),
    Etale f → Surjective f → ∀ U : Over S, Eqv R ((bcMap (cechAug f) (sch.map r)).app U) F := by
  intro R _ F S W V r f hE hS U
  obtain ⟨e₁, e₂, he⟩ := bc_cechAug_iso S W V r f U
  have hE' : Etale (pullback.snd f (pullback.fst r U.hom)) := inferInstance
  have hS' : Surjective (pullback.snd f (pullback.fst r U.hom)) := inferInstance
  have hA : Eqv R (cechAug (pullback.snd f (pullback.fst r U.hom))) F :=
    smooth_surjective_cech_descent_cohomology R (pullback.snd f (pullback.fst r U.hom)) F
  obtain ⟨hiso, hcomp, -, -⟩ := eqv_basic R F
  have h1 : Eqv R e₁.hom F := hiso _ _ _ inferInstance
  have h2 : Eqv R e₂.hom F := hiso _ _ _ inferInstance
  have h3 : Eqv R (e₁.hom ≫ (bcMap (cechAug f) (sch.map r)).app U) F := by
    rw [he]; exact (hcomp _ _ _ _ _).1 hA h2
  exact (hcomp _ _ _ _ _).2.1 h1 h3

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomologyEquivalence_baseChange_cechAugmentation : ∀ (R : Type) [CommRing R] (F : Shv R) (S W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W), Etale f → Surjective f → ∀ U : Over S, Eqv R ((bcMap (cechAug f) (sch.map r)).app U) F := by
  first | (exact @GlobalTheory.EtC.bc_cechAug_eqv) | (exact GlobalTheory.EtC.bc_cechAug_eqv) | (intros; apply GlobalTheory.EtC.bc_cechAug_eqv  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contCone_of_etale_surjective : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G) (W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W), Etale f → Surjective f → ∀ (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative], P f → (∀ (Z : Scheme.{0}) (π : Z ⟶ V), P π → ContCone R F ((bc (sch.map (π ≫ f ≫ r))).mapCone c)) → ContCone R F ((bc (sch.map r)).mapCone c) := by
  intro R _ F S I _ _ G c W V r f hE hS P _ _ hf hZ
  have hstep : ContCone R F ((bc (cechAug f ≫ sch.map r)).mapCone c) := by
    refine GlobalTheory.T.cohomologyContinuous_base_change_of_levels R F S (cech f) (cechAug f ≫ sch.map r) I G c (fun k => ?_)
    obtain ⟨Z, π, e, hP, he⟩ := GlobalTheory.EtC.cech_level_representable P V W f hf k
    refine ⟨Z, π ≫ f ≫ r, e, ?_, hZ Z π hP⟩
    rw [NatTrans.comp_app, ← Category.assoc, he]
    change yoneda.map (π ≫ f) ≫ yoneda.map r = _
    rw [← yoneda.map_comp, Category.assoc]
  refine (ContCone.iff_of_eqv R F I _ _ ((bc (cechAug f ≫ sch.map r)).mapCone c) ((bc (sch.map r)).mapCone c)
    (Functor.whiskerLeft G (bcMap (cechAug f) (sch.map r))) ((bcMap (cechAug f) (sch.map r)).app c.pt) (fun i => ?_)
    (fun i => GlobalTheory.T.etaleCohomologyEquivalence_baseChange_cechAugmentation R F S W V r f hE hS (G.obj i)) (GlobalTheory.T.etaleCohomologyEquivalence_baseChange_cechAugmentation R F S W V r f hE hS c.pt)).mp hstep
  exact ((bcMap (cechAug f) (sch.map r)).naturality (c.π.app i))

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousCone_descends_etale_surjective : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G) (W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W), Etale f → Surjective f → ∀ (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative], P f → (∀ (Z : Scheme.{0}) (π : Z ⟶ V), P π → ContCone R F ((bc (sch.map (π ≫ f ≫ r))).mapCone c)) → ContCone R F ((bc (sch.map r)).mapCone c) := by
  first | (exact @GlobalTheory.EtC.contCone_of_etale_surjective) | (exact GlobalTheory.EtC.contCone_of_etale_surjective) | (intros; apply GlobalTheory.EtC.contCone_of_etale_surjective <;> assumption)
end

section
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem contCone_bc_of_compact_separated (R : Type) [CommRing R] (F : Shv R) (hF : Finitary F)
    (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G)
    (hc : IsLimit c) (hG : ∀ i, IsAffineHom (G.obj i).hom) (W : Scheme.{0}) (r : W ⟶ S)
    [CompactSpace W] [W.IsSeparated] : ContCone R F ((bc (sch.map r)).mapCone c) := by
  obtain ⟨V, f, hV, hfe, hfs⟩ := GlobalTheory.exists_affine_etale_surjective W
  have hfa : IsAffineHom f := by
    have : IsAffineHom (f ≫ terminal.from W) := isAffineHom_of_isAffine _
    exact IsAffineHom.of_comp f (terminal.from W)
  refine GlobalTheory.T.continuousCone_descends_etale_surjective R F S I G c W V r f hfe hfs @IsAffineHom hfa ?_
  intro Z π hπ
  have : IsAffine Z := isAffine_of_isAffineHom π
  exact GlobalTheory.T.continuity_baseChange_affine_cofiltered_limit R F hF S I G c hc hG Z (π ≫ f ≫ r) inferInstance

theorem contCone_bc_of_qcqs : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffineHom (G.obj i).hom) → ∀ (W : Scheme.{0}) (r : W ⟶ S) [CompactSpace W] [QuasiSeparatedSpace W], ContCone R F ((bc (sch.map r)).mapCone c) := by
  intro R _ F hF S I _ _ G c hc hG W r _ _
  obtain ⟨V, f, hV, hfe, hfs⟩ := GlobalTheory.exists_affine_etale_surjective W
  have hqc : QuasiCompact f := inferInstance
  have hsep : IsSeparated f := by
    have : IsSeparated (f ≫ terminal.from W) := by
      rw [Subsingleton.elim (f ≫ terminal.from W) (terminal.from V)]; infer_instance
    exact IsSeparated.of_comp f (terminal.from W)
  haveI : (@QuasiCompact ⊓ @IsSeparated : MorphismProperty Scheme.{0}).IsStableUnderBaseChange :=
    MorphismProperty.IsStableUnderBaseChange.inf
  haveI : (@QuasiCompact ⊓ @IsSeparated : MorphismProperty Scheme.{0}).IsMultiplicative :=
    { id_mem := fun X => ⟨inferInstance, inferInstance⟩
      comp_mem := fun f g hf hg => by
        obtain ⟨hf1, hf2⟩ := hf
        obtain ⟨hg1, hg2⟩ := hg
        exact ⟨inferInstance, inferInstance⟩ }
  refine GlobalTheory.T.continuousCone_descends_etale_surjective R F S I G c W V r f hfe hfs (@QuasiCompact ⊓ @IsSeparated) ⟨hqc, hsep⟩ ?_
  intro Z π hπ
  obtain ⟨h1, h2⟩ := hπ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace π
  have : Z.IsSeparated := by
    constructor
    rw [Subsingleton.elim (terminal.from Z) (π ≫ terminal.from V)]; infer_instance
  exact contCone_bc_of_compact_separated R F hF S I G c hc hG Z (π ≫ f ≫ r)

end GlobalTheory
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologyContinuous_baseChange_qcqs : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffineHom (G.obj i).hom) → ∀ (W : Scheme.{0}) (r : W ⟶ S) [CompactSpace W] [QuasiSeparatedSpace W], ContCone R F ((bc (sch.map r)).mapCone c) := by
  atlas_forward_decl GlobalTheory.contCone_bc_of_qcqs
end

section
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contCone_of_qcqs_affine : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, CompactSpace (G.obj i)) → (∀ i, QuasiSeparatedSpace (G.obj i)) → (∀ (i j : I) (f : i ⟶ j), IsAffineHom (G.map f)) → ContCone R F (sch.mapCone c) := by
  intro R _ F hF I _ _ G c hc hcp hqs haff
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have hc' : IsLimit ((Over.conePost G i₀).obj c) := Over.isLimitConePost i₀ hc
  haveI := hcp i₀
  haveI := hqs i₀
  have hcore := GlobalTheory.T.cohomologyContinuous_baseChange_qcqs R F hF (G.obj i₀) (Over i₀) (Over.post G) ((Over.conePost G i₀).obj c) hc'
    (fun j => haff _ _ j.hom) (G.obj i₀) (𝟙 _)
  have hb := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  haveI : IsIso (sch.map (𝟙 (G.obj i₀))) := inferInstance
  apply GlobalTheory.T.cohomologyContinuousOnCone_of_whisker R F I (Over i₀) (Over.forget i₀) (G ⋙ sch) (sch.mapCone c)
  · intro i
    exact ⟨Over.mk (IsCofiltered.minToRight i i₀), ⟨IsCofiltered.minToLeft i i₀⟩⟩
  · let α : Over.post G ⋙ bc (sch.map (𝟙 (G.obj i₀))) ⟶ Over.forget i₀ ⋙ G ⋙ sch :=
      { app := fun j => pullback.snd _ _
        naturality := fun j k f => by
          simp only [Functor.comp_map, bc, pullback.map]
          erw [pullback.lift_snd]
          rfl }
    refine (GlobalTheory.T.of_etaleCohomologyEquivalence_diagram R F (Over i₀) _ _ ((bc (sch.map (𝟙 (G.obj i₀)))).mapCone ((Over.conePost G i₀).obj c))
      ((sch.mapCone c).whisker (Over.forget i₀)) α (pullback.snd _ _) ?_ ?_ ?_).1 hcore
    · intro j
      simp only [Functor.mapCone_π_app, Cone.whisker_π, bc, pullback.map]
      erw [pullback.lift_snd]
      rfl
    · intro j
      exact hb.1 _ _ _ (pullback_snd_iso_of_left_iso _ _)
    · exact hb.1 _ _ _ (pullback_snd_iso_of_left_iso _ _)
end GlobalTheory.EtC
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contCone_of_isLimit_of_qcqs_affine_transitions : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, CompactSpace (G.obj i)) → (∀ i, QuasiSeparatedSpace (G.obj i)) → (∀ (i j : I) (f : i ⟶ j), IsAffineHom (G.map f)) → ContCone R F (sch.mapCone c) := by
  atlas_forward_decl GlobalTheory.EtC.contCone_of_qcqs_affine
end
