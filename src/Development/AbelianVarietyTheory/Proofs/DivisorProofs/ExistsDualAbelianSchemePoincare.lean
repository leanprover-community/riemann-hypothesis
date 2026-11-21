import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeOfSqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeNoetherianInduc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueOpenChartsAdditiveFamiliesRepresenting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesUniqueIso

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem Good.good_of_isPullback' {g : ℕ} {X Y X' Y' : Scheme.{0}} {k : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {h : Y' ⟶ Y} (sq : IsPullback k f' f h) (hf : Good g f) : Good g f' where
  proper := MorphismProperty.of_isPullback sq hf.proper
  smooth := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    exact MorphismProperty.of_isPullback sq hf.smooth
  conn := MorphismProperty.of_isPullback sq hf.conn

theorem HasRep.baseChange (S : Scheme.{0}) (A S' S'' : Over S) [GrpObj A] (g : ℕ) (h : S'' ⟶ S')
    (H : HasRep A g S') : HasRep A g S'' := by
  obtain ⟨B, b, P, hRep, hGood⟩ := H

  have sq := IsPullback.of_hasPullback b h
  refine ⟨pullback b h, pullback.snd b h, ev P (fst A (pullback b h)) (snd A (pullback b h) ≫ pullback.fst b h),
    GlobalTheory.T.rep_ev_of_isPullback S A B S' S'' (pullback b h) b P h _ _ hRep sq, ?_⟩

  exact Good.good_of_isPullback' (sq.map (Over.forget S)) hGood

end GlobalTheory.DualCon
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChangeBis : ∀ (S : Scheme.{0}) (A S' S'' : Over S) [GrpObj A] (g : ℕ) (_ : S'' ⟶ S'), HasRep A g S' → HasRep A g S'' := by
  atlas_forward_decl GlobalTheory.DualCon.HasRep.baseChange
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representsAdditiveLineBundleFamilies_unique_iso : ∀ (S : Scheme.{0}) (A B B' S' : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (b' : B' ⟶ S') (P' : LB (A ⊗ B').left), Rep A b P → Rep A b' P' → ∃ e : B ≅ B', e.hom ≫ b' = b ∧ Same A P P' (𝟙 B) e.hom := by
  first | exact @GlobalTheory.DualCon.rep_unique | exact GlobalTheory.DualCon.rep_unique | (intros; apply GlobalTheory.DualCon.rep_unique <;> assumption)
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ZarGlue

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem fam_pull {T Y : Over S} {N : LB (A ⊗ T).left} (hN : Fam A N) (y : Y ⟶ T) :
    Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have hL : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN.isLB _
  refine ⟨hL, (isAdditive_iff hL).2 fun Z a a' t => ?_⟩
  rw [evc_ev hN.isLB _ _ hL, evc_ev hN.isLB _ _ hL, evc_ev hN.isLB _ _ hL]
  simp only [lift_fst, lift_snd_assoc]
  exact (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)

omit [GrpObj A] in

theorem hom_open_eq (V : S.Opens) {Y : Over S} (u u' : Y ⟶ Over.mk V.ι) : u = u' := by
  apply Over.OverMorphism.ext
  have h : u.left ≫ V.ι = u'.left ≫ V.ι := (Over.w u).trans (Over.w u').symm
  exact (cancel_mono V.ι).1 h

omit [GrpObj A] in

theorem exists_hom_open (V : S.Opens) (Y : Over S) (h : ∀ z, Y.hom z ∈ V) : Nonempty (Y ⟶ Over.mk V.ι) := by
  refine ⟨Over.homMk (IsOpenImmersion.lift V.ι Y.hom ?_) (IsOpenImmersion.lift_fac _ _ _)⟩
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact h z

theorem isChart_of_rep (V : S.Opens) {B : Over S} (b : B ⟶ Over.mk V.ι) {P : LB (A ⊗ B).left} (h : Rep A b P) :
    IsChart A P where
  fam := h.fam
  inj := by
    intro Y u u' hs
    have hA : (ev P (fst A Y) (snd A Y ≫ u)).IsLB := pull_isLB h.fam.isLB _
    have hB : (ev P (fst A Y) (snd A Y ≫ u')).IsLB := pull_isLB h.fam.isLB _
    obtain ⟨x, -, hx⟩ := h.univ Y (u ≫ b) _ (fam_pull h.fam u)
    rw [hx u ⟨rfl, LBIso.trans hA hB hA hs (LBIso.symm hs)⟩, hx u' ⟨hom_open_eq V _ _, hs⟩]
  chart := by
    intro T N hN
    refine ⟨T.hom ⁻¹ᵁ V, fun Y y => ⟨?_, ?_⟩⟩
    · rintro ⟨u, -⟩ z
      have hb : b.left ≫ V.ι = B.hom := Over.w b
      have e : (u.left ≫ b.left) ≫ V.ι = y.left ≫ T.hom := by
        rw [Over.w y, Category.assoc, hb, Over.w u]
      have hmem : (y.left ≫ T.hom) z ∈ Set.range V.ι := ⟨(u.left ≫ b.left) z, by rw [← e]; rfl⟩
      rw [Scheme.Opens.range_ι] at hmem
      exact hmem
    · intro hz
      have hY : ∀ z, Y.hom z ∈ V := fun z => by
        rw [← Over.w y]
        exact hz z
      obtain ⟨t⟩ := exists_hom_open V Y hY
      obtain ⟨x, ⟨-, hx⟩, -⟩ := h.univ Y t _ (fam_pull hN y)
      exact ⟨x, hx⟩

omit [GrpObj A] in

theorem good_iso_comp {g : ℕ} {X X' Y : Scheme.{0}} (e : X' ⟶ X) [IsIso e] {f : X ⟶ Y}
    (h : GlobalTheory.DualCon.Good g f) : GlobalTheory.DualCon.Good g (e ≫ f) := ⟨MorphismProperty.RespectsIso.precomp @IsProper e f h.proper,
  by
    haveI := h.smooth
    have h0 : SmoothOfRelativeDimension (0 + g) (e ≫ f) := inferInstance
    rwa [zero_add] at h0,
  by
    haveI := h.conn
    have hsq : IsPullback e (e ≫ f) f (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsq h.conn⟩

theorem zariski_glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, HasRep A (g i) (Over.mk (V i).ι)) → ∃ (B : Over S) (P : LB (A ⊗ B).left), Rep A (toUnit B) P ∧ ∀ i, GlobalTheory.DualCon.Good (g i) (pullback.snd B.hom (V i).ι) := by
  intro S A _ hA Ix V g hcov hrep
  have hrep' : ∀ i, ∃ (B : Over S) (b : B ⟶ Over.mk (V i).ι) (P : LB (A ⊗ B).left),
      Rep A b P ∧ GlobalTheory.DualCon.Good (g i) b.left := hrep
  choose Bi bi Pi hRi hGi using hrep'
  obtain ⟨B, P, j, hR, -, -, -⟩ := GlobalTheory.T.glue_openCharts_additiveFamilies_representing S A hA Ix Bi Pi
    (fun i => isChart_of_rep (V i) (bi i) (hRi i)) (by
      intro K _ _ s N hN
      obtain ⟨i, hi⟩ := hcov (s (default : Sp K))
      have hs : ∀ z : Sp K, s z ∈ V i := fun z => by
        rw [Subsingleton.elim z default]
        exact hi
      obtain ⟨t⟩ := exists_hom_open (V i) (Over.mk s) hs
      obtain ⟨x, ⟨-, hx⟩, -⟩ := (hRi i).univ _ t N hN
      exact ⟨i, x, (same_id_iff hN.isLB (hRi i).fam.isLB x).2 hx⟩)
  refine ⟨B, P, hR, fun i => ?_⟩
  have hpb : IsPullback (fst B (Over.mk (V i).ι)) (snd B (Over.mk (V i).ι)) (toUnit B)
      (toUnit (Over.mk (V i).ι)) :=
    IsPullback.of_is_product' (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _)
      SemiCartesianMonoidalCategory.isTerminalTensorUnit
  have hR' := GlobalTheory.T.rep_ev_of_isPullback S A B (𝟙_ (Over S)) (Over.mk (V i).ι) (B ⊗ Over.mk (V i).ι) (toUnit B) P
    (toUnit _) (fst _ _) (snd _ _) hR hpb
  obtain ⟨e, he, -⟩ := GlobalTheory.T.representsAdditiveLineBundleFamilies_unique_iso S A _ _ _ (snd B (Over.mk (V i).ι)) _ (bi i) (Pi i) hR' (hRi i)
  haveI : IsIso e.hom.left := Functor.map_isIso (Over.forget _) e.hom
  have h2 := good_iso_comp e.hom.left (hGi i)
  rw [← Over.comp_left, he] at h2
  exact h2

end GlobalTheory.DualCon.ZarGlue
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additiveFamily_representative_zariski_glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, HasRep A (g i) (Over.mk (V i).ι)) → ∃ (B : Over S) (P : LB (A ⊗ B).left), Rep A (toUnit B) P ∧ ∀ i, GlobalTheory.DualCon.Good (g i) (pullback.snd B.hom (V i).ι) := by
  atlas_forward_decl GlobalTheory.DualCon.ZarGlue.zariski_glue
end

section
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem local_of_opens_pullback (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q] {X Y : Scheme.{0}}
    (f : X ⟶ Y) {Ix : Type} (V : Ix → Y.Opens) (hV : ∀ y : Y, ∃ i, y ∈ V i)
    (h : ∀ i, Q (pullback.snd f (V i).ι)) : Q f := by
  have hV' : iSup V = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 (hV y)
  exact IsZariskiLocalAtTarget.of_openCover (P := Q) (Y.openCoverOfIsOpenCover V hV') h

theorem Good.of_opens {g : ℕ} {X Y : Scheme.{0}} (f : X ⟶ Y) {Ix : Type} (V : Ix → Y.Opens)
    (hV : ∀ y : Y, ∃ i, y ∈ V i) (h : ∀ i, Good g (pullback.snd f (V i).ι)) : Good g f := by
  have h1 : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  have h2 : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
    rw [GeometricallyConnected.eq_geometrically]; infer_instance
  exact ⟨local_of_opens_pullback @IsProper f V hV fun i ↦ (h i).proper,
    local_of_opens_pullback (@SmoothOfRelativeDimension g) f V hV fun i ↦ (h i).smooth,
    local_of_opens_pullback @GeometricallyConnected f V hV fun i ↦ (h i).conn⟩

theorem hasRep_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (g : ℕ), IsAbelianScheme A → (∀ s : S, ∃ V : S.Opens, s ∈ V ∧ HasRep A g (Over.mk V.ι)) → HasRep A g (𝟙_ _) := by
  intro S A _ g hA h
  choose V hV hR using h
  obtain ⟨B, P, hP, hG⟩ := GlobalTheory.T.exists_additiveFamily_representative_zariski_glue S A hA S V (fun _ ↦ g) (fun s ↦ ⟨s, hV s⟩) hR
  exact ⟨B, toUnit B, P, hP, Good.of_opens (Y := S) B.hom V (fun s ↦ ⟨s, hV s⟩) hG⟩

end GlobalTheory.DualCon
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (g : ℕ), IsAbelianScheme A → (∀ s : S, ∃ V : S.Opens, s ∈ V ∧ HasRep A g (Over.mk V.ι)) → HasRep A g (𝟙_ _) := by
  atlas_forward_decl GlobalTheory.DualCon.hasRep_of_local
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.chartAroundUnit (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (s : Sp R) :
    ∃ f : R, s ∈ Set.range (spMap (algebraMap R (Localization.Away f))) ∧ ∃ W : A.left.Opens,
      IsAffineOpen W ∧ ∀ t ∈ Set.range (spMap (algebraMap R (Localization.Away f))),
        ∃ x ∈ W, A.hom x = t := by
  let e : Sp R ⟶ A.left := (η[A]).left
  have he : e ≫ A.hom = 𝟙 (Sp R) := Over.w (η[A])
  have hpt : ∀ t : Sp R, A.hom (e t) = t := by
    intro t
    rw [← Scheme.Hom.comp_apply, he]
    rfl
  obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := e s) trivial
  have hrange : ∀ f : R, Set.range (spMap (algebraMap R (Localization.Away f))) =
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
    intro f
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have hopen : IsOpen (e ⁻¹' (W : Set A.left)) := W.isOpen.preimage e.continuous
  obtain ⟨_, ⟨f, rfl⟩, hsf, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      (a := s) hsW hopen
  refine ⟨f, ?_, W, hW, ?_⟩
  · rw [hrange]; exact hsf
  · intro t ht
    rw [hrange] at ht
    exact ⟨e t, hsub ht, hpt t⟩
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_affineOpen_meeting_fibres_grpScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (s : Sp R), ∃ f : R, s ∈ Set.range (spMap (algebraMap R (Localization.Away f))) ∧ ∃ W : A.left.Opens, IsAffineOpen W ∧ ∀ t ∈ Set.range (spMap (algebraMap R (Localization.Away f))), ∃ x ∈ W, A.hom x = t := by
  atlas_forward_decl GlobalTheory.chartAroundUnit
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem affine_preimage_pullback_meets_fibres {R R' : Type} [CommRing R] [CommRing R'] (a : R →+* R')
    (A : Over (Sp R)) (W : A.left.Opens) : IsAffineOpen W →
    (∀ t ∈ Set.range (spMap a), ∃ x ∈ W, A.hom x = t) →
    ∃ V : ((Over.pullback (spMap a)).obj A).left.Opens, IsAffineOpen V ∧
      ∀ s : Sp R', ∃ x ∈ V, ((Over.pullback (spMap a)).obj A).hom x = s := by
  intro hW hfib
  haveI : IsAffineHom (pullback.fst A.hom (spMap a)) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  refine ⟨(pullback.fst A.hom (spMap a)) ⁻¹ᵁ W, hW.preimage _, ?_⟩
  intro s
  obtain ⟨x, hxW, hx⟩ := hfib (spMap a s) ⟨s, rfl⟩
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := A.hom) (g := spMap a) x s hx
  exact ⟨z, by show (pullback.fst A.hom (spMap a)) z ∈ W; rw [hz1]; exact hxW, hz2⟩

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineOpen_meeting_fibres_pullback_specRingHom : ∀ {R R' : Type} [CommRing R] [CommRing R'] (a : R →+* R') (A : Over (Sp R)) (W : A.left.Opens), IsAffineOpen W → (∀ t ∈ Set.range (spMap a), ∃ x ∈ W, A.hom x = t) → ∃ V : ((Over.pullback (spMap a)).obj A).left.Opens, IsAffineOpen V ∧ ∀ s : Sp R', ∃ x ∈ V, ((Over.pullback (spMap a)).obj A).hom x = s := by
  atlas_forward_decl GlobalTheory.affine_preimage_pullback_meets_fibres
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.Step

theorem exists_sq_zero (R : Type) [CommRing R] [IsNoetherianRing R] (h : ¬ IsReduced R) :
    ∃ J : Ideal R, J ≠ ⊥ ∧ J ^ 2 = ⊥ := by
  classical
  set N := nilradical R with hNdef
  have hN : N ≠ ⊥ := by
    intro h0
    apply h
    refine ⟨fun x hx => ?_⟩
    have : x ∈ N := (mem_nilradical).2 hx
    rw [h0] at this
    exact (Submodule.mem_bot R).1 this
  have hnil : IsNilpotent N := IsNoetherianRing.isNilpotent_nilradical R
  let n := Nat.find hnil
  have hn : N ^ n = 0 := Nat.find_spec hnil
  have hn0 : n ≠ 0 := by
    intro h0
    have : N ^ 0 = 0 := h0 ▸ hn
    rw [pow_zero] at this
    apply hN
    rw [eq_bot_iff, ← Ideal.zero_eq_bot, ← this, Ideal.one_eq_top]
    exact le_top
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hN
    rw [hk] at hn
    simpa using hn
  refine ⟨N ^ k, ?_, ?_⟩
  · intro h0
    have := Nat.find_min hnil (show k < n by omega)
    exact this h0
  · rw [← pow_mul]
    apply le_bot_iff.1
    calc N ^ (k * 2) ≤ N ^ (k + 1) := Ideal.pow_le_pow_right (by omega)
      _ = ⊥ := by rw [← Nat.succ_eq_add_one, ← hk]; exact hn

theorem hasRep_opens {S X : Scheme.{0}} (i : X ⟶ S) [IsOpenImmersion i] (A : Over S) [GrpObj A] (g : ℕ)
    (V : S.Opens) (hV : (V : Set S) ⊆ Set.range i) (h : HasRep A g (Over.mk i)) : HasRep A g (Over.mk V.ι) := by
  have hr : Set.range V.ι ⊆ Set.range i := by
    rw [Scheme.Opens.range_ι]; exact hV
  let m : Over.mk V.ι ⟶ Over.mk i := Over.homMk (IsOpenImmersion.lift i V.ι hr) (IsOpenImmersion.lift_fac _ _ _)
  exact GlobalTheory.T.baseChangeBis S A (Over.mk i) (Over.mk V.ι) g m h

theorem comap_ne_bot_away {R : Type} [CommRing R] (f : R) (J' : Ideal (Localization.Away f)) (h : J' ≠ ⊥) :
    J'.comap (algebraMap R (Localization.Away f)) ≠ ⊥ := by
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) y
  have hx : algebraMap R (Localization.Away f) x ∈ J' := by
    rw [← IsLocalization.mk'_spec (Localization.Away f) x s]
    exact J'.mul_mem_right _ hy
  have hx0 : algebraMap R (Localization.Away f) x ≠ 0 := by
    intro h0
    apply hy0
    rw [IsLocalization.mk'_eq_zero_iff]
    exact (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ x).1 h0
  intro hb
  have : x ∈ J'.comap (algebraMap R (Localization.Away f)) := hx
  rw [hb, Submodule.mem_bot] at this
  exact hx0 (by rw [this, map_zero])

theorem hasRep_quot {R R' : Type} [CommRing R] [CommRing R'] (a : R →+* R')
    (ha : ∀ J' : Ideal R', J' ≠ ⊥ → J'.comap a ≠ ⊥) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A']
    (φ : A'.left ⟶ A.left) (hφ : IsGrpPullback A' A (spMap a) φ) (g : ℕ)
    (hJ : ∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) :
    ∀ J' : Ideal R', J' ≠ ⊥ → HasRep A' g (Over.mk (spMap (Ideal.Quotient.mk J'))) := by
  intro J' hJ'
  set J := J'.comap a
  let q : R ⧸ J →+* R' ⧸ J' := Ideal.quotientMap J' a le_rfl
  have hq : q.comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk J').comp a := by
    ext x; rfl
  have w : spMap q ≫ spMap (Ideal.Quotient.mk J) = (Over.mk (spMap (Ideal.Quotient.mk J') ≫ spMap a)).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  let m : Over.mk (spMap (Ideal.Quotient.mk J') ≫ spMap a) ⟶ Over.mk (spMap (Ideal.Quotient.mk J)) :=
    Over.homMk (spMap q) w
  have h1 := GlobalTheory.T.baseChangeBis _ A _ _ g m (hJ J (ha J' hJ'))
  exact ((GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ (spMap a) A A' φ hφ g (Over.mk (spMap (Ideal.Quotient.mk J')))).1).2 h1

theorem local_rep (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (hJ : ∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) (s : Sp R) :
    ∃ V : (Sp R).Opens, s ∈ V ∧ HasRep A g (Over.mk V.ι) := by
  obtain ⟨f, hs, W, hW, hWf⟩ := GlobalTheory.T.exists_basicOpen_affineOpen_meeting_fibres_grpScheme R A s
  let a := algebraMap R (Localization.Away f)
  let A' := (Over.pullback (spMap a)).obj A
  letI : GrpObj A' := Functor.grpObjObj
  have hφ : IsGrpPullback A' A (spMap a) (pullback.fst _ _) := isGrpPullback_pullback A (spMap a)
  obtain ⟨hA', hg'⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback a A A' _ g hφ hA hg
  obtain ⟨V, hV, hVs⟩ := GlobalTheory.T.affineOpen_meeting_fibres_pullback_specRingHom a A W hW hWf
  haveI : @Algebra.FiniteType ℤ (Localization.Away f) _ _ (Ring.toIntAlgebra _) := by
    have h := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ R)
      (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) (Localization.Away f))
    convert h using 1 <;> first | rfl | exact Subsingleton.elim _ _
  have h1 : HasRep A' g (𝟙_ _) :=
    GlobalTheory.T.hasProperSmoothDualRepresentative_noetherianInduction (Localization.Away f) A' g hA' hg' V hV hVs
      (hasRep_quot a (comap_ne_bot_away f) A A' _ hφ g hJ)
  have h2 := ((GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ (spMap a) A A' _ hφ g (𝟙_ _)).1).1 h1
  have h3 : HasRep A g (Over.mk (spMap a)) := by
    convert h2 using 2 <;> first | rfl | exact (Category.id_comp _).symm
  have : IsOpenImmersion (spMap a) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))))
  refine ⟨(spMap a).opensRange, hs, hasRep_opens (spMap a) A g _ (fun x hx => hx) h3⟩

theorem step : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) → HasRep A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg hJ
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  by_cases hr : IsReduced R
  · exact GlobalTheory.T.hasProperSmoothDualRepresentative_of_local _ A g hA (local_rep R A g hA hg hJ)
  · obtain ⟨J, hJ0, hJ2⟩ := exists_sq_zero R hr
    exact GlobalTheory.T.hasProperSmoothDualRepresentative_of_sqZero R A g hA hg J hJ2 (hJ J hJ0)

end GlobalTheory.DualCon.Step
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_noetherian_induction : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) → HasRep A g (𝟙_ _) := by
  atlas_forward_decl GlobalTheory.DualCon.Step.step
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DualConFT

theorem hasRep_quot_of_factor {S T : Type} [CommRing S] [CommRing T] (J : Ideal S) (φ : S →+* T)
    (ψ : T →+* S ⧸ J) (hcomp : ψ.comp φ = Ideal.Quotient.mk J) (g : ℕ)
    (h : ∀ (B : Over (Sp T)) [GrpObj B], IsAbelianScheme B → SmoothOfRelativeDimension g B.hom →
      HasRep B g (𝟙_ _))
    (A : Over (Sp S)) [GrpObj A] (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J))) := by
  let f : Sp T ⟶ Sp S := spMap φ
  let B : Over (Sp T) := (Over.pullback f).obj A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsGrpPullback B A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  obtain ⟨hAB, hgB⟩ :=
    GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback φ A B _ g hB hA hg
  have h2 := (GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ f A B _ hB g (𝟙_ _)).1.mp (h B hAB hgB)
  refine GlobalTheory.T.baseChangeBis _ A (Over.mk ((𝟙_ (Over (Sp T))).hom ≫ f)) (Over.mk (spMap (Ideal.Quotient.mk J))) g
    (Over.homMk (spMap ψ) ?_) h2
  change spMap ψ ≫ 𝟙 _ ≫ spMap φ = spMap (Ideal.Quotient.mk J)
  rw [Category.id_comp, ← hcomp, spMap_comp]

end GlobalTheory.DualConFT

namespace GlobalTheory.DualConFT

theorem hasRep_quot (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (g : ℕ) (I : Ideal R) :
    ∀ (A : Over (Sp (R ⧸ I))) [GrpObj A], IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      HasRep A g (𝟙_ _) := by
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  induction I using WellFoundedGT.induction with
  | _ I ih =>
    intro A _ hA hg
    haveI : @Algebra.FiniteType ℤ (R ⧸ I) _ _ (Ring.toIntAlgebra _) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mk I).toIntAlgHom Ideal.Quotient.mk_surjective
    refine GlobalTheory.T.hasProperSmoothDualRepresentative_noetherian_induction (R ⧸ I) A g hA hg fun J' hJ' => ?_
    let J : Ideal R := J'.comap (Ideal.Quotient.mk I)
    have hle : I ≤ J := fun a ha => by
      show Ideal.Quotient.mk I a ∈ J'
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact J'.zero_mem
    have hlt : I < J := by
      refine lt_of_le_of_ne hle fun hIJ => hJ' ?_
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      have ha : a ∈ J := hx
      rw [← hIJ] at ha
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact (⊥ : Ideal (R ⧸ I)).zero_mem
    let ψ : R ⧸ J →+* (R ⧸ I) ⧸ J' :=
      Ideal.Quotient.lift J ((Ideal.Quotient.mk J').comp (Ideal.Quotient.mk I)) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.mpr ha
    refine hasRep_quot_of_factor J' (Ideal.Quotient.factor hle) ψ ?_ g (fun B _ hB hgB => ih J hlt B hB hgB)
      A hA hg
    apply Ideal.Quotient.ringHom_ext
    ext a
    rfl

theorem hasRep_of_finiteType : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (A : Over (Sp R)) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasRep A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg
  refine GlobalTheory.T.hasProperSmoothDualRepresentative_noetherian_induction R A g hA hg fun J _ => ?_
  exact hasRep_quot_of_factor J (Ideal.Quotient.mk J) (RingHom.id _) rfl g
    (fun B _ hB hgB => hasRep_quot R g J B hB hgB) A hA hg

end GlobalTheory.DualConFT
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_finiteType : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasRep A g (𝟙_ _) := by
  atlas_forward_decl GlobalTheory.DualConFT.hasRep_of_finiteType
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem hasRep_affine : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → HasRep A g (𝟙_ _) := by
  intro R _ A _ g hA hg
  obtain ⟨S, B, _, φ, -, hS, hB, hgB, hφ⟩ :=
    GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring R g A ∅ hA hg
  have h₀ : HasRep B g (𝟙_ _) := GlobalTheory.T.hasProperSmoothDualRepresentative_finiteType S B g hB hgB
  exact (GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ _ B A φ hφ g (𝟙_ _)).1.2 (GlobalTheory.T.baseChangeBis _ B _ _ g (toUnit _) h₀)

end GlobalTheory.DualCon
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_dual_representable_affine_base : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasRep A g (𝟙_ _) := by
  atlas_forward_decl GlobalTheory.DualCon.hasRep_affine
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

instance isZariskiLocalAtTarget_smoothDim (n : ℕ) : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension n) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension n)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))

theorem smoothDim_restrict_pullback {S T X : Scheme.{0}} (b : X ⟶ S) (t : T ⟶ S) (U : S.Opens) {n : ℕ}
    (h : SmoothOfRelativeDimension n (pullback.snd b U.ι)) :
    SmoothOfRelativeDimension n (pullback.snd b t ∣_ (t ⁻¹ᵁ U)) := by
  have big := (isPullback_morphismRestrict (pullback.snd b t) (t ⁻¹ᵁ U)).flip.paste_horiz
    (IsPullback.of_hasPullback b t)
  rw [← morphismRestrict_ι t U] at big
  have hc : ((pullback.snd b t ⁻¹ᵁ (t ⁻¹ᵁ U)).ι ≫ pullback.fst b t) ≫ b =
      (pullback.snd b t ∣_ (t ⁻¹ᵁ U) ≫ t ∣_ U) ≫ U.ι := by
    simp only [Category.assoc, pullback.condition, morphismRestrict_ι, morphismRestrict_ι_assoc]
  have sq := IsPullback.of_right (h₁₁ := pullback.lift _ _ hc) (by rw [pullback.lift_fst]; exact big)
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback b U.ι)
  exact (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback sq h

theorem dimLe_of_local : ∀ (S : Scheme.{0}) (A B : Over S), Surjective A.hom → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd A.hom (V i).ι)) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd B.hom (V i).ι)) → DimLe A B := by
  intro S A B hs Ix V g hV hA hB n T t hn
  have hcov : iSup (fun i => t ⁻¹ᵁ V i) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨i, hi⟩ := hV (t y)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) _ hcov fun i => ?_
  by_cases hne : ∃ y, y ∈ t ⁻¹ᵁ V i
  · obtain ⟨y, hy⟩ := hne
    have : Surjective (pullback.snd A.hom t) := by haveI := hs; infer_instance
    obtain ⟨x, hx⟩ := (pullback.snd A.hom t).surjective y
    have h1 : SmoothOfRelativeDimension n (pullback.snd A.hom t ∣_ (t ⁻¹ᵁ V i)) :=
      IsZariskiLocalAtTarget.restrict hn _
    have h2 := smoothDim_restrict_pullback A.hom t (V i) (hA i)
    have e : n = g i := ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2
      ⟨x, by rw [Scheme.Hom.mem_preimage, hx]; exact hy⟩
    rw [e]
    exact smoothDim_restrict_pullback B.hom t (V i) (hB i)
  · push_neg at hne
    exact ⟨fun x => (hne _ x.2).elim⟩

end GlobalTheory.DualCon
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relDimPreserved_of_equal_local_relDims : ∀ (S : Scheme.{0}) (A B : Over S), Surjective A.hom → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd A.hom (V i).ι)) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd B.hom (V i).ι)) → DimLe A B := by
  atlas_forward_decl GlobalTheory.DualCon.dimLe_of_local
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

variable {S : Scheme.{0}}

def addCls (A : Over S) [GrpObj A] (T : Over S) : AddSubgroup (Pic (A ⊗ T).left) where
  carrier := {c | ∀ (Y : Over S) (a a' : Y ⟶ A) (t : Y ⟶ T),
    CechPic.pull (lift (a * a') t).left c = CechPic.pull (lift a t).left c + CechPic.pull (lift a' t).left c}
  add_mem' {c d} hc hd Y a a' t := by
    simp only [map_add]
    rw [hc Y a a' t, hd Y a a' t]
    abel
  zero_mem' Y a a' t := by simp only [map_zero, add_zero]
  neg_mem' {c} hc Y a a' t := by
    simp only [map_neg]
    rw [hc Y a a' t]
    abel

variable {A : Over S} [GrpObj A]

theorem fam_iff_mem {T : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) : Fam A N ↔ cls N hN ∈ addCls A T :=
  ⟨fun h ↦ (isAdditive_iff hN).1 h.add, fun h ↦ ⟨hN, (isAdditive_iff hN).2 h⟩⟩

def resCls {T' T : Over S} (u : T' ⟶ T) : addCls A T →+ addCls A T' :=
  ((CechPic.pull (lift (fst A T') (snd A T' ≫ u)).left).comp (addCls A T).subtype).codRestrict _
    fun c Y a a' t ↦ by
      simp only [AddMonoidHom.coe_comp, AddSubgroup.coe_subtype, Function.comp_apply, ← CechPic.pull_comp,
        ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
      exact c.2 Y a a' (t ≫ u)

variable (A) in

def famFunctor : (Over S)ᵒᵖ ⥤ CommGrpCat.{1} where
  obj T := CommGrpCat.of (Multiplicative (addCls A T.unop))
  map g := CommGrpCat.ofHom (AddMonoidHom.toMultiplicative (resCls (A := A) g.unop))
  map_id T := by
    refine CommGrpCat.hom_ext (MonoidHom.ext fun c ↦ ?_)
    refine Subtype.ext ?_
    change CechPic.pull (lift (fst A T.unop) (snd A T.unop ≫ 𝟙 _)).left _ = _
    rw [Category.comp_id, lift_fst_snd, Over.id_left, CechPic.pull_id]
    rfl
  map_comp {T T' T''} g g' := by
    refine CommGrpCat.hom_ext (MonoidHom.ext fun c ↦ ?_)
    refine Subtype.ext ?_
    change CechPic.pull (lift (fst A T''.unop) (snd A T''.unop ≫ g'.unop ≫ g.unop)).left _ =
      CechPic.pull (lift (fst A T''.unop) (snd A T''.unop ≫ g'.unop)).left
        (CechPic.pull (lift (fst A T'.unop) (snd A T'.unop ≫ g.unop)).left _)
    rw [← CechPic.pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.assoc]

section Rep

variable {B : Over S} {P : LB (A ⊗ B).left} (h : Rep A (toUnit B) P)

include h

def ptCls (T : Over S) (x : T ⟶ B) : addCls A T :=
  ⟨evc h.fam.isLB (fst A T) (snd A T ≫ x), (fam_iff_mem (pull_isLB h.fam.isLB _)).1
    ⟨pull_isLB h.fam.isLB _, fun Y a a' t ↦ by
      refine (cls_eq_iff (pull_isLB (pull_isLB h.fam.isLB _) _)
        (isLB_tens (pull_isLB (pull_isLB h.fam.isLB _) _) (pull_isLB (pull_isLB h.fam.isLB _) _))).1 ?_
      rw [cls_tens (pull_isLB (pull_isLB h.fam.isLB _) _) (pull_isLB (pull_isLB h.fam.isLB _) _)]
      rw [cls_ev (pull_isLB h.fam.isLB _), cls_ev (pull_isLB h.fam.isLB _), cls_ev (pull_isLB h.fam.isLB _)]
      rw [evc_ev h.fam.isLB, evc_ev h.fam.isLB, evc_ev h.fam.isLB]
      simp only [lift_fst, lift_snd_assoc]
      exact (isAdditive_iff h.fam.isLB).1 h.fam.add Y _ _ _⟩⟩

theorem ptCls_bij (T : Over S) : Function.Bijective (ptCls h T) := by
  have hP := h.fam.isLB
  constructor
  · intro x x' e
    have hN : (ev P (fst A T) (snd A T ≫ x)).IsLB := pull_isLB hP _
    have fN : Fam A (ev P (fst A T) (snd A T ≫ x)) := (fam_iff_mem hN).2 (ptCls h T x).2
    refine (h.univ T (toUnit T) _ fN).unique ⟨toUnit_unique _ _, (cls_eq_iff hN hN).1 rfl⟩
      ⟨toUnit_unique _ _, (cls_eq_iff hN (pull_isLB hP _)).1 (congrArg Subtype.val e)⟩
  · intro c
    obtain ⟨N, hN, hc⟩ := cls_surj (c : Pic (A ⊗ T).left)
    have fN : Fam A N := (fam_iff_mem hN).2 (hc ▸ c.2)
    obtain ⟨x, ⟨-, hx⟩, -⟩ := h.univ T (toUnit T) N fN
    exact ⟨x, Subtype.ext (((cls_eq_iff hN (pull_isLB hP _)).2 hx).symm.trans hc)⟩

theorem ptCls_comp {T' T : Over S} (g : T' ⟶ T) (x : T ⟶ B) :
    ptCls h T' (g ≫ x) = resCls g (ptCls h T x) := by
  refine Subtype.ext ?_
  change evc h.fam.isLB (fst A T') (snd A T' ≫ g ≫ x) =
    CechPic.pull (lift (fst A T') (snd A T' ≫ g)).left (evc h.fam.isLB (fst A T) (snd A T ≫ x))
  rw [pull_evc, lift_fst, lift_snd_assoc, Category.assoc]

def famRep : (famFunctor A ⋙ forget CommGrpCat.{1}).RepresentableBy B where
  homEquiv {T} := (Equiv.ofBijective _ (ptCls_bij h T)).trans Multiplicative.ofAdd
  homEquiv_comp g x := ptCls_comp h g x

end Rep

end GlobalTheory.DualCon

namespace GlobalTheory.DualCon

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {B : Over S} {P : LB (A ⊗ B).left}

theorem evc_eq_pull_ptCls (h : Rep A (toUnit B) P) {Y : Over S} (a : Y ⟶ A) (x : Y ⟶ B) :
    evc h.fam.isLB a x = CechPic.pull (lift a (𝟙 Y)).left (ptCls h Y x : Pic (A ⊗ Y).left) := by
  change _ = CechPic.pull (lift a (𝟙 Y)).left (evc h.fam.isLB (fst A Y) (snd A Y ≫ x))
  rw [pull_evc, lift_fst, lift_snd_assoc, Category.id_comp]

theorem rep_isDual : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] (P : LB (A ⊗ B).left),
    Rep A (toUnit B) P → ∃ _ : GrpObj B, IsCommMonObj B ∧ IsDual A B P ∧ IsAdditive (swap P) := by
  intro S A B _ P h
  have hP := h.fam.isLB
  letI inst : CommGrpObj B := CommGrpObj.ofRepresentableBy B _ (famRep h)
  have hmul : ∀ (Y : Over S) (x y : Y ⟶ B), ptCls h Y (x * y) = ptCls h Y x + ptCls h Y y := by
    have hμ : ptCls h (B ⊗ B) μ[B] = ptCls h _ (fst B B) + ptCls h _ (snd B B) :=
      Equiv.ofBijective_apply_symm_apply (ptCls h (B ⊗ B)) (ptCls_bij h _) _
    intro Y x y
    rw [Hom.mul_def, ptCls_comp, hμ, map_add, ← ptCls_comp, ← ptCls_comp, lift_fst, lift_snd]
  have hone : ∀ (Y : Over S), ptCls h Y (1 : Y ⟶ B) = 0 := by
    have hη : ptCls h (𝟙_ (Over S)) η[B] = 0 :=
      Equiv.ofBijective_apply_symm_apply (ptCls h _) (ptCls_bij h _) 0
    intro Y
    rw [Hom.one_def, ptCls_comp, hη, map_zero]
  refine ⟨inferInstance, inferInstance, ⟨hP, h.fam.add, ?_, fun T M hM hA ↦ ?_⟩, ?_⟩
  · rw [triv_ev_iff hP, evc_eq_pull_ptCls h, hone, ZeroMemClass.coe_zero, map_zero]
  · obtain ⟨x, ⟨-, hx⟩, hu⟩ := h.univ T (toUnit T) M ⟨hM, hA⟩
    exact ⟨x, hx, fun y hy ↦ hu y ⟨toUnit_unique _ _, hy⟩⟩
  · have hs : (swap P).IsLB := pull_isLB hP _
    refine (isAdditive_iff hs).2 fun Y b b' a ↦ ?_
    rw [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs, evc_eq_pull_ptCls h, evc_eq_pull_ptCls h,
      evc_eq_pull_ptCls h, hmul, AddSubgroup.coe_add, map_add]

end GlobalTheory.DualCon
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representing_additiveFamilies_isDual_comm : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] (P : LB (A ⊗ B).left), Rep A (toUnit B) P → ∃ _ : GrpObj B, IsCommMonObj B ∧ IsDual A B P ∧ IsAdditive (swap P) := by
  atlas_forward_decl GlobalTheory.DualCon.rep_isDual
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem abelianScheme_locally_relDim : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ s : S,
    ∃ (V : S.Opens) (g : ℕ), IsAffineOpen V ∧ s ∈ V ∧ SmoothOfRelativeDimension g (pullback.snd A.hom V.ι) := by
  intro S A _ hA s
  have := hA.smooth
  have := hA.geomConnected
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim A.hom
  have loc : ∀ x y, y ∈ W x → n y = n x := fun x y hy => by
    have := hd x
    have := hd y
    have e₁ : SmoothOfRelativeDimension (0 + n y) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W y ⊓ W x ≤ W y), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + n x) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W y ⊓ W x ≤ W x), Category.assoc]; infer_instance
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨y, hW y, hy⟩
  have hc : IsLocallyConstant n :=
    (IsLocallyConstant.iff_exists_open n).2 fun x => ⟨W x, (W x).isOpen, hW x, loc x⟩
  have hsec : η[A].left ≫ A.hom = 𝟙 S := Over.w η[A]
  have he : ∀ t : S, A.hom (η[A].left t) = t := fun t => by
    rw [← Scheme.Hom.comp_apply, hsec]; rfl
  have fib : ∀ x, n x = n (η[A].left (A.hom x)) := fun x => by
    have hconn : _root_.IsPreconnected (A.hom ⁻¹' {A.hom x}) := by
      rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
      exact isPreconnected_univ.image _ (A.hom.fiberι _).continuous.continuousOn
    exact hc.apply_eq_of_isPreconnected hconn rfl (he (A.hom x))
  let x₀ : A.left := η[A].left s
  let U : S.Opens := η[A].left ⁻¹ᵁ W x₀
  have hsU : s ∈ U := hW x₀
  obtain ⟨V, hV, hsV, hVU⟩ := exists_isAffineOpen_mem_and_subset hsU
  refine ⟨V, n x₀, hV, hsV, ?_⟩
  have dimy : ∀ y, n (pullback.fst A.hom V.ι y) = n x₀ := fun y => by
    have h1 : A.hom (pullback.fst A.hom V.ι y) ∈ V := by
      have := congrArg (fun g => g y) (pullback.condition (f := A.hom) (g := V.ι))
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]; exact (pullback.snd A.hom V.ι y).2
    rw [fib, loc _ _ (hVU h1)]
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (n x₀)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (n x₀))
    (fun y => pullback.fst A.hom V.ι ⁻¹ᵁ W (pullback.fst A.hom V.ι y))
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW _⟩) fun y => ?_
  rw [← dimy y]
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    ((isPullback_morphismRestrict (pullback.fst A.hom V.ι) (W _)).paste_vert (IsPullback.of_hasPullback _ _))
    (hd (pullback.fst A.hom V.ι y))

end GlobalTheory.DualCon
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_locally_constant_relDim : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ s : S, ∃ (V : S.Opens) (g : ℕ), IsAffineOpen V ∧ s ∈ V ∧ SmoothOfRelativeDimension g (pullback.snd A.hom V.ι) := by
  atlas_forward_decl GlobalTheory.DualCon.abelianScheme_locally_relDim
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualExist

theorem hasRep_of_iso {S : Scheme.{0}} {A : Over S} [GrpObj A] {g : ℕ} {S₁ S₂ : Over S} (e : S₁ ≅ S₂)
    (h : HasRep A g S₁) : HasRep A g S₂ := by
  obtain ⟨B, b, P, hR, hG⟩ := h
  refine ⟨B, b ≫ e.hom, P, ⟨hR.fam, fun T t N hN => ?_⟩, ?_⟩
  · obtain ⟨x, ⟨hx, hxN⟩, hu⟩ := hR.univ T (t ≫ e.inv) N hN
    refine ⟨x, ⟨by rw [← Category.assoc, hx, Category.assoc, e.inv_hom_id, Category.comp_id], hxN⟩,
      fun y ⟨hy, hyN⟩ => hu y ⟨?_, hyN⟩⟩
    rw [← hy, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]
  · have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget S).mapIso e).inv)
    have sq : IsPullback (𝟙 B.left) (b.left ≫ e.hom.left) b.left e.inv.left :=
      IsPullback.of_horiz_isIso ⟨by
        rw [Category.id_comp, Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left, Category.comp_id]⟩
    have hp := hG.proper
    have := smoothOfRelativeDimension_isStableUnderBaseChange g
    rw [Over.comp_left]
    exact ⟨MorphismProperty.of_isPullback (P := @IsProper) sq hp, MorphismProperty.of_isPullback sq hG.smooth,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq hG.conn⟩

theorem hasRep_affineOpen {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {V : S.Opens}
    (hV : IsAffineOpen V) (g : ℕ) (hg : SmoothOfRelativeDimension g (pullback.snd A.hom V.ι)) :
    HasRep A g (Over.mk V.ι) := by
  let A' : Over (Sp Γ(S, V)) := (Over.pullback hV.fromSpec).obj A
  letI : GrpObj A' := Functor.grpObjObj
  have hpb : IsGrpPullback A' A hV.fromSpec (pullback.fst A.hom hV.fromSpec) :=
    isGrpPullback_pullback A hV.fromSpec
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hpb
  have hg' : SmoothOfRelativeDimension g A'.hom := by
    have sq : IsPullback (pullback.lift (pullback.fst A.hom hV.fromSpec)
        (pullback.snd A.hom hV.fromSpec ≫ hV.isoSpec.inv)
        (by rw [pullback.condition, Category.assoc, IsAffineOpen.isoSpec_inv_ι]))
        (pullback.snd A.hom hV.fromSpec) (pullback.snd A.hom V.ι) hV.isoSpec.inv :=
      IsPullback.of_right (by rw [pullback.lift_fst]; exact IsPullback.of_hasPullback A.hom hV.fromSpec)
        (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback A.hom V.ι)
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange g
    exact MorphismProperty.of_isPullback sq hg
  have h1 := ((GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ hV.fromSpec A A' _ hpb g (𝟙_ _)).1).1 (GlobalTheory.T.abelianScheme_dual_representable_affine_base _ A' g hA' hg')
  refine hasRep_of_iso (Over.isoMk hV.isoSpec.symm ?_) h1
  show hV.isoSpec.inv ≫ V.ι = 𝟙 _ ≫ hV.fromSpec
  rw [Category.id_comp, IsAffineOpen.isoSpec_inv_ι]

theorem exists_dual : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∃ (B : Over S) (_ : GrpObj B) (P : LB (A ⊗ B).left), IsAbelianScheme B ∧ DimLe A B ∧ IsDual A B P := by
  intro S A _ hA
  choose V g hV hsV hgV using GlobalTheory.T.abelianScheme_locally_constant_relDim S A hA
  have cov : ∀ s : S, ∃ i, s ∈ V i := fun s => ⟨s, hsV s⟩
  obtain ⟨B, P, hR, hGood⟩ :=
    GlobalTheory.T.exists_additiveFamily_representative_zariski_glue S A hA S V g cov (fun i => hasRep_affineOpen A hA (hV i) (g i) (hgV i))
  obtain ⟨inst, hcomm, hD, -⟩ := GlobalTheory.T.representing_additiveFamilies_isDual_comm S A B P hR
  refine ⟨B, inst, P, ?_, ?_, hD⟩
  · have hU : iSup V = ⊤ := eq_top_iff.2 fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hsV s⟩
    have : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
      rw [GeometricallyConnected.eq_geometrically]; infer_instance
    have : IsZariskiLocalAtTarget @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
    have sq := fun i => IsPullback.of_hasPullback B.hom (V i).ι
    exact
      { comm := hcomm
        smooth := GlobalTheory.CoverGlue.of_isPullback_cover @Smooth hU sq fun i => by
          haveI := (hGood i).smooth; exact SmoothOfRelativeDimension.smooth (g i) _
        proper := GlobalTheory.CoverGlue.of_isPullback_cover @IsProper hU sq fun i => (hGood i).proper
        geomConnected := GlobalTheory.CoverGlue.of_isPullback_cover @GeometricallyConnected hU sq fun i => (hGood i).conn }
  · have : GeometricallyConnected A.hom := hA.geomConnected
    exact GlobalTheory.T.relDimPreserved_of_equal_local_relDims S A B inferInstance S V g cov hgV fun i => (hGood i).smooth

end GlobalTheory.DualExist
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_abelianScheme_poincare : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∃ (B : Over S) (_ : GrpObj B) (P : LB (A ⊗ B).left), IsAbelianScheme B ∧ DimLe A B ∧ IsDual A B P := by
  atlas_forward_decl GlobalTheory.DualExist.exists_dual
end
