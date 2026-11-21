import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDataOfCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafGlueOfOpenImmersions

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace GlobalTheory.IdealGlue

theorem exists_comap_eq : ∀ {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : X, ∃ i y, f i y = x) →
    ∀ (J : ∀ i, (V i).IdealSheafData),
    (∀ i j (Y : Scheme.{0}) (a : Y ⟶ V i) (a' : Y ⟶ V j), a ≫ f i = a' ≫ f j →
      (J i).comap a = (J j).comap a') →
    ∃ I : X.IdealSheafData, ∀ i, I.comap (f i) = J i := by
  intro X ι V f hf hcov J hJ
  exact idealSheaf_glue_of_openImmersions (fun 𝒜 h1 h2 k h3 => GlobalTheory.T.exists_idealSheafData_of_compatible_ideals 𝒜 h1 h2 k h3)
    V f hf (fun x => by obtain ⟨i, y, hy⟩ := hcov x; exact ⟨i, y, hy⟩) J hJ

end GlobalTheory.IdealGlue
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idealSheaf_comap_eq_of_openCover : ∀ {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : X, ∃ i y, f i y = x) →
    ∀ (J : ∀ i, (V i).IdealSheafData),
    (∀ i j (Y : Scheme.{0}) (a : Y ⟶ V i) (a' : Y ⟶ V j), a ≫ f i = a' ≫ f j →
      (J i).comap a = (J j).comap a') →
    ∃ I : X.IdealSheafData, ∀ i, I.comap (f i) = J i := by
  first | (exact @GlobalTheory.IdealGlue.exists_comap_eq) | (exact GlobalTheory.IdealGlue.exists_comap_eq) | (intros; apply GlobalTheory.IdealGlue.exists_comap_eq <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace GlobalTheory.HilbAff

theorem idealSheafData_ext_of_openCover {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0})
    (f : ∀ i, V i ⟶ X) (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : X, ∃ i y, f i y = x)
    (I I' : X.IdealSheafData) (h : ∀ i, I.comap (f i) = I'.comap (f i)) : I = I' := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := Σ i, (V i).affineOpens)
    (fun p => ⟨(f p.1) ''ᵁ p.2.1, p.2.2.image_of_isOpenImmersion (f p.1)⟩) ?_ ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, y, rfl⟩ := hcov x
    have hy : y ∈ (⊤ : (V i).Opens) := trivial
    rw [← iSup_affineOpens_eq_top (V i)] at hy
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, W⟩, ⟨y, hW, rfl⟩⟩
  · rintro ⟨i, W⟩
    have e := congrArg (fun J => J.ideal W) (h i)
    simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at e
    exact Ideal.comap_injective_of_surjective _
      ((ConcreteCategory.bijective_of_isIso ((f i).appIso W).inv).2) e

end GlobalTheory.HilbAff
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheafData_ext_of_openCover' : ∀ {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : X, ∃ i y, f i y = x) →
    ∀ (I I' : X.IdealSheafData), (∀ i, I.comap (f i) = I'.comap (f i)) → I = I' := by
  first | (exact @GlobalTheory.HilbAff.idealSheafData_ext_of_openCover) | (exact GlobalTheory.HilbAff.idealSheafData_ext_of_openCover) | (intros; apply GlobalTheory.HilbAff.idealSheafData_ext_of_openCover  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace GlobalTheory.HilbAff

set_option backward.isDefEq.respectTransparency.types false in

theorem of_isPullback_openImmersions (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    {X T : Scheme.{0}} (φ : X ⟶ T) {ι : Type u} {V : ι → Scheme.{0}} (f : ∀ i, V i ⟶ T)
    [∀ i, IsOpenImmersion (f i)] (hcov : ∀ x : T, ∃ i y, f i y = x)
    {Z : ι → Scheme.{0}} (k : ∀ i, Z i ⟶ X) (q : ∀ i, Z i ⟶ V i)
    (H : ∀ i, IsPullback (k i) (q i) φ (f i)) (hq : ∀ i, P (q i)) : P φ := by
  have hU : iSup (fun i => (f i).opensRange) = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, y, rfl⟩ := hcov x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, rfl⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top _ hU fun i => ?_
  refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange φ (f i))).mpr ?_
  rw [← (H i).isoPullback_inv_snd]
  exact (P.cancel_left_of_respectsIso _ _).mpr (hq i)

set_option backward.isDefEq.respectTransparency.types false in
theorem good_of_cover : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    {T : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ T),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : T, ∃ i y, f i y = x) →
    ∀ (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData),
    (∀ i, GlobalTheory.HilbAff.Good A B r (f i ≫ g) (I.comap (GlobalTheory.HilbAff.bc A B g (f i)))) →
    GlobalTheory.HilbAff.Good A B r g I := by
  intro A B _ _ _ r T ι V f hf hcov g I hG
  have H : ∀ i, IsPullback (pullback.snd (bc A B g (f i)) I.subschemeι)
      (pullback.fst (bc A B g (f i)) I.subschemeι ≫ pullback.snd _ (f i ≫ g))
      (I.subschemeι ≫ pullback.snd _ g) (f i) := fun i =>
    (IsPullback.of_hasPullback (bc A B g (f i)) I.subschemeι).flip.paste_vert
      (isPullback_bc A B g (f i))
  have e : ∀ i, (I.comap (bc A B g (f i))).subschemeι ≫ pullback.snd _ (f i ≫ g) =
      (I.comapIso (bc A B g (f i))).hom ≫ (pullback.fst (bc A B g (f i)) I.subschemeι ≫
        pullback.snd _ (f i ≫ g)) := fun i => by
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have hfin : ∀ i, IsFinite (pullback.fst (bc A B g (f i)) I.subschemeι ≫
      pullback.snd _ (f i ≫ g)) := fun i => by
    have h := (hG i).1
    rw [e i, MorphismProperty.cancel_left_of_respectsIso @IsFinite.{0}] at h
    exact h
  have hfl : ∀ i, Flat (pullback.fst (bc A B g (f i)) I.subschemeι ≫
      pullback.snd _ (f i ≫ g)) := fun i => by
    have h := (hG i).2.1
    rw [e i, MorphismProperty.cancel_left_of_respectsIso @Flat.{0}] at h
    exact h
  have : IsZariskiLocalAtTarget @Flat.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0})
  have : IsZariskiLocalAtTarget @IsFinite.{0} := inferInstance
  have h1 : IsFinite (I.subschemeι ≫ pullback.snd _ g) :=
    of_isPullback_openImmersions @IsFinite.{0} _ f hcov _ _ H hfin
  have h2 : Flat (I.subschemeι ≫ pullback.snd _ g) :=
    of_isPullback_openImmersions @Flat.{0} _ f hcov _ _ H hfl
  refine ⟨h1, h2, fun y => ?_⟩
  obtain ⟨i, y', rfl⟩ := hcov y
  have h := (hG i).2.2 y'
  rw [e i, Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_of_isPullback _ _ _ _ (H i) y'] at h
  exact h

end GlobalTheory.HilbAff
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFiniteFlatRankClosedSubscheme_of_openCover : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    {T : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ T),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : T, ∃ i y, f i y = x) →
    ∀ (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData),
    (∀ i, GlobalTheory.HilbAff.Good A B r (f i ≫ g) (I.comap (GlobalTheory.HilbAff.bc A B g (f i)))) →
    GlobalTheory.HilbAff.Good A B r g I := by
  first | (exact @GlobalTheory.HilbAff.good_of_cover) | (exact GlobalTheory.HilbAff.good_of_cover) | (intros; apply GlobalTheory.HilbAff.good_of_cover  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace GlobalTheory.HilbAff
theorem glue_exists {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X)
    (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : X, ∃ i y, f i y = x)
    (J : ∀ i, (V i).IdealSheafData)
    (hJ : ∀ i j (Y : Scheme.{0}) (a : Y ⟶ V i) (a' : Y ⟶ V j), a ≫ f i = a' ≫ f j →
      (J i).comap a = (J j).comap a') :
    ∃ I : X.IdealSheafData, ∀ i, I.comap (f i) = J i :=
  GlobalTheory.T.exists_idealSheaf_comap_eq_of_openCover V f hf hcov J hJ
theorem glue_ext {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X)
    (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : X, ∃ i y, f i y = x)
    (I I' : X.IdealSheafData) (h : ∀ i, I.comap (f i) = I'.comap (f i)) : I = I' :=
  GlobalTheory.T.idealSheafData_ext_of_openCover' V f hf hcov I I' h
theorem good_local (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    {T : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ T)
    (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : T, ∃ i y, f i y = x)
    (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData)
    (h : ∀ i, GlobalTheory.HilbAff.Good A B r (f i ≫ g) (I.comap (GlobalTheory.HilbAff.bc A B g (f i)))) :
    GlobalTheory.HilbAff.Good A B r g I :=
  GlobalTheory.T.isFiniteFlatRankClosedSubscheme_of_openCover A B r V f hf hcov g I h

theorem snd_eq_of_sigma {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ} {T : Scheme.{0}}
    {g₀ g₁ : T ⟶ Spec (CommRingCat.of A)}
    {I₀ : (pullback (str A B) g₀).IdealSheafData} {I₁ : (pullback (str A B) g₁).IdealSheafData}
    {h₀ : Good A B r g₀ I₀} {h₁ : Good A B r g₁ I₁}
    (e : (⟨g₀, ⟨I₀, h₀⟩⟩ : Σ g : T ⟶ Spec (CommRingCat.of A),
      {I : (pullback (str A B) g).IdealSheafData // Good A B r g I}) = ⟨g₁, ⟨I₁, h₁⟩⟩) :
    ∃ h : g₀ = g₁, I₀ = I₁.comap (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h])) := by
  have hg : g₀ = g₁ := congrArg Sigma.fst e
  refine ⟨hg, ?_⟩
  subst hg
  have h2 : I₀ = I₁ := by
    have := (Sigma.mk.inj_iff.mp e).2
    exact congrArg Subtype.val (eq_of_heq this)
  have : pullback.map (str A B) g₀ (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    ext <;> simp
  rw [this, Scheme.IdealSheafData.comap_id, h2]

theorem fac_bc {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {T Z : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (φ : Z ⟶ pullback (str A B) g) :
    pullback.lift (φ ≫ pullback.fst _ _) (𝟙 Z) (by
        rw [Category.id_comp, Category.assoc, pullback.condition, Category.assoc]) ≫
      bc A B g (φ ≫ pullback.snd _ _) = φ := by
  apply pullback.hom_ext <;> simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem lift_map_eq {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {T T' Z : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (g' : T' ⟶ Spec (CommRingCat.of A))
    (φ : Z ⟶ pullback (str A B) g) (φ' : Z ⟶ pullback (str A B) g')
    (e1 : φ ≫ pullback.fst _ _ = φ' ≫ pullback.fst _ _)
    (hh : (φ ≫ pullback.snd _ _) ≫ g = (φ' ≫ pullback.snd _ _) ≫ g') :
    pullback.lift (φ ≫ pullback.fst _ _) (𝟙 Z) (by
        rw [Category.id_comp, Category.assoc, pullback.condition, Category.assoc]) ≫
      pullback.map (str A B) ((φ ≫ pullback.snd _ _) ≫ g) (str A B) ((φ' ≫ pullback.snd _ _) ≫ g')
        (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [hh]) =
    pullback.lift (φ' ≫ pullback.fst _ _) (𝟙 Z) (by
        rw [Category.id_comp, Category.assoc, pullback.condition, Category.assoc]) := by
  apply pullback.hom_ext
  · simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
    exact e1
  · simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem comap_eq_of_map_eq {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
    {X X' Z : Scheme.{0}} (y : (functor A B r).obj (op X)) (y' : (functor A B r).obj (op X'))
    (φ : Z ⟶ pullback (str A B) y.1) (φ' : Z ⟶ pullback (str A B) y'.1)
    (e1 : φ ≫ pullback.fst _ _ = φ' ≫ pullback.fst _ _)
    (e : (functor A B r).map (φ ≫ pullback.snd _ _).op y =
      (functor A B r).map (φ' ≫ pullback.snd _ _).op y') :
    y.2.1.comap φ = y'.2.1.comap φ' := by
  obtain ⟨hh, hI⟩ := snd_eq_of_sigma e
  simp only [Quiver.Hom.unop_op] at hh hI
  rw [← fac_bc y.1 φ, ← fac_bc y'.1 φ', Scheme.IdealSheafData.comap_comp, hI,
    Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp _ _ (pullback.map _ _ _ _ _ _ _ _ _),
    lift_map_eq y.1 y'.1 φ φ' e1 hh, ← Scheme.IdealSheafData.comap_comp]

theorem good_transport {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ} {T : Scheme.{0}}
    {g₀ g : T ⟶ Spec (CommRingCat.of A)} (h : g₀ = g)
    {I : (pullback (str A B) g).IdealSheafData} (hI : Good A B r g I) :
    Good A B r g₀ (I.comap (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h]))) := by
  subst h
  have : pullback.map (str A B) g₀ (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    ext <;> simp
  rw [this, Scheme.IdealSheafData.comap_id]
  exact hI

theorem isOpenImmersion_bc (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T T' : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T) [IsOpenImmersion a] :
    IsOpenImmersion (bc A B g a) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_bc A B g a).flip inferInstance

theorem isSheaf_functor (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology (functor A B r) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y S hS
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hS
  rw [Presieve.isSheafFor_arrows_iff]
  intro (x : ∀ j, (functor A B r).obj (op (𝒰.X j))) hx
  replace hx : ∀ i j (Z : Scheme.{0}) (a : Z ⟶ 𝒰.X i) (a' : Z ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = a' ≫ 𝒰.f j → (functor A B r).map a.op (x i) = (functor A B r).map a'.op (x j) := hx
  let g : Y ⟶ Spec (CommRingCat.of A) := 𝒰.glueMorphisms (fun j => (x j).1) fun i j =>
    congrArg Sigma.fst (hx i j _ _ _ pullback.condition)
  have hg : ∀ j, 𝒰.f j ≫ g = (x j).1 := fun j => 𝒰.ι_glueMorphisms _ _ j
  have hoi : ∀ j, IsOpenImmersion (bc A B g (𝒰.f j)) := fun j => isOpenImmersion_bc A B g (𝒰.f j)
  have hcov : ∀ p : ↥(pullback (str A B) g : Scheme.{0}), ∃ j q, bc A B g (𝒰.f j) q = p := by
    intro p
    obtain ⟨j, t, ht⟩ := 𝒰.exists_eq (pullback.snd (str A B) g p)
    have hr := (isPullback_bc A B g (𝒰.f j)).isoPullback_hom_fst
    have hmem : p ∈ Set.range (bc A B g (𝒰.f j)) := by
      rw [← hr, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso _).2, Set.image_univ,
        Scheme.Pullback.range_fst]
      exact ⟨t, ht⟩
    obtain ⟨q, hq⟩ := hmem
    exact ⟨j, q, hq⟩
  let J : ∀ j, (pullback (str A B) (𝒰.f j ≫ g)).IdealSheafData := fun j =>
    (x j).2.1.comap (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [hg j]))
  have hJ : ∀ i j (Z : Scheme.{0}) (a : Z ⟶ pullback (str A B) (𝒰.f i ≫ g))
      (a' : Z ⟶ pullback (str A B) (𝒰.f j ≫ g)),
      a ≫ bc A B g (𝒰.f i) = a' ≫ bc A B g (𝒰.f j) → (J i).comap a = (J j).comap a' := by
    intro i j Z a a' e
    have f1 : ∀ k, bc A B g (𝒰.f k) ≫ pullback.fst (str A B) g = pullback.fst _ _ := fun k =>
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    have f2 : ∀ k, bc A B g (𝒰.f k) ≫ pullback.snd (str A B) g = pullback.snd _ _ ≫ 𝒰.f k :=
      fun k => pullback.lift_snd _ _ _
    have p1 : ∀ k (b : Z ⟶ pullback (str A B) (𝒰.f k ≫ g)),
        (b ≫ pullback.map (str A B) (𝒰.f k ≫ g) (str A B) (x k).1 (𝟙 _) (𝟙 _) (𝟙 _)
          (by simp) (by simp [hg k])) ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ := by
      intro k b; simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
    have p2 : ∀ k (b : Z ⟶ pullback (str A B) (𝒰.f k ≫ g)),
        (b ≫ pullback.map (str A B) (𝒰.f k ≫ g) (str A B) (x k).1 (𝟙 _) (𝟙 _) (𝟙 _)
          (by simp) (by simp [hg k])) ≫ pullback.snd _ _ = b ≫ pullback.snd _ _ := by
      intro k b; simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
    have e1 : a ≫ pullback.fst _ _ = a' ≫ pullback.fst _ _ := by
      rw [← f1 i, ← f1 j, ← Category.assoc, e, Category.assoc]
    have e2 : (a ≫ pullback.snd _ _) ≫ 𝒰.f i = (a' ≫ pullback.snd _ _) ≫ 𝒰.f j := by
      rw [Category.assoc, Category.assoc, ← f2 i, ← f2 j, ← Category.assoc, e, Category.assoc]
    change ((x i).2.1.comap _).comap a = ((x j).2.1.comap _).comap a'
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
    refine comap_eq_of_map_eq (x i) (x j) _ _ (by rw [p1, p1, e1]) ?_
    rw [p2, p2]
    exact hx i j Z _ _ e2
  obtain ⟨I, hI⟩ := glue_exists (fun j : 𝒰.I₀ => pullback (str A B) (𝒰.f j ≫ g))
    (fun j : 𝒰.I₀ => bc A B g (𝒰.f j)) hoi hcov J hJ
  have good : Good A B r g I := good_local A B r 𝒰.X 𝒰.f (fun j => inferInstance)
    (fun y => 𝒰.exists_eq y) g I (fun j => by rw [hI j]; exact good_transport (hg j) (x j).2.2)
  have amal : ∀ j, (functor A B r).map (𝒰.f j).op ⟨g, ⟨I, good⟩⟩ = x j := fun j =>
    sigma_eq A B r (hg j) (hI j) _ (x j).2.2
  refine ⟨⟨g, ⟨I, good⟩⟩, amal, fun y' hy' => ?_⟩
  replace hy' : ∀ j, (functor A B r).map (𝒰.f j).op y' = x j := hy'
  have e : y'.1 = g := 𝒰.hom_ext _ _ fun j => (congrArg Sigma.fst (hy' j)).trans (hg j).symm
  obtain ⟨g', I', hI'⟩ := y'
  change g' = g at e
  subst e
  have : I' = I := by
    refine glue_ext (fun j : 𝒰.I₀ => pullback (str A B) (𝒰.f j ≫ g))
      (fun j : 𝒰.I₀ => bc A B g (𝒰.f j)) hoi hcov I' I fun j => ?_
    have := (hy' j).trans (amal j).symm
    exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp this).2)
  subst this
  rfl

end GlobalTheory.HilbAff
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertSchemeFunctor_isSheaf_zariski : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ), Presieve.IsSheaf Scheme.zariskiTopology (GlobalTheory.HilbAff.functor A B r) := by
  first | (exact @GlobalTheory.HilbAff.isSheaf_functor) | (exact GlobalTheory.HilbAff.isSheaf_functor) | (intros; apply GlobalTheory.HilbAff.isSheaf_functor <;> assumption)
end
