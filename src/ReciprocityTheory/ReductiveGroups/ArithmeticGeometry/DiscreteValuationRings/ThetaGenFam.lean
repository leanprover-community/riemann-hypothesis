import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenFlat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.HasGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GsScalJFK

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

noncomputable section

variable {R : Type} [CommRing R]

lemma toW_res {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) {V W : X.Opens} (h : W ≤ V) (r : R) :
    (X.presheaf.map (homOfLE h).op).hom (toW p V r) = toW p W r := by
  simp only [toW, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

lemma app_toW {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (f : Y ⟶ X) (W : X.Opens) (r : R) :
    (f.app W).hom (toW p W r) = toW (f ≫ p) (f ⁻¹ᵁ W) r := by
  simp only [toW, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE]
  erw [Scheme.Hom.appLE_comp_appLE]

lemma toW_congr {X : Scheme.{0}} {p p' : X ⟶ Spec (CommRingCat.of R)} (h : p = p') (W : X.Opens) (r : R) :
    toW p W r = toW p' W r := by subst h; rfl

lemma app_res {X Y : Scheme.{0}} (f : Y ⟶ X) {V W : X.Opens} (h : W ≤ V) (x : Γ(X, V)) :
    (Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom ((f.app V).hom x) =
      (f.app W).hom ((X.presheaf.map (homOfLE h).op).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

variable [IsDomain R]

theorem exists_div {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] {a : R} (ha : a ≠ 0)
    {J : Ideal R} (hJ : J ≤ Ideal.span {a})
    (V : X.Opens) (x : Γ(X, V)) (hx : (pullback.fst p (tq J)).app V x = 0) :
    ∃ g : Γ(X, V), x = toW p V a * g := by
  classical
  set π := pullback.fst p (tq J)
  let ι := {W : X.affineOpens // (W : X.Opens) ≤ V}
  let U : ι → X.Opens := fun W => W.1
  have hloc : ∀ W : ι, ∃ g : Γ(X, U W), (X.presheaf.map (homOfLE W.2).op).hom x = toW p (U W) a * g := by
    intro W
    have h0 : (π.app (U W)).hom ((X.presheaf.map (homOfLE W.2).op).hom x) = 0 := by
      rw [← app_res, hx, map_zero]
    have hm := Ideal.map_mono hJ ((app_fst_tq p J (U W) W.1.2).2 _ h0)
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hm
    obtain ⟨g, hg⟩ := hm
    exact ⟨g, by rw [← hg, mul_comm]⟩
  choose g hg using hloc
  have hcover : V ≤ iSup U := by
    intro y hy
    obtain ⟨W, hW, hyW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWV⟩, hyW⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U g := by
    intro i j
    show (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (g i) =
      (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (g j)
    rw [← sub_eq_zero]
    apply toW_mul_eq_zero p _ ha
    rw [mul_sub]
    have e1 := congrArg (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (hg i)
    have e2 := congrArg (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (hg j)
    rw [map_mul, toW_res, ← CommRingCat.comp_apply, ← Functor.map_comp] at e1 e2
    rw [sub_eq_zero]
    exact e1.symm.trans e2
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf U V (fun i => homOfLE i.2) hcover g hcompat
  refine ⟨s, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf U V (fun i => homOfLE i.2) hcover
  intro i
  show (X.presheaf.map (homOfLE i.2).op).hom x = (X.presheaf.map (homOfLE i.2).op).hom (toW p V a * (show Γ(X, V) from s))
  rw [hg i, map_mul, toW_res]
  exact congrArg _ (hs i).symm

end

end ReciprocityTheory.ChartRestriction.G.DVR.TG

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

noncomputable section

variable {R : Type} [CommRing R]

lemma app_toW_of_mem {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (W : X.Opens)
    {r : R} (hr : r ∈ J) : (pullback.fst p (tq J)).app W (toW p W r) = 0 := by
  have e1 : (pullback.fst p (tq J)).app W (toW p W r) =
      ((pullback.snd p (tq J) ≫ tq J).appLE ⊤ (pullback.fst p (tq J) ⁻¹ᵁ W) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [toW, RingHom.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE]
    erw [Scheme.Hom.appLE_comp_appLE]
    rw [appLE_of_eq pullback.condition]
  have e2 : (pullback.snd p (tq J) ≫ tq J).appLE ⊤ (pullback.fst p (tq J) ⁻¹ᵁ W) le_top =
      (tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) le_rfl ≫
        (pullback.snd p (tq J)).appLE (tq J ⁻¹ᵁ ⊤) (pullback.fst p (tq J) ⁻¹ᵁ W) le_top := by
    erw [Scheme.Hom.appLE_comp_appLE]
  have e3 : (tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) le_rfl =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv := by
    rw [Scheme.Hom.appLE_eq_app, ← Scheme.Hom.appTop,
      (Iso.eq_comp_inv _).2 (Scheme.ΓSpecIso_naturality _), Category.assoc]
  have eR : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r := by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
  have e4 : ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = 0 := by
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, eR]
    erw [Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  rw [e1, e2, CommRingCat.comp_apply, e3]
  erw [e4, map_zero]

variable [IsDomain R]

set_option maxHeartbeats 400000 in

theorem vanish_of_mul {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] {a : R} (ha : a ≠ 0)
    (e : ℕ) {J₁ J₂ : Ideal R} (h1 : J₁ ≤ Ideal.span {a ^ (e + 2)}) (h2 : a ^ (e + 1) ∈ J₂)
    (ι : pullback p (tq J₂) ⟶ pullback p (tq J₁)) (hι : ι ≫ pullback.fst p (tq J₁) = pullback.fst p (tq J₂))
    (V : (pullback p (tq J₁)).Opens) (y : Γ(pullback p (tq J₁), V))
    (hy : toW (pullback.fst p (tq J₁) ≫ p) V a * y = 0) :
    (ι.app V) y = 0 := by
  set π₁ := pullback.fst p (tq J₁)
  set π₂ := pullback.fst p (tq J₂)
  have : IsClosedImmersion (tq J₁) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion π₁ := inferInstance
  refine TopCat.Presheaf.section_ext (pullback p (tq J₂)).sheaf _ _ 0 fun z hz => ?_

  have hemb : Topology.IsEmbedding π₁.base := π₁.isClosedEmbedding.isEmbedding
  obtain ⟨V₀, hV₀, hV₀e⟩ := hemb.isInducing.isOpen_iff.1 V.isOpen
  have hz0 : π₁.base (ι.base z) ∈ V₀ := by
    have : ι.base z ∈ (π₁.base ⁻¹' V₀) := by rw [hV₀e]; exact hz
    exact this
  obtain ⟨W, hW, hzW, hWV₀⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show π₁.base (ι.base z) ∈ (⟨V₀, hV₀⟩ : X.Opens) from hz0)
  have hWV : π₁ ⁻¹ᵁ W ≤ V := by
    intro u hu
    have : u ∈ π₁.base ⁻¹' V₀ := hWV₀ hu
    rw [hV₀e] at this; exact this

  obtain ⟨hs, hk⟩ := app_fst_tq p J₁ W hW
  obtain ⟨yt, hyt⟩ := hs (((pullback p (tq J₁)).presheaf.map (homOfLE hWV).op).hom y)
  have hay : π₁.app W (toW p W a * yt) = 0 := by
    rw [map_mul, hyt, app_toW, ← toW_res (π₁ ≫ p) hWV, ← map_mul, hy, map_zero]
  have hm := Ideal.map_mono h1 (hk _ hay)
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hm
  obtain ⟨c, hc⟩ := hm
  have hyt' : yt = toW p W (a ^ (e + 1)) * c := by
    apply sub_eq_zero.1
    apply toW_mul_eq_zero p W ha
    rw [mul_sub, ← hc, map_pow, map_pow, pow_succ' _ (e + 1)]
    ring

  have hW2 : π₂ ⁻¹ᵁ W ≤ ι ⁻¹ᵁ V := by
    intro u hu
    apply hWV
    show π₁.base (ι.base u) ∈ W
    rw [← Scheme.Hom.comp_apply, hι]; exact hu
  have hW2' : π₂ ⁻¹ᵁ W ≤ ι ⁻¹ᵁ (π₁ ⁻¹ᵁ W) := by
    intro u hu
    show π₁.base (ι.base u) ∈ W
    rw [← Scheme.Hom.comp_apply, hι]; exact hu
  have hzW2 : z ∈ π₂ ⁻¹ᵁ W := by
    show π₂.base z ∈ W
    rw [← hι, Scheme.Hom.comp_apply]; exact hzW
  have e5 : ((pullback p (tq J₂)).presheaf.map (homOfLE hW2).op).hom ((ι.app V) y) = (π₂.app W) yt := by
    have a1 : ((pullback p (tq J₂)).presheaf.map (homOfLE hW2).op).hom ((ι.app V) y) =
        (ι.appLE V (π₂ ⁻¹ᵁ W) hW2) y := by
      rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply]
      erw [Scheme.Hom.appLE_map]
    have a2 : (ι.appLE V (π₂ ⁻¹ᵁ W) hW2) y =
        (ι.appLE (π₁ ⁻¹ᵁ W) (π₂ ⁻¹ᵁ W) hW2') (((pullback p (tq J₁)).presheaf.map (homOfLE hWV).op).hom y) := by
      rw [← CommRingCat.comp_apply]
      erw [Scheme.Hom.map_appLE]
    have a3 : (ι.appLE (π₁ ⁻¹ᵁ W) (π₂ ⁻¹ᵁ W) hW2') ((π₁.app W) yt) = (π₂.app W) yt := by
      rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply]
      erw [Scheme.Hom.appLE_comp_appLE]
      rw [appLE_of_eq hι, Scheme.Hom.app_eq_appLE]
    rw [a1, a2, ← hyt, a3]
  have hzero : ((pullback p (tq J₂)).presheaf.map (homOfLE hW2).op).hom ((ι.app V) y) = 0 := by
    rw [e5, hyt', map_mul, app_toW_of_mem p J₂ W h2, zero_mul]
  show (pullback p (tq J₂)).presheaf.germ _ z hz ((ι.app V) y) = (pullback p (tq J₂)).presheaf.germ _ z hz 0
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hW2) z hzW2, hzero, map_zero, map_zero]

end

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

lemma resTop_scal {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens)
    (r : R) : resTop W (scal p r) = toW p W r := rfl

theorem sec_div {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) [Flat p]
    {M : LB Y} (s : LB.Sec M) {a : R} (ha : a ≠ 0) {J : Ideal R} (hJ : J ≤ Ideal.span {a})
    (h0 : ∀ j, (pullback.fst p (tq J)).app _ (s.f j) = 0) :
    ∃ g : LB.Sec M, ∀ j, s.f j = toW p _ a * g.f j := by
  choose g hg using fun j => exists_div p ha hJ (M.U j) (s.f j) (h0 j)
  refine ⟨⟨g, fun i j => ?_⟩, hg⟩
  apply sub_eq_zero.1
  apply toW_mul_eq_zero p _ ha
  have c := s.compat i j
  rw [hg i, hg j, map_mul, map_mul, toW_res, toW_res] at c
  rw [mul_sub, sub_eq_zero, c]
  ring

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma thickMap_fst (e : ℕ) : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left := by
  unfold thickMap fstG pullback.map
  simp only [Over.homMk_left]
  erw [pullback.lift_fst]
  try simp

lemma pG_struct {e : ℕ} (g : GtCoord I D.toPre e G) :
    g.pG.left ≫ D.toPre.P.A.hom = (fstG I e G).left ≫ G.hom :=
  (Over.w g.pG).trans (Over.w (fstG I e G)).symm

end ReciprocityTheory.ChartRestriction.G.DVR.TG

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

lemma app_eq_zero_of_comp {X Y Z : Scheme.{0}} {f : X ⟶ Z} {g : X ⟶ Y} {h : Y ⟶ Z} (hf : g ≫ h = f)
    (W : Z.Opens) (x : Γ(Z, W)) (hx : g.app (h ⁻¹ᵁ W) (h.app W x) = 0) : f.app W x = 0 := by
  subst hf
  first
  | exact hx
  | (rw [Scheme.comp_app]; exact hx)
  | (simp only [Scheme.comp_app, CommRingCat.comp_apply]; exact hx)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def thickO (e : ℕ) : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶
    (Over.map (thick R I (e + 1))).obj (thickObj R I (e + 1) G) :=
  Over.homMk (thickMap R I e G) (by
    show thickMap R I e G ≫ pullback.snd G.hom (thick R I (e + 1)) ≫ thick R I (e + 1) =
      pullback.snd G.hom (thick R I e) ≫ thick R I e
    rw [thickMap, pullback.lift_snd_assoc, Category.assoc, thickTrans_comp])

lemma thickO_pG (U : UnifPre I D A G) (e : ℕ) : thickO e ≫ (U.gt (e + 1)).pG = (U.gt e).pG :=
  Over.OverMorphism.ext (U.gt_q e)

lemma Oφ_thick (U : UnifPre I D A G) (e : ℕ) (α : D.toPre.X) (k : Fin 4) :
    thickMap R I e G ≫ D.toPre.Oφ (U.gt (e + 1)).pG α k = D.toPre.Oφ (U.gt e).pG α k := by
  have := WeightPf.Oφ_comp (thickO (G := G) (I := I) e) (U.gt (e + 1)).pG α k
  rw [thickO_pG] at this
  exact this

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

lemma appLE_res {X Y : Scheme.{0}} (i0 : X ⟶ Y) {V1 W : Y.Opens} {V0 : X.Opens} (hV : V0 ≤ i0 ⁻¹ᵁ V1)
    (h1 : V1 ≤ W) (h0 : V0 ≤ i0 ⁻¹ᵁ W) (y : Γ(Y, W)) :
    (i0.appLE V1 V0 hV) ((Y.presheaf.map (homOfLE h1).op).hom y) =
      (X.presheaf.map (homOfLE h0).op).hom ((i0.app W).hom y) := by
  have e1 := i0.map_appLE hV (homOfLE h1).op
  have e2 : i0.app W ≫ X.presheaf.map (homOfLE h0).op = i0.appLE W V0 h0 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  calc (i0.appLE V1 V0 hV) ((Y.presheaf.map (homOfLE h1).op).hom y)
      = (Y.presheaf.map (homOfLE h1).op ≫ i0.appLE V1 V0 hV).hom y := rfl
    _ = (i0.appLE W V0 h0).hom y := by rw [e1]
    _ = (i0.app W ≫ X.presheaf.map (homOfLE h0).op).hom y := by rw [e2]
    _ = _ := rfl

lemma appLE_pull {X Y Z : Scheme.{0}} (i0 : X ⟶ Y) (m : Y ⟶ Z) (m' : X ⟶ Z) (h : i0 ≫ m = m')
    {V1 : Y.Opens} {V0 : X.Opens} (hV : V0 ≤ i0 ⁻¹ᵁ V1) {W : Z.Opens} (h1 : V1 ≤ m ⁻¹ᵁ W)
    (h0 : V0 ≤ m' ⁻¹ᵁ W) (x : Γ(Z, W)) :
    (i0.appLE V1 V0 hV) ((Y.presheaf.map (homOfLE h1).op).hom ((m.app W).hom x)) =
      (X.presheaf.map (homOfLE h0).op).hom ((m'.app W).hom x) := by
  subst h
  have e1 : m.app W ≫ Y.presheaf.map (homOfLE h1).op = m.appLE W V1 h1 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  have e2 : (i0 ≫ m).app W ≫ X.presheaf.map (homOfLE h0).op = (i0 ≫ m).appLE W V0 h0 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  calc (i0.appLE V1 V0 hV) ((Y.presheaf.map (homOfLE h1).op).hom ((m.app W).hom x))
      = ((m.app W ≫ Y.presheaf.map (homOfLE h1).op) ≫ i0.appLE V1 V0 hV).hom x := rfl
    _ = ((i0 ≫ m).appLE W V0 h0).hom x := by rw [e1, Scheme.Hom.appLE_comp_appLE]
    _ = ((i0 ≫ m).app W ≫ X.presheaf.map (homOfLE h0).op).hom x := by rw [e2]
    _ = _ := rfl

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def expL (U : UnifPre I D A G) (e : ℕ) (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι))
    (j₁ : Fin 1 → U.LG.L.ι) (S : Finset D.toPre.X) (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι)
    (σ : H0 U.LG.L 1) : Γ((thickObj R I e G).left, U.expW e p j₁ S jf jt) :=
  (res (inf_le_left.trans inf_le_left :
      U.expW e p j₁ S jf jt ≤ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
        (U.LG.L.pull (fstG I e G).left)).U p) ((U.w e).s p)).val ^ 1 *
    ((thickObj R I e G).left.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
      U.expW e p j₁ S jf jt ≤
        (fstG I e G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁)).op).hom
      (((fstG I e G).left.app _).hom (σ.f j₁))

def expR (U : UnifPre I D A G) (e : ℕ) (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι))
    (j₁ : Fin 1 → U.LG.L.ι) (S : Finset D.toPre.X) (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι)
    (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) : Γ((thickObj R I e G).left, U.expW e p j₁ S jf jt) :=
  ∑ α ∈ S.attach,
    ((thickObj R I e G).left.presheaf.map (homOfLE (U.expW_le_f e p j₁ jf jt α.2)).op).hom
        (((U.gt e).pG.left.app _).hom ((f α.1).f (jf α.1))) *
      (res (U.expWeight_le_chart_weight e p j₁ jf jt α.2) (((U.gt e).t α.1).s (jt α.1))).val

set_option maxHeartbeats 1000000 in

theorem expandsAt_of_div (U : UnifPre I D A G) [Flat G.hom] {ϖ : R} (hϖ : ϖ ≠ 0) (hI : I = Ideal.span {ϖ})
    (σ τ : H0 U.LG.L 1) (hστ : ∀ j, σ.f j = toW G.hom _ ϖ * τ.f j)
    (f g : ∀ α, D.toPre.SecB 1 α) (hfg : ∀ α j, (f α).f j = toW D.toPre.P.A.hom _ ϖ * (g α).f j)
    (e : ℕ) (h : U.ExpandsAt (e + 1) 1 σ f) : U.ExpandsAt e 1 τ g := by
  classical
  obtain ⟨S, hout, hmain⟩ := h
  have hι : thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
    thickMap_fst e
  have hq : thickMap R I e G ≫ (U.gt (e + 1)).pG.left = (U.gt e).pG.left := U.gt_q e
  have hJ1 : I ^ (e + 1 + 1) ≤ Ideal.span {ϖ ^ (e + 2)} := by
    rw [hI, Ideal.span_singleton_pow]
  have hJ2 : ϖ ^ (e + 1) ∈ I ^ (e + 1) := by
    rw [hI, Ideal.span_singleton_pow]; exact Ideal.subset_span rfl
  have van : ∀ (V : (thickObj R I (e + 1) G).left.Opens) (y : Γ((thickObj R I (e + 1) G).left, V)),
      toW (X := (thickObj R I (e + 1) G).left) ((fstG I (e + 1) G).left ≫ G.hom) V ϖ * y = 0 →
        (thickMap R I e G).app V y = 0 :=
    fun V y hy => vanish_of_mul G.hom hϖ e hJ1 hJ2 (thickMap R I e G) hι V y hy
  refine ⟨S, fun α hα j => ?_, fun p j₁ jf jt hj hcoh => ?_⟩
  · have h1 := hout α hα j
    erw [hfg α j, map_mul, app_toW, toW_congr (pG_struct _)] at h1
    exact app_eq_zero_of_comp hq _ _ (van _ _ h1)
  ·
    have hfam : ∀ z, (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2))) z =
        thickMap R I e G ≫ (Sum.elim (fun _ : PUnit.{1} => (U.gt (e + 1)).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt (e + 1)).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt (e + 1)).pG a.1.1 a.2))) z := by
      rintro (z | z | z)
      · exact hq.symm
      · show (U.gt e).pG.left ≫ D.toPre.famφB z.1.1 z.2 =
          thickMap R I e G ≫ (U.gt (e + 1)).pG.left ≫ D.toPre.famφB z.1.1 z.2
        rw [← Category.assoc, hq]
      · exact (Oφ_thick U e z.1.1 z.2).symm
    have hcoh1 := fun a b (hab : (Sum.elim (fun _ : PUnit.{1} => (U.gt (e + 1)).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt (e + 1)).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt (e + 1)).pG a.1.1 a.2))) a =
        (Sum.elim (fun _ : PUnit.{1} => (U.gt (e + 1)).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt (e + 1)).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt (e + 1)).pG a.1.1 a.2))) b) =>
      hcoh a b (by rw [hfam a, hfam b, hab])
    have E := hmain p j₁ jf jt hj hcoh1
    have E' : expL U (e + 1) p j₁ S jf jt σ = expR U (e + 1) p j₁ S jf jt f := E
    show expL U e p j₁ S jf jt τ = expR U e p j₁ S jf jt g

    have hι' : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left := thickMap_fst e
    have hV : U.expW e p j₁ S jf jt ≤ thickMap R I e G ⁻¹ᵁ U.expW (e + 1) p j₁ S jf jt := by
      intro x hx
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hx
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · exact wchart_le_preimage D.toPre.P.L (thickMap R I e G) (fun _ => (U.gt (e + 1)).pG.left)
          (fun _ => (U.gt e).pG.left) (fun _ => hq.symm) p.1 h1
      · exact wchart_le_preimage U.LG.L (thickMap R I e G) (fun _ => (fstG I (e + 1) G).left)
          (fun _ => (fstG I e G).left) (fun _ => hι'.symm) p.2 h2
      · show (fstG I (e + 1) G).left.base ((thickMap R I e G).base x) ∈
          LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁
        rw [← Scheme.Hom.comp_apply, hι']; exact h3
      · refine WeightPf.mem_finset_inf _ _ _ fun α hα => ?_
        have hx' := WeightPf.mem_of_finset_inf h4 hα
        refine ⟨?_, wchart_le_preimage D.toPre.P.L (thickMap R I e G) (D.toPre.Oφ (U.gt (e + 1)).pG α)
          (D.toPre.Oφ (U.gt e).pG α) (fun k => (Oφ_thick U e α k).symm) (jt α) hx'.2⟩
        show (U.gt (e + 1)).pG.left.base ((thickMap R I e G).base x) ∈
          LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α)
        rw [← Scheme.Hom.comp_apply, hq]; exact hx'.1
    set c1 := toW (X := (thickObj R I (e + 1) G).left) ((fstG I (e + 1) G).left ≫ G.hom)
      (U.expW (e + 1) p j₁ S jf jt) ϖ with hc1
    have hL1 : expL U (e + 1) p j₁ S jf jt σ = c1 * expL U (e + 1) p j₁ S jf jt τ := by
      simp only [expL]
      erw [hστ j₁, map_mul, map_mul, app_toW, toW_res]
      ring
    have hR1 : expR U (e + 1) p j₁ S jf jt f = c1 * expR U (e + 1) p j₁ S jf jt g := by
      simp only [expR, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      erw [hfg α.1 (jf α.1), map_mul, map_mul, app_toW, toW_res, toW_congr (pG_struct _)]
      ring
    have hdiff : c1 * (expL U (e + 1) p j₁ S jf jt τ - expR U (e + 1) p j₁ S jf jt g) = 0 := by
      rw [mul_sub, ← hL1, ← hR1, E', sub_self]
    have hvan := van _ _ hdiff
    have hres : (thickMap R I e G).appLE _ _ hV
        (expL U (e + 1) p j₁ S jf jt τ - expR U (e + 1) p j₁ S jf jt g) = 0 := by
      show ((thickMap R I e G).app _ ≫ (thickObj R I e G).left.presheaf.map (homOfLE hV).op).hom _ = 0
      rw [CommRingCat.comp_apply, hvan, map_zero]
    have h0w : U.expW e p j₁ S jf jt ≤ thickMap R I e G ⁻¹ᵁ
        (LB.div (D.toPre.P.L.pull (U.gt (e + 1)).pG.left) (U.LG.L.pull (fstG I (e + 1) G).left)).U p :=
      fun x hx => (inf_le_left.trans inf_le_left :
        U.expW (e + 1) p j₁ S jf jt ≤ (LB.div (D.toPre.P.L.pull (U.gt (e + 1)).pG.left)
          (U.LG.L.pull (fstG I (e + 1) G).left)).U p) (hV hx)
    have hL2 : (thickMap R I e G).appLE _ _ hV (expL U (e + 1) p j₁ S jf jt τ) = expL U e p j₁ S jf jt τ := by
      simp only [expL, map_mul, map_pow]
      congr 1
      · congr 1
        rw [WeightPf.res_val, appLE_res (thickMap R I e G) hV _ h0w]
        exact congrArg Units.val (U.w_compat e p (U.expW e p j₁ S jf jt) h0w (inf_le_left.trans inf_le_left))
      · exact appLE_pull _ _ _ hι' hV _ _ _
    have ht : ∀ α : S, (thickMap R I e G).appLE _ _ hV
        (res (U.expWeight_le_chart_weight (e + 1) p j₁ jf jt α.2) (((U.gt (e + 1)).t α.1).s (jt α.1))).val =
        (res (U.expWeight_le_chart_weight e p j₁ jf jt α.2) (((U.gt e).t α.1).s (jt α.1))).val := by
      intro α
      have hfun : (fun k => thickMap R I e G ≫ D.toPre.Oφ (U.gt (e + 1)).pG α.1 k) =
          D.toPre.Oφ (U.gt e).pG α.1 := funext (Oφ_thick U e α.1)
      have hW : U.expW e p j₁ S jf jt ≤
          LB.wchart D.toPre.P.L (fun k => thickMap R I e G ≫ D.toPre.Oφ (U.gt (e + 1)).pG α.1 k) (jt α.1) := by
        rw [hfun]; exact U.expWeight_le_chart_weight e p j₁ jf jt α.2
      have hcohE : ∀ k1 k2, D.toPre.Oφ (U.gt e).pG α.1 k1 = D.toPre.Oφ (U.gt e).pG α.1 k2 →
          jt α.1 k1 = jt α.1 k2 :=
        fun k1 k2 h => hcoh (Sum.inr (Sum.inr (α, k1))) (Sum.inr (Sum.inr (α, k2))) h
      have C2 := LBVal.corr_val D.toPre.P.L _ _ _ _ _ _ (U.gt_t e α.1) (jt α.1) (jt α.1)
        (fun k1 k2 h => hcohE k1 k2 ((Oφ_thick U e α.1 k1).symm.trans (h.trans (Oφ_thick U e α.1 k2)))) hcohE
        (fun k k' h => hcohE k k' ((Oφ_thick U e α.1 k).symm.trans h)) (U.expW e p j₁ S jf jt)
        (le_inf hW (U.expWeight_le_chart_weight e p j₁ jf jt α.2))
      show ((thickObj R I (e + 1) G).left.presheaf.map (homOfLE (U.expWeight_le_chart_weight (e + 1) p j₁ jf jt α.2)).op ≫
          (thickMap R I e G).appLE _ _ hV).hom (((U.gt (e + 1)).t α.1).s (jt α.1)).val =
        ((thickObj R I e G).left.presheaf.map (homOfLE (U.expWeight_le_chart_weight e p j₁ jf jt α.2)).op).hom
          (((U.gt e).t α.1).s (jt α.1)).val
      erw [Scheme.Hom.map_appLE]
      rw [← LBVal.pullGen_val (L := D.toPre.P.L) _ _ ((U.gt (e + 1)).t α.1) (thickMap R I e G) (jt α.1) _ hW]
      exact C2
    have hR2 : (thickMap R I e G).appLE _ _ hV (expR U (e + 1) p j₁ S jf jt g) = expR U e p j₁ S jf jt g := by
      simp only [expR, map_sum, map_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      congr 1
      · exact appLE_pull _ _ _ hq hV _ _ _
      · exact ht α
    rw [map_sub, hL2, hR2, sub_eq_zero] at hres
    exact hres

end ReciprocityTheory.ChartRestriction.G.DVR.TG

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma flat_G (U : UnifPre I D A G) : Flat G.hom := by
  haveI := U.smooth
  exact AlgebraicGeometry.instFlatOfSmooth _

lemma flat_B : Flat D.toPre.P.A.hom := by
  haveI := D.toPre.P.smoothDim
  haveI : AlgebraicGeometry.Smooth D.toPre.P.A.hom :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth D.toPre.P.g _
  exact AlgebraicGeometry.instFlatOfSmooth _

theorem expandsAt_scale (U : UnifPre I D A G) (c : R) (τ τ' : H0 U.LG.L 1)
    (hτ : ∀ j, τ'.f j = toW G.hom _ c * τ.f j)
    (g g' : ∀ α, D.toPre.SecB 1 α) (hg : ∀ α j, (g' α).f j = toW D.toPre.P.A.hom _ c * (g α).f j)
    (e : ℕ) (h : U.ExpandsAt e 1 τ g) : U.ExpandsAt e 1 τ' g' := by
  obtain ⟨S, hout, hmain⟩ := h
  refine ⟨S, fun α hα j => ?_, fun p j₁ jf jt hj hcoh => ?_⟩
  · erw [hg α j, map_mul, hout α hα j, mul_zero]
  · have E : expL U e p j₁ S jf jt τ = expR U e p j₁ S jf jt g := hmain p j₁ jf jt hj hcoh
    show expL U e p j₁ S jf jt τ' = expR U e p j₁ S jf jt g'
    set c1 := toW (X := (thickObj R I e G).left) ((fstG I e G).left ≫ G.hom) (U.expW e p j₁ S jf jt) c
    have hL : expL U e p j₁ S jf jt τ' = c1 * expL U e p j₁ S jf jt τ := by
      simp only [expL]
      erw [hτ j₁, map_mul, map_mul, app_toW, toW_res]
      ring
    have hR : expR U e p j₁ S jf jt g' = c1 * expR U e p j₁ S jf jt g := by
      simp only [expR, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      erw [hg α.1 (jf α.1), map_mul, map_mul, app_toW, toW_res, toW_congr (pG_struct _)]
      ring
    rw [hL, hR, E]

theorem expand_div_one (U : UnifPre I D A G) (hWI : WeightIndepSt) {ϖ : R} (hϖ : ϖ ≠ 0)
    (hI : I = Ideal.span {ϖ}) (σ τ : H0 U.LG.L 1) (hστ : ∀ j, σ.f j = toW G.hom _ ϖ * τ.f j)
    (f : ∀ α, D.toPre.SecB 1 α) (hf : ∀ e, U.ExpandsAt e 1 σ f) :
    ∃ g : ∀ α, D.toPre.SecB 1 α, (∀ α j, (f α).f j = toW D.toPre.P.A.hom _ ϖ * (g α).f j) ∧
      ∀ e, U.ExpandsAt e 1 τ g := by
  have := flat_G U
  have := flat_B (D := D)
  have hϖI : ϖ ∈ I ^ (0 + 1) := by rw [hI, zero_add, pow_one]; exact Ideal.mem_span_singleton_self ϖ
  have hσ0 : ∀ j, ((fstG I 0 G).left.app _).hom (σ.f j) = 0 := by
    intro j
    rw [hστ, map_mul]
    erw [app_toW_of_mem G.hom (I ^ (0 + 1)) _ hϖI, zero_mul]
  have hpG := hWI R I D A G U 0 1 σ f hσ0 (hf 0)
  have hB : ∀ α j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ ((f α).f j) = 0 := by
    intro α j
    have := (U.gt 0).q_flat
    have := (U.gt 0).q_surj
    apply app_injective_of_flat_surj (U.gt 0).q.left
    rw [map_zero]
    have h := hpG α j
    have e : (U.gt 0).pG.left = (U.gt 0).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R I 0) := rfl
    rw [e, Scheme.Hom.comp_app] at h
    exact h
  choose g hg using fun α => sec_div D.toPre.P.A.hom (f α) hϖ (J := I ^ (0 + 1))
    (by rw [hI, zero_add, pow_one]) (hB α)
  exact ⟨g, hg, fun e => expandsAt_of_div U hϖ hI σ τ hστ f g hg e (hf (e + 1))⟩

theorem expand_div_pow (U : UnifPre I D A G) (hWI : WeightIndepSt) {ϖ : R} (hϖ : ϖ ≠ 0)
    (hI : I = Ideal.span {ϖ}) (n : ℕ) : ∀ (σ τ : H0 U.LG.L 1), (∀ j, σ.f j = toW G.hom _ (ϖ ^ n) * τ.f j) →
    ∀ (f : ∀ α, D.toPre.SecB 1 α), (∀ e, U.ExpandsAt e 1 σ f) →
    ∃ g : ∀ α, D.toPre.SecB 1 α, (∀ α j, (f α).f j = toW D.toPre.P.A.hom _ (ϖ ^ n) * (g α).f j) ∧
      ∀ e, U.ExpandsAt e 1 τ g := by
  induction n with
  | zero =>
    intro σ τ hστ f hf
    refine ⟨f, fun α j => by rw [pow_zero, map_one, _root_.one_mul], fun e => ?_⟩
    have : σ = τ := SecOps.sec_ext fun j => by rw [hστ, pow_zero, map_one, _root_.one_mul]
    rw [← this]; exact hf e
  | succ n ih =>
    intro σ τ hστ f hf
    let σ' : H0 U.LG.L 1 := SecOps.secScale (scal G.hom (ϖ ^ n)) τ
    have h1 : ∀ j, σ.f j = toW G.hom _ ϖ * σ'.f j := fun j => by
      rw [hστ]
      show _ = _ * (toW G.hom _ (ϖ ^ n) * τ.f j)
      rw [pow_succ', map_mul, _root_.mul_assoc]
    obtain ⟨g1, hg1, he1⟩ := expand_div_one U hWI hϖ hI σ σ' h1 f hf
    obtain ⟨g, hg, he⟩ := ih σ' τ (fun j => rfl) g1 he1
    refine ⟨g, fun α j => ?_, he⟩
    rw [hg1, hg, pow_succ', map_mul, _root_.mul_assoc]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

def pullSec' {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k) :
    LB.Sec (LB.LinComb L φ' ε) := by
  have e : φ' = fun k => h ≫ φ k := funext hφ
  subst e
  exact pullSec L φ ε s h

lemma pullSec'_f {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k)
    (j : K → L.ι) :
    (pullSec' L φ ε s h φ' hφ).f j =
      (Z.presheaf.map (homOfLE (wchart_le_preimage L h φ φ' hφ j)).op).hom ((h.app _).hom (s.f j)) := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  rfl

lemma map_inj_of_le_ge {X : Scheme.{0}} {V W : X.Opens} (h1 : W ≤ V) (h2 : V ≤ W) {a b : Γ(X, V)}
    (h : (X.presheaf.map (homOfLE h1).op).hom a = (X.presheaf.map (homOfLE h1).op).hom b) : a = b := by
  obtain rfl : W = V := le_antisymm h1 h2
  have e : homOfLE h1 = 𝟙 W := Subsingleton.elim _ _
  rw [e] at h
  simpa using h

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def secK (U : UnifPre I D A G) (s : H0 U.LG.L 1) : U.SecK 1 :=
  pullSec' U.LG.L _ _ s (pullback.fst G.hom (jK R)) _ (fun _ => (Category.comp_id _).symm)

lemma secK_rel (U : UnifPre I D A G) (s : H0 U.LG.L 1) :
    GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) (secK U s)
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) s (pullback.fst G.hom (jK R)) 1 := by
  intro j₁ j₂ hc
  have hj : j₁ = j₂ := funext fun k => by
    rw [Subsingleton.elim k 0]
    exact hc (Sum.inl 0) (Sum.inr 0) (Category.comp_id _).symm
  subst hj
  rw [secK, pullSec'_f]
  have h1 : resTop (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j₁ ⊓
      LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R) ≫ 𝟙 G.left) j₁)
      (1 : Γ(pullback G.hom (jK R), ⊤)) = 1 := map_one _
  rw [h1, _root_.one_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem sec_eq_of_secScal (U : UnifPre I D A G) [Flat G.hom] (s σ : H0 U.LG.L 1) (sK : U.SecK 1) (r : R)
    (h1 : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) sK
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) s (pullback.fst G.hom (jK R)) 1)
    (h2 : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) sK
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) σ (pullback.fst G.hom (jK R))
      (scal (pullback.snd G.hom (jK R) ≫ jK R) r)) :
    ∀ j, σ.f j = toW G.hom _ r * s.f j := by
  intro (j : Fin 1 → U.LG.L.ι)
  have hc : LB.Coh U.LG.L (Sum.elim (fun _ : Fin 1 => pullback.fst G.hom (jK R))
      (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k)) (Sum.elim j j) := by
    intro a b _
    rcases a with a | a <;> rcases b with b | b <;> exact congrArg j (Subsingleton.elim _ _)
  have e1 := h1 j j hc
  have e2 := h2 j j hc
  have h1' : resTop (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j ⊓
      LB.wchart U.LG.L (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) j)
      (1 : Γ(pullback G.hom (jK R), ⊤)) = 1 := map_one _
  rw [h1', _root_.one_mul] at e1
  rw [← e1] at e2
  have hle : pullback.fst G.hom (jK R) ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j ≤
      LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j ⊓
        LB.wchart U.LG.L (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) j :=
    fun x hx => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k⟩
  apply app_fst_jF_injective G.hom
  apply map_inj_of_le_ge (inf_le_right.trans (wchart_comp_le _ _ j)) hle
  refine e2.trans ?_
  have e3 : (((pullback.fst G.hom (jK R)).app (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)).hom
      (toW G.hom (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) r *
        (show Γ(G.left, LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) from s.f j))) =
      toW (pullback.fst G.hom (jK R) ≫ G.hom) _ r *
        ((pullback.fst G.hom (jK R)).app (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)).hom
          (show Γ(G.left, LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) from s.f j) := by
    rw [map_mul, app_toW]
  erw [e3, map_mul, toW_res, resTop_scal, toW_congr pullback.condition.symm]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

section Rel

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def SecCorr (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (x : LB.Sec (LB.LinComb L φ' ε')) : Prop :=
  ∀ (j : K → L.ι) (j' : K' → L.ι), LB.Coh L φ j → LB.Coh L φ' j' → (∀ k k', φ k = φ' k' → j k = j' k') →
    rs (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (s.f j) =
      rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (x.f j')

private lemma exists_coh_extending_of_mem_wchart (hL : L.IsLB) (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j' : K' → L.ι)
    (hj' : LB.Coh L φ' j') (y : Y) (hy : y ∈ LB.wchart L φ' j') :
    ∃ j : K → L.ι, LB.Coh L φ j ∧ (∀ k k', φ k = φ' k' → j k = j' k') ∧ y ∈ LB.wchart L φ j := by
  classical
  have memw : ∀ {T : Type} [Fintype T] (ψ : T → (Y ⟶ X)) (i : T → L.ι),
      y ∈ LB.wchart L ψ i ↔ ∀ t, (ψ t).base y ∈ L.U (i t) := by
    intro T _ ψ i
    first
    | exact Set.mem_iInter
    | simp [LB.wchart]
  have hcov : ∀ x : X, ∃ i, x ∈ L.U i := by
    intro x
    have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  let g : (Y ⟶ X) → L.ι := fun ψ =>
    if h : ∃ k', φ' k' = ψ then j' h.choose else (hcov (ψ.base y)).choose
  refine ⟨fun k => g (φ k), ?_, ?_, ?_⟩
  · intro k₁ k₂ h
    show g (φ k₁) = g (φ k₂)
    rw [h]
  · intro k k' h
    have hex : ∃ k'', φ' k'' = φ k := ⟨k', h.symm⟩
    show g (φ k) = j' k'
    simp only [g, dif_pos hex]
    exact hj' _ _ (hex.choose_spec.trans h)
  · rw [memw]
    intro k
    have hy' := (memw φ' j').mp hy
    show (φ k).base y ∈ L.U (g (φ k))
    by_cases hex : ∃ k'', φ' k'' = φ k
    · simp only [g, dif_pos hex]
      have := hy' hex.choose
      rw [hex.choose_spec] at this
      exact this
    · simp only [g, dif_neg hex]
      exact (hcov _).choose_spec

private lemma sections_eq_of_locally_rs_eq {Z : Scheme.{0}} {W : Z.Opens} (a b : Γ(Z, W))
    (h : ∀ z ∈ W, ∃ (V : Z.Opens) (hV : V ≤ W), z ∈ V ∧ rs hV a = rs hV b) : a = b := by
  first
  | (apply TopCat.Presheaf.section_ext Z.sheaf W a b
     intro z hz
     obtain ⟨V, hV, hzV, he⟩ := h z hz
     have ha := congrArg (fun f => f.hom a) (Z.presheaf.germ_res (homOfLE hV) z hzV)
     have hb := congrArg (fun f => f.hom b) (Z.presheaf.germ_res (homOfLE hV) z hzV)
     have hc := congrArg (Z.presheaf.germ V z hzV).hom he
     exact ha.symm.trans (hc.trans hb))
  | (choose V hV hzV he using h
     exact TopCat.Sheaf.eq_of_locally_eq' Z.sheaf (fun z : W => V z.1 z.2) W
       (fun z => homOfLE (hV z.1 z.2))
       (by intro z hz; exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzV z hz⟩) a b
       (fun z => he z.1 z.2))

lemma rs_resTop {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (c : Γ(Z, ⊤)) :
    rs h (resTop U c) = resTop V c := by
  first
  | rfl
  | (simp only [rs, resTop]; rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
  | (unfold rs; rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
  | (simp [rs, resTop, ← Functor.map_comp])

private lemma map_mul_rs {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (a b : Γ(Z, U)) :
    rs h (a * b) = rs h a * rs h b := by
  first
  | exact map_mul _ a b
  | simp [rs]

theorem secCorr_scal (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    {s₁ s₂ : LB.Sec (LB.LinComb L φ ε)} {x₁ x₂ : LB.Sec (LB.LinComb L φ' ε')}
    (h1 : SecCorr φ ε φ' ε' s₁ x₁) (h2 : SecCorr φ ε φ' ε' s₂ x₂) (c d : Γ(Y, ⊤))
    (hx : ∀ j' : K' → L.ι, resTop _ c * x₁.f j' = resTop _ d * x₂.f j') :
    ∀ j : K → L.ι, resTop _ c * s₁.f j = resTop _ d * s₂.f j := by
  have memE : ∀ z : Y, z ∈ LB.wchart L (K := Empty) (fun e => e.elim : Empty → (Y ⟶ X)) (fun e => e.elim) := by
    intro z
    first
    | exact Set.mem_iInter.mpr (fun e => e.elim)
    | simp [LB.wchart]
  have stepA : ∀ j : K → L.ι, LB.Coh L φ j → resTop _ c * s₁.f j = resTop _ d * s₂.f j := by
    intro j hj
    apply sections_eq_of_locally_rs_eq
    intro z hz
    obtain ⟨j', hj', hjj, hzj'⟩ := exists_coh_extending_of_mem_wchart (K := K') (K' := K) hL φ' φ j hj z hz
    have hcomp : ∀ k k', φ k = φ' k' → j k = j' k' := fun k k' h => (hjj k' k h.symm).symm
    refine ⟨LB.wchart L φ j ⊓ LB.wchart L φ' j', inf_le_left, ?_, ?_⟩
    · first
      | exact ⟨hz, hzj'⟩
      | exact TopologicalSpace.Opens.mem_inf.mpr ⟨hz, hzj'⟩
    · have e1 := h1 j j' hj hj' hcomp
      have e2 := h2 j j' hj hj' hcomp
      have e3 := congrArg (rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _)) (hx j')
      have m1 := map_mul_rs (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ c) (s₁.f j)
      have m2 := map_mul_rs (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ d) (s₂.f j)
      have m3 := map_mul_rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ c) (x₁.f j')
      have m4 := map_mul_rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ d) (x₂.f j')
      rw [rs_resTop] at m1 m2 m3 m4
      exact m1.trans ((congrArg (fun t => resTop _ c * t) e1).trans (m3.symm.trans (e3.trans
        (m4.trans ((congrArg (fun t => resTop _ d * t) e2.symm).trans m2.symm)))))
  intro j
  apply sections_eq_of_locally_rs_eq
  intro z hz
  obtain ⟨j'', hj'', -, hz''⟩ := exists_coh_extending_of_mem_wchart (K' := Empty) hL φ
    (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) z (memE z)
  refine ⟨(LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'', inf_le_left, ?_, ?_⟩
  · first
    | exact ⟨hz, hz''⟩
    | exact TopologicalSpace.Opens.mem_inf.mpr ⟨hz, hz''⟩
  · have e1 := s₁.compat j j''
    have e2 := s₂.compat j j''
    have e3 := congrArg (rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _))
      (stepA j'' hj'')
    have m1 := map_mul_rs (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)
      (resTop _ c) (s₁.f j)
    have m2 := map_mul_rs (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)
      (resTop _ d) (s₂.f j)
    have m3 := map_mul_rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)
      (resTop _ c) (s₁.f j'')
    have m4 := map_mul_rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)
      (resTop _ d) (s₂.f j'')
    rw [rs_resTop] at m1 m2 m3 m4
    have key := m3.symm.trans (e3.trans m4)
    rw [m1, m2]
    dsimp only [rs]
    rw [e1, e2, _root_.mul_left_comm, _root_.mul_left_comm (resTop _ d)]
    congr 1

end Rel

section SameSum

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I)

lemma c_zero : D.toPre.c 0 = 1 := by
  have h := D.toPre.c_add 0 0
  rw [add_zero] at h
  have h' : D.toPre.c 0 * D.toPre.c 0 = D.toPre.c 0 * 1 := by
    rw [_root_.mul_one]
    exact h.symm
  exact _root_.mul_left_cancel h'

lemma famφB0_one : D.toPre.famφB 0 1 = 𝟙 _ := by
  have h1 : (toUnit D.toPre.P.A ≫ D.toPre.c 0) = 1 := by
    rw [c_zero D]
    first
    | simp [Hom.one_def]
    | (rw [Hom.one_def, Hom.one_def, ← Category.assoc]; congr 1)
  show (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c 0)).left = 𝟙 _
  rw [h1]
  show ((𝟙 D.toPre.P.A) * 1 : D.toPre.P.A ⟶ D.toPre.P.A).left = _
  rw [_root_.mul_one]
  first
  | rfl
  | simp

lemma famφB0_two : D.toPre.famφB 0 2 = D.toPre.famφB 0 3 := by
  show (toUnit D.toPre.P.A ≫ D.toPre.c 0).left = (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left
  rw [c_zero D, Hom.one_def]
  first
  | simp
  | (congr 1; rw [← Category.assoc]; congr 1)

lemma sameSum_famφB0 : LB.SameSum (D.toPre.famφB 0) (DegPre.famε 1)
    (fun _ : Fin 1 => 𝟙 D.toPre.P.A.left) (fun _ => ((1 : ℕ) : ℤ)) := by
  intro ψ
  have h0 : D.toPre.famφB 0 0 = 𝟙 _ := rfl
  have e1 := famφB0_one D
  have e2 := famφB0_two D
  rw [Fin.sum_univ_four, Fin.sum_univ_one]
  split_ifs
  all_goals first
    | (exfalso; exact ‹¬ 𝟙 D.toPre.P.A.left = ψ› (h0.symm.trans ‹D.toPre.famφB 0 0 = ψ›))
    | (exfalso; exact ‹¬ D.toPre.famφB 0 0 = ψ› (h0.trans ‹𝟙 D.toPre.P.A.left = ψ›))
    | (exfalso; exact ‹¬ 𝟙 D.toPre.P.A.left = ψ› (e1.symm.trans ‹D.toPre.famφB 0 1 = ψ›))
    | (exfalso; exact ‹¬ D.toPre.famφB 0 1 = ψ› (e1.trans ‹𝟙 D.toPre.P.A.left = ψ›))
    | (exfalso; exact ‹¬ D.toPre.famφB 0 3 = ψ› (e2.symm.trans ‹D.toPre.famφB 0 2 = ψ›))
    | (exfalso; exact ‹¬ D.toPre.famφB 0 2 = ψ› (e2.trans ‹D.toPre.famφB 0 3 = ψ›))
    | (simp [DegPre.famε]; done)
    | rfl
    | decide

end SameSum

section Rank

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {I : Ideal R} (D : DegData R I)

set_option maxHeartbeats 1000000 in

theorem secB_rank_one (hLaws : Laws) (t s' : D.toPre.SecB 1 0) :
    ∃ c₀ c' : R, (∀ j, toW D.toPre.P.A.hom _ c₀ * s'.f j = toW D.toPre.P.A.hom _ c' * t.f j) ∧
      (c₀ = 0 → ∀ j, t.f j = 0) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨V, hpV, b, hb⟩ := hLaws.secBaseChange (Spec (CommRingCat.of R)) D.toPre.P 1 le_rfl
    (IsLocalRing.closedPoint R)
  have hV : V = ⊤ := eq_top_of_closedPoint_mem V hpV
  let t0 : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Spec (CommRingCat.of R))) V).left :=
    IsOpenImmersion.lift V.ι (𝟙 _) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨x, ?_⟩, rfl⟩
      rw [hV]; trivial)
  have ht0 : t0 ≫ V.ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  set T := baseAt t0 with hTdef
  have hT : T.hom = 𝟙 _ := by
    show t0 ≫ V.ι ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, ht0]
  let b' : Fin (1 ^ D.toPre.P.g) → LB.Sec (LPow D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) := fun i =>
    pullSec' D.toPre.P.L _ _ (b i) (homAt t0 ▷ D.toPre.P.A).left (fun _ => (snd T D.toPre.P.A).left)
      (fun _ => by rw [← Over.comp_left, whiskerRight_snd])
  have hpull : ∀ i, IsPullSec D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) (homAt t0 ▷ D.toPre.P.A)
      (whiskerRight_snd (homAt t0) D.toPre.P.A) (b i) (b' i) := fun i j => pullSec'_f _ _ _ _ _ _ _ j
  obtain ⟨-, hspan⟩ := hb R t0 b' hpull
  have hsub : Subsingleton (Fin (1 ^ D.toPre.P.g)) := by rw [one_pow]; infer_instance
  have i0 : Fin (1 ^ D.toPre.P.g) := ⟨0, by rw [one_pow]; exact Nat.one_pos⟩
  have mem : ∀ x : LB.Sec (LPow D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T), ∃ c : Γ(T.left, ⊤),
      (SecM.ofSec D.toPre.P.A x : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) =
        c • SecM.ofSec D.toPre.P.A (b' i0) := by
    intro x
    have hx : (SecM.ofSec D.toPre.P.A x : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) ∈
        Submodule.span Γ(T.left, ⊤) (Set.range fun i => (SecM.ofSec D.toPre.P.A (b' i) :
          SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T)) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    refine ⟨c i0, ?_⟩
    rw [← hc, Finset.sum_eq_single i0 (fun i _ hi => absurd (Subsingleton.elim i i0) hi)
      (fun h => absurd (Finset.mem_univ i0) h)]
  obtain ⟨ut, hut⟩ := sec_transport hL (sameSum_famφB0 D) t
  obtain ⟨us, hus⟩ := sec_transport hL (sameSum_famφB0 D) s'
  set π₂ := (snd T D.toPre.P.A).left with hπ₂
  have : IsIso T.hom := by rw [hT]; infer_instance
  have hiso : IsIso π₂ := by
    show IsIso (pullback.snd T.hom D.toPre.P.A.hom)
    infer_instance
  let pl : LB.Sec (LB.LinComb D.toPre.P.L (fun _ : Fin 1 => 𝟙 D.toPre.P.A.left) (fun _ => ((1 : ℕ) : ℤ))) →
      LB.Sec (LPow D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) := fun u =>
    pullSec' D.toPre.P.L _ _ u π₂ (fun _ => π₂) (fun _ => (Category.comp_id _).symm)
  obtain ⟨c0, hc0⟩ := mem (pl ut)
  obtain ⟨c1, hc1⟩ := mem (pl us)
  have hrel : c0 • (SecM.ofSec D.toPre.P.A (pl us) : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) =
      c1 • SecM.ofSec D.toPre.P.A (pl ut) := by
    rw [hc0, hc1, smul_smul, smul_smul, mul_comm]
  have hfstp : (fst T D.toPre.P.A).left = π₂ ≫ D.toPre.P.A.hom := by
    have h1 : (fst T D.toPre.P.A).left ≫ T.hom = (T ⊗ D.toPre.P.A).hom := Over.w _
    have h2 : π₂ ≫ D.toPre.P.A.hom = (T ⊗ D.toPre.P.A).hom := Over.w _
    rw [hT, Category.comp_id] at h1
    rw [h1, h2]
  have eR' : ∀ c : Γ(T.left, ⊤), (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) = c :=
    fun c => by rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  have hlift : ∀ (W : (T ⊗ D.toPre.P.A).left.Opens) (c : Γ(T.left, ⊤)), liftHom D.toPre.P.A W c =
      toW ((fst T D.toPre.P.A).left) W ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) := by
    intro W c
    simp only [liftHom, toW, RingHom.comp_apply]
    rw [eR']
    rfl
  have key : ∀ (u₁ u₂ : LB.Sec (LB.LinComb D.toPre.P.L (fun _ : Fin 1 => 𝟙 D.toPre.P.A.left)
      (fun _ => ((1 : ℕ) : ℤ)))) (c c' : Γ(T.left, ⊤)),
      c • (SecM.ofSec D.toPre.P.A (pl u₁) : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) =
        c' • SecM.ofSec D.toPre.P.A (pl u₂) →
      ∀ j : Fin 1 → D.toPre.P.L.ι, toW D.toPre.P.A.hom _ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) * u₁.f j =
        toW D.toPre.P.A.hom _ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c') * u₂.f j := by
    intro u₁ u₂ c c' h j
    have hj := congrArg (fun z => z.1 j) h
    change liftHom _ _ c * (pl u₁).f j = liftHom _ _ c' * (pl u₂).f j at hj
    rw [hlift, hlift] at hj
    simp only [pl] at hj
    rw [pullSec'_f, pullSec'_f, toW_congr hfstp, toW_congr hfstp] at hj
    apply Scheme.Hom.app_injective π₂
    apply map_inj_of_le_ge (wchart_le_preimage D.toPre.P.L π₂ (fun _ => 𝟙 _) (fun _ => π₂)
      (fun _ => (Category.comp_id _).symm) j) (fun x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k)
    erw [map_mul, map_mul, app_toW, map_mul, map_mul, app_toW, toW_res, toW_res]
    exact hj
  have e1 := key us ut c0 c1 hrel
  have hsc := secCorr_scal hL _ _ _ _ hus hut (scal D.toPre.P.A.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c0))
    (scal D.toPre.P.A.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c1)) (fun j' => by
      rw [resTop_scal, resTop_scal]; exact e1 j')
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c0, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c1,
    fun j => by rw [← resTop_scal, ← resTop_scal]; exact hsc j, fun h0 => ?_⟩
  have hc00 : c0 = 0 := by rw [← eR' c0, h0, map_zero]
  have hut0 : ∀ j : Fin 1 → D.toPre.P.L.ι, ut.f j = 0 := by
    have h := key ut ut 1 0 (by rw [one_smul, zero_smul, hc0, hc00, zero_smul])
    intro j
    have hj := h j
    rw [map_one, map_zero, map_one, map_zero, _root_.one_mul, zero_mul] at hj
    exact hj
  have ht := secCorr_scal hL _ _ _ _ hut hut 1 0 (fun j' => by rw [hut0 j', mul_zero, mul_zero])
  intro j
  have hj := ht j
  simp only [resTop, map_one, map_zero, _root_.one_mul, zero_mul] at hj
  exact hj

end Rank

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

section
set_option autoImplicit false
set_option linter.overlappingInstances false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma isUnit_toW_of_K {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (W : Y.Opens) {r : R}
    (hr : r ≠ 0) : IsUnit (toW (q ≫ jK R) W r) := by
  have e1 : toW (q ≫ jK R) W r = (q.appLE ⊤ W le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r)) := by
    rw [toW, RingHom.comp_apply]
    rw [← Scheme.Hom.appLE_comp_appLE (f := q) (g := jK R) ⊤ ⊤ W le_top le_top]
    rw [CommRingCat.comp_apply]
    congr 1
    have := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    erw [Scheme.Hom.appLE_eq_app]
    exact this.symm
  rw [e1]
  exact ((isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)).map _).map _

lemma base_eq_of_isDominant {X Y Z W : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : f ≫ s = g ≫ s) (i0 : W ⟶ X) [IsDominant i0] (hU : i0 ≫ f = i0 ≫ g) (x : X) : f.base x = g.base x := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (i0 ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let i0' : U' ⟶ X' := Over.homMk i0
  have : IsSeparated Y'.hom := ‹_›
  have : IsDominant (equalizer.ι f' g').left := by
    apply +allowSynthFailures IsDominant.of_comp (equalizer.lift i0' ?_).left
    · rwa [← Over.comp_left, equalizer.lift_ι]
    · ext1; exact hU
  have : Surjective (equalizer.ι f' g').left :=
    surjective_of_isDominant_of_isClosed_range _ (Scheme.Hom.isClosedEmbedding _).isClosed_range
  obtain ⟨z, rfl⟩ := (equalizer.ι f' g').left.surjective x
  have e := congr($(equalizer.condition f' g').left)
  rw [Over.comp_left, Over.comp_left] at e
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  exact congrArg (fun φ => φ.base z) e

section PrB

variable (D) in
lemma prB_std : IsSchemeTheoreticallyDominant (DegPre.prB D.toPre (FractionRing R)).left ∧
    QuasiCompact (DegPre.prB D.toPre (FractionRing R)).left := by
  have := flat_B (D := D)
  have := isDominant_jF R
  have : IsSchemeTheoreticallyDominant (jF R) := IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsIso (jFK (R := R) (FractionRing R)) := by
    have : IsIso (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) := by
      rw [Algebra.algebraMap_self]
      exact inferInstanceAs (IsIso (𝟙 (CommRingCat.of (FractionRing R))))
    infer_instance
  have : IsSchemeTheoreticallyDominant (TF (R := R) (FractionRing R)).hom :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (jFK (R := R) (FractionRing R) ≫ jF R))
  have : QuasiCompact (TF (R := R) (FractionRing R)).hom :=
    inferInstanceAs (QuasiCompact (jFK (R := R) (FractionRing R) ≫ jF R))
  exact ⟨inferInstanceAs (IsSchemeTheoreticallyDominant (pullback.snd _ _)),
    inferInstanceAs (QuasiCompact (pullback.snd _ _))⟩

end PrB

lemma toW_of_K {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (W : Y.Opens) (r : R) :
    toW (q ≫ jK R) W r = (q.appLE ⊤ W le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r)) := by
  rw [toW, RingHom.comp_apply]
  rw [← Scheme.Hom.appLE_comp_appLE (f := q) (g := jK R) ⊤ ⊤ W le_top le_top]
  rw [CommRingCat.comp_apply]
  congr 1
  have := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  erw [Scheme.Hom.appLE_eq_app]
  exact this.symm

lemma hBF : (DegPre.BF D.toPre (FractionRing R)).hom =
    (pullback.fst _ _ ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
  simp [DegPre.BF, TF]

lemma constBF_alg (a : R) (W : (DegPre.BF D.toPre (FractionRing R)).left.Opens) :
    DegPre.constBF D.toPre (FractionRing R) (algebraMap R (FractionRing R) a) W =
      toW (DegPre.BF D.toPre (FractionRing R)).hom W a := by
  rw [toW_congr hBF, toW_of_K]
  rw [← Scheme.Hom.appLE_comp_appLE (f := pullback.fst _ _) (g := jFK (R := R) (FractionRing R)) ⊤ ⊤ W le_top le_top]
  rw [CommRingCat.comp_apply]
  have := congrArg (fun φ => φ.hom (algebraMap R (FractionRing R) a))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Algebra.algebraMap_self,
    RingHom.id_apply] at this
  erw [Scheme.Hom.appLE_eq_app, ← this]
  rfl

set_option maxHeartbeats 1000000 in

theorem terms_vanish [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) (hI : I = maximalIdeal R)
    (F : Fam D.toPre (FractionRing R) 1) (g : ∀ α, D.toPre.SecB 1 α)
    (hgF : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε 1) (F.s α)
      (D.toPre.famφB α) (DegPre.famε 1) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1) :
    ∀ mu, mu ≠ 0 → ∀ j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ ((g mu).f j) = 0 := by
  subst hI
  classical
  choose Q hQ using fun χ => QForm.exists_QVal hϖ D χ
  have hQ' : QForm.IsQ D.toPre ϖ Q := hQ
  have hv := valOver_vK hϖ
  obtain ⟨hstd, hqc⟩ := prB_std D
  have hs0 : VGe D (FractionRing R) (vK hϖ) 1 0 (F.s 0) 0 := by
    refine ⟨1, fun _ => 1, fun _ => g 0, fun _ => F.s 0, fun _ => hgF 0, fun _ => by simp, fun j => ?_⟩
    rw [Fin.sum_univ_one, ← map_one (algebraMap R (FractionRing R)), constBF_alg, map_one, _root_.one_mul]
  intro mu hmu
  have hm := SectionScalarValuation.fe_move hϖ hQ' hv 1 mu 0 F hs0
  have e01 : (0 : D.toPre.X) + 1 • mu = mu := by simp
  rw [e01] at hm
  have hb0 : QForm.bOf D.toPre Q mu 0 = 0 := by
    simp [QForm.bOf, QForm.Q_zero hϖ D hQ']
  have hq1 : 1 ≤ Q mu := QForm.Q_pos hϖ D hQ' hmu
  obtain ⟨N, a, σ, σF, hσF, hva, hsum⟩ := hm
  have hab : ∀ i, ∃ b : R, a i = algebraMap R (FractionRing R) (ϖ * b) := by
    intro i
    by_cases ha : a i = 0
    · exact ⟨0, by rw [ha, mul_zero, map_zero]⟩
    obtain ⟨n, hn⟩ := hasVal_of_ne_zero hϖ ha
    have h1 := hva i
    have hvn := hv _ _ hn
    rw [Algebra.algebraMap_self, RingHom.id_apply] at hvn
    rw [hvn, hb0] at h1
    have hn1 : 1 ≤ n := by
      have : ((0 : ℚ) + ((1 * Q mu + 0 : ℤ) : ℚ)) ≤ (n : ℚ) := by exact_mod_cast h1
      rw [zero_add] at this
      have : (1 : ℚ) ≤ n := le_trans (by exact_mod_cast (by omega : (1 : ℤ) ≤ 1 * Q mu + 0)) this
      exact_mod_cast this
    obtain ⟨u, hu⟩ := hn
    obtain ⟨d, hd⟩ : ∃ d : ℕ, n = d + 1 := ⟨(n - 1).toNat, by omega⟩
    refine ⟨ϖ ^ d * u, ?_⟩
    rw [hu, hd, zpow_add₀ (by exact (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hϖ.ne_zero),
      zpow_natCast, zpow_one]
    simp only [map_mul, map_pow]
    ring
  choose b hb using hab
  have := flat_B (D := D)
  have hdom : IsDominant (DegPre.prB D.toPre (FractionRing R)).left := inferInstance
  have key : ∀ j₂ : Fin 4 → D.toPre.P.L.ι,
      (∀ k k', (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k =
        (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k' → j₂ k = j₂ k') →
      (g mu).f j₂ = toW D.toPre.P.A.hom _ ϖ *
        ∑ i, toW D.toPre.P.A.hom _ (b i) * (σ i).f j₂ := by
    intro j₂ hcoh
    have hc : LB.Coh D.toPre.P.L (Sum.elim (DegPre.famφ D.toPre (FractionRing R) mu)
        (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k)) (Sum.elim j₂ j₂) := by
      intro x y hxy
      rcases x with k | k <;> rcases y with k' | k' <;>
        simp only [Sum.elim_inl, Sum.elim_inr, GC.famφ_eq] at hxy ⊢ <;> exact hcoh k k' hxy
    have E1 := hgF mu j₂ j₂ hc
    have E2 := hsum j₂
    have E3 := fun i => hσF i j₂ j₂ hc
    have hle : (DegPre.prB D.toPre (FractionRing R)).left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂ ≤
        LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) mu) j₂ ⊓
          LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k) j₂ := by
      intro x hx
      refine ⟨Set.mem_iInter.2 fun k => ?_, Set.mem_iInter.2 fun k => ?_⟩
      · rw [GC.famφ_eq]; exact Set.mem_iInter.1 hx k
      · exact Set.mem_iInter.1 hx k
    apply Scheme.Hom.app_injective (DegPre.prB D.toPre (FractionRing R)).left
    apply map_inj_of_le_ge (inf_le_right.trans (wchart_comp_le _ _ j₂)) hle
    refine E1.trans ?_
    have hw : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom = (DegPre.BF D.toPre (FractionRing R)).hom :=
      Over.w _
    rw [show resTop _ (1 : Γ((DegPre.BF D.toPre (FractionRing R)).left, ⊤)) = 1 from map_one _, _root_.one_mul, E2]
    simp only [map_sum, map_mul, app_toW, toW_congr hw]
    erw [map_sum, map_mul, map_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have E3i := E3 i
    rw [show resTop _ (1 : Γ((DegPre.BF D.toPre (FractionRing R)).left, ⊤)) = 1 from map_one _, _root_.one_mul] at E3i
    erw [map_mul, map_mul, ← E3i, hb i, constBF_alg, toW_res, toW_res, toW_res, map_mul]
    rw [_root_.mul_assoc]
    rfl
  intro (j : Fin 4 → D.toPre.P.L.ι)
  set π := pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)
  refine TopCat.Presheaf.section_ext (pullback D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).sheaf _ _ 0
    fun z hz => ?_
  choose ch hch using WeightPf.exists_chart D.toPre.P.L D.toPre.P.isLB
  let j₂ : Fin 4 → D.toPre.P.L.ι := fun k => ch ((D.toPre.famφB mu k).base (π.base z))
  have hcoh : ∀ k k', (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k =
      (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k' → j₂ k = j₂ k' := fun k k' h =>
    congrArg ch (base_eq_of_isDominant D.toPre.P.A.hom
      ((GC.famφB_over mu k).trans (GC.famφB_over mu k').symm) _ h (π.base z))
  have hK := key j₂ hcoh
  have hV : LB.wchart D.toPre.P.L (D.toPre.famφB mu) j ⊓ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂ ≤
      LB.wchart D.toPre.P.L (D.toPre.famφB mu) j := inf_le_left
  have hzV : z ∈ π ⁻¹ᵁ (LB.wchart D.toPre.P.L (D.toPre.famφB mu) j ⊓ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂) :=
    ⟨hz, Set.mem_iInter.2 fun k => hch _⟩
  have hres : (π.app _) ((D.toPre.P.A.left.presheaf.map (homOfLE hV).op).hom ((g mu).f j)) = 0 := by
    have c := (g mu).compat j j₂
    have hm : ϖ ∈ maximalIdeal R ^ (0 + 1) := by
      rw [zero_add, pow_one]; exact hϖ.not_isUnit
    have h2 : (π.app (LB.wchart D.toPre.P.L (D.toPre.famφB mu) j ⊓ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂))
        ((D.toPre.P.A.left.presheaf.map (homOfLE (inf_le_right : LB.wchart D.toPre.P.L (D.toPre.famφB mu) j ⊓
          LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂ ≤ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂)).op).hom
          ((g mu).f j₂)) = 0 := by
      rw [hK]
      erw [map_mul, toW_res, map_mul, app_toW_of_mem D.toPre.P.A.hom _ _ hm, zero_mul]
    erw [c, map_mul, h2]
    rw [mul_zero]
  have hz2 : π ⁻¹ᵁ (LB.wchart D.toPre.P.L (D.toPre.famφB mu) j ⊓ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂) ≤
      π ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j := π.preimage_mono hV
  show (pullback D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).presheaf.germ _ z hz _ =
    (pullback D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).presheaf.germ _ z hz 0
  erw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hz2) z hzV, app_res π hV, hres, map_zero, map_zero]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

section
set_option autoImplicit false
set_option linter.overlappingInstances false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

set_option maxHeartbeats 1000000 in

theorem leading_expansion_term_ne_zero [IsDiscreteValuationRing R] (hI : I = maximalIdeal R) (U : Unif I D A G) (s : H0 U.LG.L 1)
    (hs : NonzeroOnSpecial U s) (g : ∀ α, D.toPre.SecB 1 α) (hexp : U.ExpandsAt 0 1 s g)
    (hv : ∀ mu, mu ≠ 0 → ∀ j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ ((g mu).f j) = 0) :
    ¬ ∀ j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ ((g 0).f j) = 0 := by
  intro h0
  subst hI

  have hloc : ∀ {X : Scheme.{0}} {W : X.Opens} (y : Γ(X, W)),
      (∀ x ∈ W, ∃ V : X.Opens, ∃ hV : V ≤ W, x ∈ V ∧ (X.presheaf.map (homOfLE hV).op).hom y = 0) →
        y = 0 := by
    intro X W y h
    choose V hV hxV hy using h
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun p : W => V p.1 p.2) W
      (fun p => homOfLE (hV p.1 p.2)) ?_ y 0 ?_
    · intro x hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩
    · intro p
      exact (hy p.1 p.2).trans (map_zero _).symm

  have hvan : ∀ (α : D.toPre.X) (j : Fin 4 → D.toPre.P.L.ι),
      ((U.gt 0).pG.left.app (D.toPre.P.L.wchart (D.toPre.famφB α) j)).hom ((g α).f j) = 0 := by
    intro α j
    have hz : ((pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).app
        ((D.toPre.P.L.LinComb (D.toPre.famφB α) (DegPre.famε 1)).U j)).hom ((g α).f j) = 0 := by
      by_cases hα : α = 0
      · subst hα
        exact h0 j
      · exact hv α hα j
    show (((U.gt 0).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).app
        ((D.toPre.P.L.LinComb (D.toPre.famφB α) (DegPre.famε 1)).U j)).hom ((g α).f j) = 0
    try rw [Scheme.comp_app]
    exact (congrArg (fun z => ((U.gt 0).q.left.app _).hom z) hz).trans (map_zero _)
  unfold NonzeroOnSpecial at hs
  obtain ⟨j, hj⟩ := hs
  obtain ⟨S, -, hS⟩ := hexp
  choose ch hch using fun y : D.toPre.P.A.left => WeightPf.exists_chart D.toPre.P.L D.toPre.P.isLB y
  apply hj
  refine hloc _ fun x hx => ?_
  refine ⟨U.expW 0 (fun _ => ch ((U.gt 0).pG.left.base x), fun _ => j 0) j S
      (fun α i => ch (((U.gt 0).pG.left ≫ D.toPre.famφB α i).base x))
      (fun α i => ch ((D.toPre.Oφ (U.gt 0).pG α i).base x)),
    inf_le_left.trans inf_le_right, ?_, ?_⟩
  · refine TopologicalSpace.Opens.mem_inf.mpr ⟨TopologicalSpace.Opens.mem_inf.mpr
      ⟨TopologicalSpace.Opens.mem_inf.mpr ⟨?_, ?_⟩, hx⟩, ?_⟩
    · exact Set.mem_iInter.mpr fun _ => hch _
    · exact Set.mem_iInter.mpr fun _ => Set.mem_iInter.mp hx 0
    · exact WeightPf.mem_finset_inf S _ x fun α _ => TopologicalSpace.Opens.mem_inf.mpr
        ⟨Set.mem_iInter.mpr fun i => hch _, Set.mem_iInter.mpr fun i => hch _⟩
  · have e := hS (fun _ => ch ((U.gt 0).pG.left.base x), fun _ => j 0) j
      (fun α i => ch (((U.gt 0).pG.left ≫ D.toPre.famφB α i).base x))
      (fun α i => ch ((D.toPre.Oφ (U.gt 0).pG α i).base x)) rfl (by
        intro a b hab
        rcases a with _ | a | a <;> rcases b with _ | b | b <;>
          exact congrArg (fun f => ch (f.base x)) hab)
    rw [Finset.sum_eq_zero (fun α _ => by rw [hvan, map_zero, zero_mul]), ← Units.val_pow_eq_pow_val] at e
    exact (Units.mul_right_eq_zero _).mp e

theorem generates_of_ne (hLaws : Laws) [IsDiscreteValuationRing R] (hI : I = maximalIdeal R)
    (t : D.toPre.SecB 1 0) (ht : ¬ ∀ j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ (t.f j) = 0) :
    SecBGenerates 1 0 t := by
  unfold SecBGenerates
  intro s'
  obtain ⟨c₀, c', h, h0⟩ := secB_rank_one (hLaws := hLaws) (t := t) (s' := s')
  haveI : Flat D.toPre.P.A.hom := flat_B

  have hc₀ : c₀ ≠ 0 := by
    intro hz
    apply ht
    intro j
    rw [h0 hz j, map_zero]

  have hdiv : ∃ a : R, c' = c₀ * a := by
    obtain ⟨m, hm | hm⟩ := ValuationRing.cond c₀ c'
    · exact ⟨m, hm.symm⟩
    · by_cases hmu : IsUnit m
      · obtain ⟨u, rfl⟩ := hmu
        refine ⟨↑u⁻¹, ?_⟩
        rw [← hm, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
      · exfalso
        have hmI : m ∈ I ^ (0 + 1) := by
          rw [zero_add, pow_one, hI]
          exact (IsLocalRing.mem_maximalIdeal m).mpr hmu
        have hc' : c' ≠ 0 := by
          rintro rfl
          exact hc₀ (by rw [← hm, zero_mul])
        apply ht
        intro j
        have hj : t.f j = toW D.toPre.P.A.hom _ m * s'.f j := by
          refine (sub_eq_zero.mp (toW_mul_eq_zero D.toPre.P.A.hom _ hc' ?_)).symm
          rw [mul_sub, ← _root_.mul_assoc, ← map_mul, hm, h j, sub_self]
        rw [hj, map_mul, app_toW_of_mem D.toPre.P.A.hom (I ^ (0 + 1)) _ hmI, zero_mul]
  obtain ⟨a, rfl⟩ := hdiv
  have hSa : SecIsMul D.toPre.P.A.hom a s' t := by
    intro j
    rw [resTop_scal]
    refine sub_eq_zero.mp (toW_mul_eq_zero D.toPre.P.A.hom _ hc₀ ?_)
    rw [mul_sub, h j, map_mul, _root_.mul_assoc, sub_self]
  refine ⟨a, hSa, fun b hb => ?_⟩
  by_contra hne
  apply ht
  intro j
  have e1 := hb j
  have e2 := hSa j
  rw [resTop_scal] at e1 e2
  have hz : t.f j = 0 := by
    refine toW_mul_eq_zero D.toPre.P.A.hom _ (sub_ne_zero.mpr hne) ?_
    rw [map_sub, sub_mul, ← e1, ← e2, sub_self]
  rw [hz, map_zero]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm SectionScalarValuation

section FEGen

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem exists_fe_gen (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : IsQ D.toPre ϖ Q) (k : ℕ)
    (mu α : D.toPre.X) :
    ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.deltaφ D.toPre F k α mu) (DegPre.deltaε k)), u.IsGen ∧
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
        (DegPre.famMult D.toPre F k mu α) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨Ix, _, φV, εV, e', he', hC, c₀, hc₀, hval⟩ := famMult_data D hϖ hQ k mu α
  obtain ⟨eB, heB, veB⟩ := exists_eB D.toPre k α mu e' he' hC
  have hc0 : c₀ ≠ 0 := ne_zero_of_hasVal hϖ hc₀
  set c : F := algebraMap (FractionRing V) F c₀ with hc
  have hcne : c ≠ 0 := (map_ne_zero _).2 hc0
  let cU : Γ((DegPre.BF D.toPre F).left, ⊤)ˣ :=
    ⟨gF D.toPre F c, gF D.toPre F c⁻¹, by rw [← map_mul, mul_inv_cancel₀ hcne, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hcne, map_one]⟩
  let g0 : LB.Gen (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top cU⟩
  have hg0 : g0.IsGen := fun i j => by
    have hg : (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 := by
      simp [LB.LinComb]; rfl
    calc res _ (g0.s i) = res _ (g0.s j) := (res_res' _ _ cU).trans (res_res' _ _ cU).symm
      _ = _ := by rw [hg, _root_.one_mul]
  have hformU : FormEq (Sum.elim (fun i => (DegPre.prB D.toPre F).left ≫ Sum.elim (D.toPre.famφB (α + k • mu))
        (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i) i) PEmpty.elim)
      (Sum.elim (DegPre.deltaε k) PEmpty.elim) (DegPre.deltaφ D.toPre F k α mu) (DegPre.deltaε k) := fun U _ h => by
    have e0 : ∀ f : PEmpty → U, ∏ i, f i = 1 := fun f => Fintype.prod_empty f
    rw [Fintype.prod_sum_type, e0, _root_.mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases i with i | i
    · simp only [Sum.elim_inl, DegPre.deltaφ, GC.famφ_eq]
    · simp only [Sum.elim_inr, DegPre.deltaφ, GC.famφ_eq]
      rw [← Category.assoc, trF_prB, Category.assoc]
      rfl
  obtain ⟨u, hu, vu⟩ := exists_gen hL hformU
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ eB (DegPre.prB D.toPre F).left) g0)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ heB _) hg0)
  have hval_u : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
      Good D.toPre.P.L z J →
      (val u ρ z J).val = (val eB (ρ ≫ (DegPre.prB D.toPre F).left) z J).val * gs ρ z ⊤ (gF D.toPre F c) := by
    intro Z ρ z J hJ
    rw [vu Z ρ z J hJ, val_mul hJ, val_pull hJ, Units.val_mul]
    congr 1
    have hmem : ρ z ∈ LB.wchart D.toPre.P.L (K := PEmpty) PEmpty.elim (fun k => J (ρ ≫ PEmpty.elim k)) :=
      Set.mem_iInter.2 fun k => k.elim
    exact (congrArg Units.val (gm_res ρ z le_top hmem cU)).trans (gs_unit ρ z ⊤ (by trivial) cU).symm
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  have hcorr : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (DegPre.famMult D.toPre F k mu α) := corr_of_val hL fun y J hJ => Units.ext (by
    have C : IsCub (cubV D.toPre.cub (T := TF (R := V) F) y J) := isCub_cubV D.toPre.cub hJ
    have E2 : val eB ((DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left) y J =
        val e' (DegPre.jFR (R := V) F) y J := by
      have E1 := veB (TF (R := V) F) (DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F) y J hJ
      rw [z₂, C.N_one, C.face₂, inv_one, _root_.one_mul, _root_.one_mul] at E1
      have e3 : (1 : TF (R := V) F ⟶ D.toPre.P.A).left ≫ D.toPre.P.A.hom = DegPre.jFR (R := V) F := Over.w _
      rw [e3] at E1
      have e4 : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
        rw [← Over.comp_left, z₂]
      rw [e4]; exact E1
    rw [val_pull hJ, Category.id_comp, hval_u _ _ y J hJ, hval F (TF (R := V) F).left (𝟙 (TF (R := V) F).left) y J hJ, E2, gs_gF_zF, gs_scal_jFK,
      Category.id_comp, ← hc]
    exact mul_comm _ _)
  exact ⟨u, hu, hcorr⟩

theorem fam_eq_zero (hϖ : Irreducible ϖ) (G : Fam D.toPre F 1)
    (h0 : ∀ j : Fin 4 → D.toPre.P.L.ι, (G.s 0).f j = 0) :
    ∀ (mu : D.toPre.X) (j : Fin 4 → D.toPre.P.L.ι), (G.s mu).f j = 0 := by
  classical
  choose Q hQ using fun χ => QForm.exists_QVal hϖ D χ
  intro mu j
  obtain ⟨u, hu, hc⟩ := exists_fe_gen (F := F) hϖ (Q := Q) hQ 1 mu 0
  have hrel := G.fe mu 0 u hu hc
  have e01 : (0 : D.toPre.X) + 1 • mu = mu := by simp
  rw [e01] at hrel
  have hL := D.toPre.P.isLB
  refine TopCat.Presheaf.section_ext (DegPre.BF D.toPre F).left.sheaf _ _ 0 fun y hy => ?_
  choose ch hch using WeightPf.exists_chart D.toPre.P.L hL
  let j₁ : Fin 4 → D.toPre.P.L.ι := fun k => ch ((DegPre.famφ D.toPre F mu k).base y)
  let j₂ : Fin 4 → D.toPre.P.L.ι := fun k => ch (((DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k).base y)
  let j₃ : Fin 4 ⊕ Fin 4 → D.toPre.P.L.ι := fun k => ch ((DegPre.deltaφ D.toPre F 1 0 mu k).base y)
  have hcoh : LB.Coh D.toPre.P.L (Sum.elim (DegPre.famφ D.toPre F mu)
      (Sum.elim (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k)
        (DegPre.deltaφ D.toPre F 1 0 mu))) (Sum.elim j₁ (Sum.elim j₂ j₃)) := by
    have key : ∀ z, (Sum.elim j₁ (Sum.elim j₂ j₃)) z = ch (((Sum.elim (DegPre.famφ D.toPre F mu)
        (Sum.elim (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k)
          (DegPre.deltaφ D.toPre F 1 0 mu))) z).base y) := by
      rintro (z | z | z) <;> rfl
    intro a b hab
    rw [key a, key b, hab]
  have E := hrel j₁ j₂ j₃ hcoh
  have hy1 : y ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j₁ := Set.mem_iInter.2 fun k => hch _
  have hy2 : y ∈ LB.wchart D.toPre.P.L (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k) j₂ :=
    Set.mem_iInter.2 fun k => hch _
  have hy3 : y ∈ LB.wchart D.toPre.P.L (DegPre.deltaφ D.toPre F 1 0 mu) j₃ := Set.mem_iInter.2 fun k => hch _

  have hz : ((DegPre.BF D.toPre F).left.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
      LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j₁ ⊓
        LB.wchart D.toPre.P.L (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k) j₂ ⊓
        LB.wchart D.toPre.P.L (DegPre.deltaφ D.toPre F 1 0 mu) j₃ ≤ _)).op).hom ((G.s mu).f j₁) = 0 := by
    erw [E, h0 j₂, map_zero, map_zero, zero_mul]

  let W := LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j ⊓
    (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j₁ ⊓
      LB.wchart D.toPre.P.L (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k) j₂ ⊓
      LB.wchart D.toPre.P.L (DegPre.deltaφ D.toPre F 1 0 mu) j₃)
  have hyW : y ∈ W := ⟨hy, ⟨⟨hy1, hy2⟩, hy3⟩⟩
  have hW1 : W ≤ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j ⊓ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j₁ :=
    le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have hc1 := congrArg (rs hW1) ((G.s mu).compat j j₁)
  have hWz : rs (inf_le_left : W ≤ _) ((G.s mu).f j) = 0 := by
    erw [rs_rs, rs_mul, rs_rs] at hc1
    erw [hc1]
    have := congrArg (rs (inf_le_right : W ≤ _)) hz
    erw [rs_rs] at this
    erw [this]
    exact (congrArg _ (map_zero _)).trans (mul_zero _)
  show (DegPre.BF D.toPre F).left.presheaf.germ _ y hy ((G.s mu).f j) = (DegPre.BF D.toPre F).left.presheaf.germ _ y hy 0
  erw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_left : W ≤ _)) y hyW]
  exact (congrArg _ hWz).trans ((map_zero _).trans (map_zero _).symm)

end FEGen

section Local

end Local

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end
