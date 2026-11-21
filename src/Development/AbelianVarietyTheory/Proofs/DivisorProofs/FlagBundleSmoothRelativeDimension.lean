import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleTransportAlongIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleBaseChangeAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFreeModuleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFlagSmoothArithmetic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellVarietyDimensionCounts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyLiftExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyLiftUnique

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_cover_of_alteration : RegularAlteration → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsIntegral Y], IsArithVar q 1 → Nonempty (RegCover q) := by
  first | exact @GlobalTheory.RegCoverExists.nonempty_regCover | exact GlobalTheory.RegCoverExists.nonempty_regCover | (intros; apply GlobalTheory.RegCoverExists.nonempty_regCover <;> assumption)
end

section
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBaseChangeStable

open Limits (pullback)

set_option backward.isDefEq.respectTransparency false in

theorem comp_assoc_app {X Y Z W : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (E : W.Modules) :
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj E) ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app E =
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app E) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app E ≫ eqToHom (by rw [Category.assoc]) := by
  have e := congrArg (fun t => NatTrans.app t E) (Scheme.Modules.pseudofunctor_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, eqToHom_app, Category.id_comp] at e
  calc _ = (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app E) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app E ≫ ((Scheme.Modules.pullbackComp f (g ≫ h)).inv.app E ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app E) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj E) ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app E) := by
        simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
        erw [CategoryTheory.Functor.map_id, Category.id_comp]
    _ = _ := by rw [e]

set_option backward.isDefEq.respectTransparency false in

theorem comp_congr_app {X Y Z : Scheme.{0}} (f : X ⟶ Y) {u v : Y ⟶ Z} (w : u = v) (E : Z.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackCongr w).hom.app E) ≫
      (Scheme.Modules.pullbackComp f v).hom.app E =
    (Scheme.Modules.pullbackComp f u).hom.app E ≫ (Scheme.Modules.pullbackCongr (congrArg (f ≫ ·) w)).hom.app E := by
  subst w
  simp [Scheme.Modules.pullbackCongr]

set_option backward.isDefEq.respectTransparency false in

theorem congr_refl_app {X Y : Scheme.{0}} (f : X ⟶ Y) (h : f = f) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M = 𝟙 _ := by
  simp [Scheme.Modules.pullbackCongr]

variable {B Y B' : Scheme.{0}} (π : Y ⟶ B) (g : B' ⟶ B)

set_option backward.isDefEq.respectTransparency false in

theorem bcIso_coh {T : Scheme.{0}} (h : T ⟶ pullback π g) (E : B.Modules) :
    (Scheme.Modules.pullbackComp h (pullback.fst π g)).hom.app ((Scheme.Modules.pullback π).obj E) ≫
      (Scheme.Modules.pullbackComp (h ≫ pullback.fst π g) π).hom.app E ≫
        (Scheme.Modules.pullbackCongr (show (h ≫ pullback.fst π g) ≫ π = (h ≫ pullback.snd π g) ≫ g by
          rw [Category.assoc, Category.assoc, pullback.condition])).hom.app E =
    (Scheme.Modules.pullback h).map (FlagBaseChange.bcIso π g E).hom ≫
      (Scheme.Modules.pullbackComp h (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
        (Scheme.Modules.pullbackComp (h ≫ pullback.snd π g) g).hom.app E := by
  rw [reassoc_of% (comp_assoc_app h (pullback.fst π g) π E), comp_assoc_app h (pullback.snd π g) g E,
    ← Functor.map_comp_assoc]
  have e : (FlagBaseChange.bcIso π g E).hom ≫ (Scheme.Modules.pullbackComp (pullback.snd π g) g).hom.app E =
      (Scheme.Modules.pullbackComp (pullback.fst π g) π).hom.app E ≫
        (Scheme.Modules.pullbackCongr pullback.condition).hom.app E := by
    simp [FlagBaseChange.bcIso]
  rw [e, Functor.map_comp_assoc, reassoc_of% (comp_congr_app h (pullback.condition (f := π) (g := g)) E)]
  simp [Scheme.Modules.pullbackCongr]

set_option backward.isDefEq.respectTransparency false in

theorem bcIso_coh_map {T : Scheme.{0}} (h : T ⟶ pullback π g) (E : B.Modules) {F : Y.Modules}
    (j : F ⟶ (Scheme.Modules.pullback π).obj E) (w : (h ≫ pullback.fst π g) ≫ π = (h ≫ pullback.snd π g) ≫ g) :
    (Scheme.Modules.pullbackComp h (pullback.fst π g)).hom.app F ≫
      (Scheme.Modules.pullback (h ≫ pullback.fst π g)).map j ≫
        (Scheme.Modules.pullbackComp (h ≫ pullback.fst π g) π).hom.app E ≫
          (Scheme.Modules.pullbackCongr w).hom.app E =
    (Scheme.Modules.pullback h).map
        ((Scheme.Modules.pullback (pullback.fst π g)).map j ≫ (FlagBaseChange.bcIso π g E).hom) ≫
      (Scheme.Modules.pullbackComp h (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
        (Scheme.Modules.pullbackComp (h ≫ pullback.snd π g) g).hom.app E := by
  have n := (Scheme.Modules.pullbackComp h (pullback.fst π g)).hom.naturality j
  simp only [Functor.comp_map] at n
  rw [← reassoc_of% n, bcIso_coh, Functor.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in

theorem match_lift {T : Scheme.{0}} (h : T ⟶ pullback π g) {g' : T ⟶ Y} {t : T ⟶ B'}
    (h₁ : h ≫ pullback.fst π g = g') (h₂ : h ≫ pullback.snd π g = t) (w : g' ≫ π = t ≫ g)
    (E : B.Modules) {F : Y.Modules} (j : F ⟶ (Scheme.Modules.pullback π).obj E) {F' : T.Modules}
    (j' : F' ⟶ (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback g).obj E))
    (e : (Scheme.Modules.pullback g').obj F ≅ F')
    (he : e.hom ≫ j' ≫ (Scheme.Modules.pullbackComp t g).hom.app E =
      (Scheme.Modules.pullback g').map j ≫ (Scheme.Modules.pullbackComp g' π).hom.app E ≫
        (Scheme.Modules.pullbackCongr w).hom.app E) :
    ∃ e' : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback (pullback.fst π g)).obj F) ≅ F',
      e'.hom ≫ j' = (Scheme.Modules.pullback h).map
          ((Scheme.Modules.pullback (pullback.fst π g)).map j ≫ (FlagBaseChange.bcIso π g E).hom) ≫
        (Scheme.Modules.pullbackComp h (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
          (Scheme.Modules.pullbackCongr h₂).hom.app ((Scheme.Modules.pullback g).obj E) := by
  subst h₁ h₂
  refine ⟨(Scheme.Modules.pullbackComp h (pullback.fst π g)).app F ≪≫ e, ?_⟩
  rw [← cancel_mono ((Scheme.Modules.pullbackComp (h ≫ pullback.snd π g) g).hom.app E)]
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc, he]
  rw [bcIso_coh_map]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in

theorem match_fst {T : Scheme.{0}} (h : T ⟶ pullback π g) {t : T ⟶ B'}
    (h₂ : h ≫ pullback.snd π g = t) (w : (h ≫ pullback.fst π g) ≫ π = t ≫ g)
    (E : B.Modules) {F : Y.Modules} (j : F ⟶ (Scheme.Modules.pullback π).obj E) {F' : T.Modules}
    (j' : F' ⟶ (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback g).obj E))
    (e : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback (pullback.fst π g)).obj F) ≅ F')
    (he : e.hom ≫ j' = (Scheme.Modules.pullback h).map
          ((Scheme.Modules.pullback (pullback.fst π g)).map j ≫ (FlagBaseChange.bcIso π g E).hom) ≫
        (Scheme.Modules.pullbackComp h (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
          (Scheme.Modules.pullbackCongr h₂).hom.app ((Scheme.Modules.pullback g).obj E)) :
    ∃ e' : (Scheme.Modules.pullback (h ≫ pullback.fst π g)).obj F ≅ F',
      e'.hom ≫ j' ≫ (Scheme.Modules.pullbackComp t g).hom.app E =
        (Scheme.Modules.pullback (h ≫ pullback.fst π g)).map j ≫
          (Scheme.Modules.pullbackComp (h ≫ pullback.fst π g) π).hom.app E ≫
            (Scheme.Modules.pullbackCongr w).hom.app E := by
  subst h₂
  refine ⟨((Scheme.Modules.pullbackComp h (pullback.fst π g)).app F).symm ≪≫ e, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc, reassoc_of% he]
  rw [congr_refl_app, Category.id_comp, ← bcIso_coh_map π g h E j w, Iso.inv_hom_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in

theorem isFlagBundle_pullback : ∀ (B Y B' : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ g : B' ⟶ B, IsFlagBundle (Limits.pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) r (fun a => FlagBaseChange.pullFlag π g (fl a)) := by
  intro B Y B' π ι E r fl hfl g T t fl'
  obtain ⟨g', ⟨w, hw⟩, huniq⟩ :=
    hfl T (t ≫ g) (fun a => (fl' a).ofIso ((Scheme.Modules.pullbackComp t g).app (E a)))
  refine ⟨pullback.lift g' t w, ⟨pullback.lift_snd _ _ _, fun a i => ?_⟩, ?_⟩
  · obtain ⟨e, he⟩ := hw a i
    exact match_lift π g (pullback.lift g' t w) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) w (E a)
      ((fl a).ι i) ((fl' a).ι i) e he
  · rintro h ⟨w₀, hm⟩
    have w₁ : (h ≫ pullback.fst π g) ≫ π = t ≫ g := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, w₀]
    have e₁ : h ≫ pullback.fst π g = g' := huniq _ ⟨w₁, fun a i => by
      obtain ⟨e, he⟩ := hm a i
      exact match_fst π g h w₀ w₁ (E a) ((fl a).ι i) ((fl' a).ι i) e he⟩
    exact pullback.hom_ext (e₁.trans (pullback.lift_fst _ _ _).symm)
      (w₀.trans (pullback.lift_snd _ _ _).symm)

end GlobalTheory.FlagBaseChangeStable
end
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_base_change : ∀ (B Y B' : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ g : B' ⟶ B, IsFlagBundle (Limits.pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) r (fun a => FlagBaseChange.pullFlag π g (fl a)) := by
  atlas_forward_decl GlobalTheory.FlagBaseChangeStable.isFlagBundle_pullback
end

section
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.FlagUniq

variable {B Y : Scheme.{0}} {ι : Type} {E : ι → B.Modules} {n : ι → ℕ}

def Carries {T : Scheme.{0}} (π : Y ⟶ B) (g : T ⟶ B) (h : T ⟶ Y) (w : h ≫ π = g)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a))
    (flT : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)) : Prop :=
  ∀ a i, ∃ e : (Scheme.Modules.pullback h).obj ((fl a).F i) ≅ (flT a).F i,
    e.hom ≫ (flT a).ι i = (Scheme.Modules.pullback h).map ((fl a).ι i) ≫
      (Scheme.Modules.pullbackComp h π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a)

theorem carries_id (π : Y ⟶ B) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) :
    Carries π π (𝟙 Y) (Category.id_comp π) fl fl := by
  intro a i
  refine ⟨(Scheme.Modules.pullbackId Y).app ((fl a).F i), ?_⟩
  have h1 : (Scheme.Modules.pullback (𝟙 Y)).map ((fl a).ι i) ≫
      (Scheme.Modules.pullbackId Y).hom.app ((Scheme.Modules.pullback π).obj (E a)) =
      (Scheme.Modules.pullbackId Y).hom.app ((fl a).F i) ≫ (fl a).ι i :=
    (Scheme.Modules.pullbackId Y).hom.naturality ((fl a).ι i)
  have h2 := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality π) (E a)
  simp at h2
  simp only [Iso.app_hom, Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app]
  rw [← h1, ← h2, Iso.hom_inv_id_app_assoc]

theorem carries_comp {T Y' : Scheme.{0}} (π : Y ⟶ B) (π' : Y' ⟶ B) (g : T ⟶ B) (h₁ : T ⟶ Y') (h₂ : Y' ⟶ Y)
    (w₁ : h₁ ≫ π' = g) (w₂ : h₂ ≫ π = π')
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a))
    (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback π').obj (E a)) (n a))
    (flT : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a))
    (c₁ : Carries π' g h₁ w₁ fl' flT) (c₂ : Carries π π' h₂ w₂ fl fl') :
    Carries π g (h₁ ≫ h₂) (by rw [Category.assoc, w₂, w₁]) fl flT := by
  subst w₁ w₂
  intro a i
  obtain ⟨e₁, he₁⟩ := c₁ a i
  obtain ⟨e₂, he₂⟩ := c₂ a i
  refine ⟨(Scheme.Modules.pullbackComp h₁ h₂).symm.app _ ≪≫ (Scheme.Modules.pullback h₁).mapIso e₂ ≪≫ e₁, ?_⟩
  have h3 := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity h₁ h₂ π) (E a)
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc, he₁] at h3 ⊢
  rw [← Functor.map_comp_assoc, he₂]
  simp [Scheme.Modules.pullbackCongr] at h3 ⊢
  have hn : (Scheme.Modules.pullbackComp h₁ h₂).inv.app ((fl a).F i) ≫
      (Scheme.Modules.pullback h₁).map ((Scheme.Modules.pullback h₂).map ((fl a).ι i)) =
      (Scheme.Modules.pullback (h₁ ≫ h₂)).map ((fl a).ι i) ≫
        (Scheme.Modules.pullbackComp h₁ h₂).inv.app ((Scheme.Modules.pullback π).obj (E a)) :=
    ((Scheme.Modules.pullbackComp h₁ h₂).inv.naturality ((fl a).ι i)).symm
  rw [reassoc_of% hn]
  congr 1
  have h4 := congrArg (fun f => (Scheme.Modules.pullbackComp h₁ h₂).inv.app ((Scheme.Modules.pullback π).obj (E a)) ≫
    (Scheme.Modules.pullback h₁).map ((Scheme.Modules.pullbackComp h₂ π).hom.app (E a)) ≫
    (Scheme.Modules.pullbackComp h₁ (h₂ ≫ π)).hom.app (E a) ≫ f ≫ eqToHom (by rw [Category.assoc])) h3
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_app_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at h4
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc] at h4
  exact h4.symm

end GlobalTheory.CovTest.FlagUniq

open GlobalTheory.CovTest.FlagUniq in

theorem GlobalTheory.CovTest.flagBundle_iso_over : ∀ (B Y Y' : Scheme.{0}) (π : Y ⟶ B) (π' : Y' ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback π').obj (E a)) (r a)), IsFlagBundle π E r fl → IsFlagBundle π' E r fl' → ∃ e : Y ≅ Y', e.hom ≫ π' = π := by
  intro B Y Y' π π' ι E r fl fl' h h'
  obtain ⟨g₁, ⟨w₁, c₁⟩, -⟩ := h' Y π fl
  obtain ⟨g₂, ⟨w₂, c₂⟩, -⟩ := h Y' π' fl'
  obtain ⟨u, -, hu⟩ := h Y π fl
  obtain ⟨u', -, hu'⟩ := h' Y' π' fl'
  have e₁ : g₁ ≫ g₂ = 𝟙 Y :=
    (hu _ ⟨_, carries_comp π π' π g₁ g₂ w₁ w₂ fl fl' fl c₁ c₂⟩).trans (hu _ ⟨_, carries_id π fl⟩).symm
  have e₂ : g₂ ≫ g₁ = 𝟙 Y' :=
    (hu' _ ⟨_, carries_comp π' π π' g₂ g₁ w₂ w₁ fl' fl fl' c₂ c₁⟩).trans (hu' _ ⟨_, carries_id π' fl'⟩).symm
  exact ⟨⟨g₁, g₂, e₁, e₂⟩, w₁⟩
end
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_family_unique_iso : ∀ (B Y Y' : Scheme.{0}) (π : Y ⟶ B) (π' : Y' ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback π').obj (E a)) (r a)), IsFlagBundle π E r fl → IsFlagBundle π' E r fl' → ∃ e : Y ≅ Y', e.hom ≫ π' = π := by
  atlas_forward_decl GlobalTheory.CovTest.flagBundle_iso_over
end

section
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

namespace GlobalTheory.CovTest

open CategoryTheory AlgebraicGeometry

theorem isFlagBundle_cond_iso {B Y T : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E E' : ι → B.Modules) (r : ι → ℕ)
    (e : ∀ a, E a ≅ E' a) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a))
    (g : T ⟶ B) (fl'' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E' a)) (r a))
    (y : T ⟶ Y) (w : y ≫ π = g) :
    (∀ a i, ∃ e0 : (Scheme.Modules.pullback y).obj ((fl a).F i) ≅
        ((fl'' a).ofIso ((Scheme.Modules.pullback g).mapIso (e a)).symm).F i,
      e0.hom ≫ ((fl'' a).ofIso ((Scheme.Modules.pullback g).mapIso (e a)).symm).ι i =
        (Scheme.Modules.pullback y).map ((fl a).ι i) ≫
          (Scheme.Modules.pullbackComp y π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a)) ↔
    (∀ a i, ∃ e0 : (Scheme.Modules.pullback y).obj (((fl a).ofIso ((Scheme.Modules.pullback π).mapIso (e a))).F i) ≅
        (fl'' a).F i,
      e0.hom ≫ (fl'' a).ι i =
        (Scheme.Modules.pullback y).map (((fl a).ofIso ((Scheme.Modules.pullback π).mapIso (e a))).ι i) ≫
          (Scheme.Modules.pullbackComp y π).hom.app (E' a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E' a)) := by
  have nat : ∀ a, (Scheme.Modules.pullback y).map ((Scheme.Modules.pullback π).map (e a).hom) ≫
      (Scheme.Modules.pullbackComp y π).hom.app (E' a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E' a) =
      (Scheme.Modules.pullbackComp y π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a) ≫
        (Scheme.Modules.pullback g).map (e a).hom := by
    intro a
    rw [← Category.assoc, ← Functor.comp_map, (Scheme.Modules.pullbackComp y π).hom.naturality (e a).hom,
      Category.assoc, (Scheme.Modules.pullbackCongr w).hom.naturality (e a).hom]
  constructor
  · intro h a i
    obtain ⟨e0, he⟩ := h a i
    refine ⟨e0, ?_⟩
    have he' := congrArg (· ≫ (Scheme.Modules.pullback g).map (e a).hom) he
    simp only [Vert.Flag.ofIso, Iso.symm_hom, Functor.mapIso_inv, Category.assoc] at he'
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id] at he'
    simp only [Vert.Flag.ofIso, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rw [nat a]
    exact he'
  · intro h a i
    obtain ⟨e0, he⟩ := h a i
    refine ⟨e0, ?_⟩
    simp only [Vert.Flag.ofIso, Functor.mapIso_hom, Functor.map_comp, Category.assoc] at he
    rw [nat a] at he
    simp only [Vert.Flag.ofIso, Iso.symm_hom, Functor.mapIso_inv]
    rw [← Category.assoc, he]
    simp only [Category.assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

theorem isFlagBundle_of_iso : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (E E' : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → (∀ a, Nonempty (E a ≅ E' a)) → ∃ fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E' a)) (r a), IsFlagBundle π E' r fl' := by
  intro B Y π ι E E' r fl hfl he
  have e : ∀ a, E a ≅ E' a := fun a => (he a).some
  refine ⟨fun a => (fl a).ofIso ((Scheme.Modules.pullback π).mapIso (e a)), fun T g fl'' => ?_⟩
  obtain ⟨g', ⟨w, hg⟩, hu⟩ := hfl T g (fun a => (fl'' a).ofIso ((Scheme.Modules.pullback g).mapIso (e a)).symm)
  refine ⟨g', ⟨w, (isFlagBundle_cond_iso π E E' r e fl g fl'' g' w).1 hg⟩, fun y ⟨wy, hy⟩ => ?_⟩
  exact hu y ⟨wy, (isFlagBundle_cond_iso π E E' r e fl g fl'' y wy).2 hy⟩

end GlobalTheory.CovTest
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_transport_iso : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (E E' : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → (∀ a, Nonempty (E a ≅ E' a)) → ∃ fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E' a)) (r a), IsFlagBundle π E' r fl' := by
  atlas_forward_decl GlobalTheory.CovTest.isFlagBundle_of_iso
end

section
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

namespace GlobalTheory.VB

theorem exists_open_isVB_free_finite (B : Scheme.{0}) (ι : Type) [Finite ι] (E : ι → B.Modules) (r : ι → ℕ) :
    (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → ∀ b : B, ∃ U : B.Opens, b ∈ U ∧ ∀ a,
      Nonempty ((Scheme.Modules.pullback U.ι).obj (E a) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin (r a))) := by
  intro hE b
  have := Fintype.ofFinite ι
  choose V e hb he using fun a => hE a b
  refine ⟨Finset.univ.inf V, ?_, fun a => ?_⟩
  · rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf]
    simpa using hb
  · have hle : Finset.univ.inf V ≤ V a := Finset.inf_le (Finset.mem_univ a)
    set U := Finset.univ.inf V
    have hU : U.ι ''ᵁ ⊤ ≤ V a := (U.ι_image_le ⊤).trans hle
    exact ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app (E a)).symm ≪≫
      ((GlobalTheory.VB.isFrame_freeFrame U.toScheme (Fin (r a))).iso
        ((GlobalTheory.VB.isFrame_restrict_iff U.ι _).2 ((he a).res hU))).symm⟩

end GlobalTheory.VB
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_bundle_locally_free : ∀ (B : Scheme.{0}) (ι : Type) [Finite ι] (E : ι → B.Modules) (r : ι → ℕ), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → ∀ b : B, ∃ U : B.Opens, b ∈ U ∧ ∀ a, Nonempty ((Scheme.Modules.pullback U.ι).obj (E a) ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin (r a))) := by
  atlas_forward_decl GlobalTheory.VB.exists_open_isVB_free_finite
end

section
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.FlagFreeSmooth

open Limits

theorem exists_widePullback_smooth {B : Scheme.{0}} (ι : Type) [Fintype ι] :
    ∀ (Z : ι → Scheme.{0}) (ρ : ∀ a, Z a ⟶ B) (d : ι → ℕ), (∀ a, SmoothOfRelativeDimension (d a) (ρ a)) →
      ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (p : ∀ a, Y ⟶ Z a), (∀ a, p a ≫ ρ a = π) ∧
        SmoothOfRelativeDimension (∑ a, d a) π ∧
        ∀ (T : Scheme.{0}) (g : T ⟶ B) (h : ∀ a, T ⟶ Z a), (∀ a, h a ≫ ρ a = g) →
          ∃! g' : T ⟶ Y, g' ≫ π = g ∧ ∀ a, g' ≫ p a = h a := by
  refine @Fintype.induction_empty_option (fun α _ => ∀ (Z : α → Scheme.{0}) (ρ : ∀ a, Z a ⟶ B) (d : α → ℕ),
      (∀ a, SmoothOfRelativeDimension (d a) (ρ a)) →
      ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (p : ∀ a, Y ⟶ Z a), (∀ a, p a ≫ ρ a = π) ∧
        SmoothOfRelativeDimension (∑ a, d a) π ∧
        ∀ (T : Scheme.{0}) (g : T ⟶ B) (h : ∀ a, T ⟶ Z a), (∀ a, h a ≫ ρ a = g) →
          ∃! g' : T ⟶ Y, g' ≫ π = g ∧ ∀ a, g' ≫ p a = h a) ?_ ?_ ?_ ι _
  · intro α β _ e ih Z ρ d hρ
    letI : Fintype α := Fintype.ofEquiv β e.symm
    obtain ⟨Y, π, p, hp, hY, H⟩ := ih (fun a => Z (e a)) (fun a => ρ (e a)) (fun a => d (e a)) fun a => hρ _
    let p' : ∀ b, Y ⟶ Z b := Equiv.piCongrLeft (fun b => Y ⟶ Z b) e p
    have hp' (a : α) : p' (e a) = p a := Equiv.piCongrLeft_apply_apply _ _ _ _
    have hs : ∑ a, d (e a) = ∑ b, d b := Equiv.sum_comp e d
    rw [hs] at hY
    refine ⟨Y, π, p', e.forall_congr_right.1 fun a => by rw [hp', hp], hY, fun T g h hh => ?_⟩
    obtain ⟨g', ⟨h₁, h₂⟩, u⟩ := H T g (fun a => h (e a)) fun a => hh _
    exact ⟨g', ⟨h₁, e.forall_congr_right.1 fun a => by rw [hp', h₂]⟩,
      fun y hy => u y ⟨hy.1, fun a => by rw [← hp', hy.2]⟩⟩
  · intro Z ρ d _
    have h0 : (∑ a : PEmpty, d a) = 0 := by simp
    rw [h0]
    exact ⟨B, 𝟙 B, fun a => a.elim, fun a => a.elim, inferInstance,
      fun T g _ _ => ⟨g, ⟨Category.comp_id g, fun a => a.elim⟩, fun y hy => (Category.comp_id y).symm.trans hy.1⟩⟩
  · intro α _ ih Z ρ d hρ
    obtain ⟨Y, π, p, hp, hY, H⟩ := ih (fun a => Z (some a)) (fun a => ρ (some a)) (fun a => d (some a))
      fun a => hρ _
    have : SmoothOfRelativeDimension (d none) (pullback.fst π (ρ none)) :=
      haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := d none)
      MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension (d none)) π (ρ none) (hρ none)
    have hs : SmoothOfRelativeDimension (∑ a, d a) (pullback.fst π (ρ none) ≫ π) := by
      rw [Fintype.sum_option]
      infer_instance
    refine ⟨pullback π (ρ none), pullback.fst _ _ ≫ π,
      fun a => Option.rec (pullback.snd _ _) (fun a => pullback.fst _ _ ≫ p a) a, ?_, hs, fun T g h hh => ?_⟩
    · rintro (_ | a)
      · exact pullback.condition.symm
      · exact (Category.assoc _ _ _).trans (congrArg _ (hp a))
    · obtain ⟨g', ⟨h₁, h₂⟩, u⟩ := H T g (fun a => h (some a)) fun a => hh _
      refine ⟨pullback.lift g' (h none) (h₁.trans (hh none).symm), ⟨by rw [pullback.lift_fst_assoc, h₁], ?_⟩,
        fun y hy => ?_⟩
      · rintro (_ | a)
        · exact pullback.lift_snd _ _ _
        · exact (pullback.lift_fst_assoc _ _ _ _).trans (h₂ a)
      · refine pullback.hom_ext ?_ ?_
        · rw [pullback.lift_fst]
          exact u _ ⟨(Category.assoc _ _ _).trans hy.1, fun a => (Category.assoc _ _ _).trans (hy.2 (some a))⟩
        · rw [pullback.lift_snd]
          exact hy.2 none

end GlobalTheory.FlagFreeSmooth

namespace GlobalTheory.FlagFreeSmooth

theorem smooth_flStr_unit (n : ℕ) : SmoothOfRelativeDimension (n * (n - 1) / 2) (GlobalTheory.FlagZ.flStr Unit n) := by
  have h := (GlobalTheory.FlagZ.smooth_dim_isArithVar_part Unit (Unit × Fin (n + 1)) n Prod.fst Prod.snd).1
  rw [(GlobalTheory.FlagZ.Count.card_cellVar Unit n).1] at h
  unfold dimFl at h
  simpa using h

end GlobalTheory.FlagFreeSmooth

namespace GlobalTheory.FlagFreeSmooth

open GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ

def univFlag (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) :
    Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (GlobalTheory.QCoh.freeModule (X := Sp ℤ) (Fin N))) N where
  F := F ι N τ
  ι := incl ι N τ
  isSubbundle i := (GlobalTheory.T.tautological_subbundle_rank ι N τ i).2
  isVB i := (GlobalTheory.T.tautological_subbundle_rank ι N τ i).1
  step := step ι N τ
  step_ι := step_incl ι N τ
  isIso_last := isIso_incl_last ι N τ

theorem isFlagBundle_univFlag (ι : Type) [Fintype ι] (N : ℕ) :
    IsFlagBundle (flStr ι N) (fun _ : ι => SheafOfModules.free (R := (Sp ℤ).ringCatSheaf) (Fin N)) (fun _ => N)
      (univFlag ι N) := by
  intro T g fl'
  obtain ⟨g', hg'⟩ := GlobalTheory.T.flag_variety_lift_exists ι N T g fl'
  exact ⟨g', hg', fun y hy => GlobalTheory.T.flag_variety_lift_unique ι N T g fl' y g' hy hg'⟩

theorem exists_single_int : ∀ (n : ℕ), ∃ (Y : Scheme.{0}) (π : Y ⟶ Sp ℤ) (fl : ∀ _ : Unit, Vert.Flag ((Scheme.Modules.pullback π).obj (SheafOfModules.free (R := (Sp ℤ).ringCatSheaf) (Fin n))) n), IsFlagBundle π (fun _ : Unit => SheafOfModules.free (R := (Sp ℤ).ringCatSheaf) (Fin n)) (fun _ => n) fl ∧ SmoothOfRelativeDimension (n * (n - 1) / 2) π := fun n =>
  ⟨Fl Unit n, flStr Unit n, univFlag Unit n, isFlagBundle_univFlag Unit n, smooth_flStr_unit n⟩

end GlobalTheory.FlagFreeSmooth

namespace GlobalTheory.FlagFreeSmooth

open Limits

theorem exists_single (B : Scheme.{0}) (n : ℕ) :
    ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ _ : Unit, Vert.Flag ((Scheme.Modules.pullback π).obj
      (SheafOfModules.free (R := B.ringCatSheaf) (Fin n))) n),
      IsFlagBundle π (fun _ : Unit => SheafOfModules.free (R := B.ringCatSheaf) (Fin n)) (fun _ => n) fl ∧
      SmoothOfRelativeDimension (n * (n - 1) / 2) π := by
  obtain ⟨Y, π, fl, hfl, hs⟩ := exists_single_int n
  let g : B ⟶ Sp ℤ := specZIsTerminal.from B
  have hbc := GlobalTheory.T.isFlagBundle_pullback' (Sp ℤ) Y B π g Unit _ (fun _ => n) fl hfl
  obtain ⟨e⟩ := GlobalTheory.T.pullback_free_module_iso B (Sp ℤ) g n
  have hiso := GlobalTheory.FlagIsoBundle.isFlagBundle_of_iso B (pullback π g) (pullback.snd π g) Unit _
    (fun _ : Unit => SheafOfModules.free (R := B.ringCatSheaf) (Fin n)) (fun _ => n) _ (fun _ => e) hbc
  have : SmoothOfRelativeDimension (n * (n - 1) / 2) (pullback.snd π g) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := n * (n - 1) / 2)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension (n * (n - 1) / 2)) π g hs
  exact ⟨_, _, _, hiso, this⟩

theorem main : ∀ (B : Scheme.{0}) (ι : Type) [Fintype ι] (r : ι → ℕ), ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (SheafOfModules.free (R := B.ringCatSheaf) (Fin (r a)))) (r a)), IsFlagBundle π (fun a => SheafOfModules.free (R := B.ringCatSheaf) (Fin (r a))) r fl ∧ SmoothOfRelativeDimension (∑ a, r a * (r a - 1) / 2) π := by
  intro B ι _ r
  choose Z ρ fl hfl hs using fun a => exists_single B (r a)
  obtain ⟨Y, π, p, hp, hY, H⟩ := exists_widePullback_smooth ι Z ρ (fun a => r a * (r a - 1) / 2) hs
  exact ⟨Y, π, _, GlobalTheory.FlagFamily.isFlagBundle_of_widePullback
    (fun a => SheafOfModules.free (R := B.ringCatSheaf) (Fin (r a))) r ρ fl hfl π p hp H, hY⟩

end GlobalTheory.FlagFreeSmooth
end
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_flag_bundle_smooth_relative_dim : ∀ (B : Scheme.{0}) (ι : Type) [Fintype ι] (r : ι → ℕ), ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (SheafOfModules.free (R := B.ringCatSheaf) (Fin (r a)))) (r a)), IsFlagBundle π (fun a => SheafOfModules.free (R := B.ringCatSheaf) (Fin (r a))) r fl ∧ SmoothOfRelativeDimension (∑ a, r a * (r a - 1) / 2) π := by
  atlas_forward_decl GlobalTheory.FlagFreeSmooth.main
end

section
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
namespace GlobalTheory.FlagSmooth

theorem smooth_of_isFlagBundle : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules)
    (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) →
    IsFlagBundle π E r fl → SmoothOfRelativeDimension (∑ a, r a * (r a - 1) / 2) π := by
  intro B Y π ι _ E r fl hE hfl
  haveI : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension (∑ a, r a * (r a - 1) / 2)) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  choose U hU hfree using GlobalTheory.T.vector_bundle_locally_free B ι E r hE
  have hcov : TopologicalSpace.IsOpenCover U :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hU x⟩
  refine IsZariskiLocalAtTarget.of_openCover (B.openCoverOfIsOpenCover U hcov) fun b => ?_
  change SmoothOfRelativeDimension _ (Limits.pullback.snd π (U b).ι)
  have h1 := GlobalTheory.T.flag_bundle_base_change B Y (U b) π ι E r fl hfl (U b).ι
  obtain ⟨Y0, π0, fl0, h0, hs⟩ := GlobalTheory.T.free_flag_bundle_smooth_relative_dim (U b) ι r
  obtain ⟨fl0', h0'⟩ := GlobalTheory.T.flag_bundle_transport_iso (U b) Y0 π0 ι _ (fun a => (Scheme.Modules.pullback (U b).ι).obj (E a)) r fl0 h0
    (fun a => ⟨(hfree b a).some.symm⟩)
  obtain ⟨e, he⟩ := GlobalTheory.T.flag_bundle_family_unique_iso (U b) Y0 _ π0 (Limits.pullback.snd π (U b).ι) ι _ r fl0' _ h0' h1
  have e' : Limits.pullback.snd π (U b).ι = e.inv ≫ π0 := by rw [← he, Iso.inv_hom_id_assoc]
  rw [e']
  first
    | exact (@MorphismProperty.cancel_left_of_respectsIso _ _ _ (HasRingHomProperty.respectsIso _) _ _ _ _ _).2 hs
    | exact (@MorphismProperty.cancel_left_of_respectsIso _ _ _ (IsZariskiLocalAtTarget.toRespectsIso) _ _ _ _ _).2 hs
    | (haveI : SmoothOfRelativeDimension 0 e.inv := inferInstance
       simpa using (inferInstance : SmoothOfRelativeDimension (0 + ∑ a, r a * (r a - 1) / 2) (e.inv ≫ π0)))

end GlobalTheory.FlagSmooth
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_smooth_relative_dimension : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → SmoothOfRelativeDimension (∑ a, r a * (r a - 1) / 2) π := by
  atlas_forward_decl GlobalTheory.FlagSmooth.smooth_of_isFlagBundle
end
