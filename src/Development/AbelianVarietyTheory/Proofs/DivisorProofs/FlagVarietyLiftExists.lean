import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagLocallyAdaptedAffineFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSecOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulesIsoOfMatchingFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalSubbundleRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoInclLastStatement

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_locally_adapted_affine_frame : ∀ {ι : Type} [Fintype ι] {N : ℕ} {T : Scheme.{0}} (g : T ⟶ Sp ℤ)
    (fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N) (t : T),
    ∃ V : T.Opens, t ∈ V ∧ IsAffineOpen V ∧ ∃ G : ι → GL (Fin N) Γ(T, V), Loc.Adapted g fl' V G := by
  first | exact @GlobalTheory.FlagZ.Loc.exists_adapted | exact GlobalTheory.FlagZ.Loc.exists_adapted | (intros; apply GlobalTheory.FlagZ.Loc.exists_adapted <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)

namespace GlobalTheory.FlagZ.Loc

variable {N : ℕ} {T : Scheme.{0}}

theorem isQuasicoherent_stdE_ovl : (Taut.stdE N).IsQuasicoherent :=
  (isVB_freeModule_fin (Sp ℤ) N).isQuasicoherent

theorem isFrame_stdSec_ovl (g : T ⟶ Sp ℤ) (U : T.Opens) (hU : U ≤ g ⁻¹ᵁ ⊤) :
    IsFrame fun i : Fin N =>
      GlobalTheory.QCoh.pullbackSections g (Taut.stdE N) hU (freeFrame (Sp ℤ) (Fin N) i) := by
  haveI := isQuasicoherent_stdE_ovl (N := N)
  have h := ((isFrame_freeFrame (Sp ℤ) (Fin N)).pullback g).res hU
  have e : (fun i : Fin N =>
      GlobalTheory.QCoh.pullbackSections g (Taut.stdE N) hU (freeFrame (Sp ℤ) (Fin N) i)) = fun i =>
      resM _ hU (GlobalTheory.QCoh.pullbackSections g (Taut.stdE N) (le_refl (g ⁻¹ᵁ ⊤)) (freeFrame (Sp ℤ) (Fin N) i)) :=
    funext fun i => (QCoh.res_pullbackSections g _ _ _ _).symm
  rw [e]
  exact h

theorem resM_colSecOn_ovl (g : T ⟶ Sp ℤ) {U V : T.Opens} (h : U ≤ V) (M : Matrix (Fin N) (Fin N) Γ(T, V))
    (j : Fin N) :
    resM _ h (colSecOn g V M j) = colSecOn g U (M.map (resG T h)) j := by
  simp only [colSecOn, map_sum, resM_smul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
  exact QCoh.res_pullbackSections g _ _ _ _

theorem Adapted.restr {ι : Type} {g : T ⟶ Sp ℤ}
    {fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N} {U V : T.Opens}
    {G : ι → GL (Fin N) Γ(T, V)} (hG : Adapted g fl' V G) (h : U ≤ V) :
    Adapted g fl' U fun a => Matrix.GeneralLinearGroup.map (resG T h) (G a) := by
  intro a l
  obtain ⟨s, hs, hsι⟩ := hG a l
  refine ⟨fun j => resM _ h (s j), hs.res h, fun j => ?_⟩
  rw [app_resM, hsι j, resM_colSecOn_ovl]
  rfl

theorem exists_col_comb_ovl {ι : Type} {g : T ⟶ Sp ℤ}
    {fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N} {U : T.Opens}
    {G H : ι → GL (Fin N) Γ(T, U)} (hG : Adapted g fl' U G) (hH : Adapted g fl' U H) (a : ι) (j : Fin N) :
    ∃ c : Fin (j.succ : ℕ) → Γ(T, U),
      ∀ i, (H a).1 i j = ∑ k, (G a).1 i (Fin.castLE j.succ.is_le k) * c k := by
  obtain ⟨s, hs, hsι⟩ := hG a j.succ
  obtain ⟨t, -, htι⟩ := hH a j.succ
  obtain ⟨c, hc⟩ := (hs U le_rfl).2 (t (Fin.last j))
  simp only [resM_self, Fintype.linearCombination_apply] at hc
  have e1 := congrArg (((fl' a).ι j.succ).app U) hc
  simp only [map_sum, Scheme.Modules.Hom.app_smul, hsι, htι] at e1
  have hj : Fin.castLE j.succ.is_le (Fin.last j) = j := Fin.ext rfl
  rw [hj] at e1
  simp only [colSecOn, Finset.smul_sum, smul_smul] at e1
  rw [Finset.sum_comm] at e1
  simp only [← Finset.sum_smul] at e1
  have hE := (isFrame_stdSec_ovl (N := N) g U (fun _ _ => trivial) U le_rfl).1
  simp only [resM_self] at hE
  refine ⟨c, fun i => ?_⟩
  have := congrFun (hE (a₁ := fun i => (∑ k, c k * (G a).1 i (Fin.castLE j.succ.is_le k)))
    (a₂ := fun i => (H a).1 i j) (by simp only [Fintype.linearCombination_apply]; exact e1)) i
  rw [← this]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem blockTriangular_inv_mul_ovl {ι : Type} {g : T ⟶ Sp ℤ}
    {fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N} {U : T.Opens}
    {G H : ι → GL (Fin N) Γ(T, U)} (hG : Adapted g fl' U G) (hH : Adapted g fl' U H) (a : ι) :
    ((G a)⁻¹ * H a).1.BlockTriangular id := by
  intro k j hjk
  obtain ⟨c, hc⟩ := exists_col_comb_ovl hG hH a j
  rw [Units.val_mul, Matrix.mul_apply]
  simp only [hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun m _ => ?_
  simp only [← mul_assoc, ← Finset.sum_mul]
  rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_ne, zero_mul]
  intro h
  have h1 := congrArg Fin.val h
  have h2 := m.isLt
  simp only [Fin.coe_castLE, Fin.val_succ] at h1 h2
  have h3 : (j : ℕ) < k := hjk
  omega

theorem flagPt_eq_of_adapted_ovl {ι : Type} [Fintype ι] {g : T ⟶ Sp ℤ}
    {fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N} {U : T.Opens}
    {G H : ι → GL (Fin N) Γ(T, U)} (hG : Adapted g fl' U G) (hH : Adapted g fl' U H) :
    flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G = flagPt Prod.fst Prod.snd H :=
  (flagPt_mul_upper G (G⁻¹ * H) fun a => blockTriangular_inv_mul_ovl hG hH a).symm.trans
    (congrArg _ (mul_inv_cancel_left G H))

theorem flagPt_inf_eq : ∀ {ι : Type} [Fintype ι] {N : ℕ} {T : Scheme.{0}} (g : T ⟶ Sp ℤ)
    (fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N) (V W : T.Opens)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (G : ι → GL (Fin N) Γ(T, V)) (H : ι → GL (Fin N) Γ(T, W)),
    Loc.Adapted g fl' V G → Loc.Adapted g fl' W H →
    T.homOfLE (inf_le_left : V ⊓ W ≤ V) ≫ hV.isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G =
      T.homOfLE (inf_le_right : V ⊓ W ≤ W) ≫ hW.isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd H := by
  intro ι _ N T g fl' V W hV hW G H hG hH
  rw [hV.isoSpec_hom, hW.isoSpec_hom, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]
  refine congrArg ((V ⊓ W).toSpecΓ ≫ ·) ?_
  change spMap (resG T _) ≫ _ = spMap (resG T _) ≫ _
  rw [spMap_flagPt, spMap_flagPt]
  exact flagPt_eq_of_adapted_ovl (hG.restr inf_le_left) (hH.restr inf_le_right)

end GlobalTheory.FlagZ.Loc
end
end

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frames_agree_on_overlap : ∀ {ι : Type} [Fintype ι] {N : ℕ} {T : Scheme.{0}} (g : T ⟶ Sp ℤ)
    (fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N) (V W : T.Opens)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (G : ι → GL (Fin N) Γ(T, V)) (H : ι → GL (Fin N) Γ(T, W)),
    Loc.Adapted g fl' V G → Loc.Adapted g fl' W H →
    T.homOfLE (inf_le_left : V ⊓ W ≤ V) ≫ hV.isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G =
      T.homOfLE (inf_le_right : V ⊓ W ≤ W) ≫ hW.isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd H := by
  atlas_forward_decl GlobalTheory.FlagZ.Loc.flagPt_inf_eq
end

section
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory

namespace GlobalTheory

open CategoryTheory.Limits

theorem glue_homs_of_opens_cover {X Y : Scheme.{0}} {κ : Type} (U : κ → X.Opens) (hU : ⨆ k, U k = ⊤)
    (f : ∀ k, (U k).toScheme ⟶ Y)
    (hf : ∀ k l, X.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ f k =
      X.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ f l) :
    ∃ g : X ⟶ Y, ∀ k, (U k).ι ≫ g = f k := by
  let 𝒰 := X.openCoverOfIsOpenCover U hU
  have hc : ∀ a b, pullback.fst (U a).ι (U b).ι ≫ f a = pullback.snd (U a).ι (U b).ι ≫ f b := by
    intro a b
    have P := isPullback_opens_inf (U a) (U b)
    rw [← cancel_epi P.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_snd_assoc]
    exact hf a b
  exact ⟨𝒰.glueMorphisms f hc, fun k => 𝒰.ι_glueMorphisms f hc k⟩

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scheme_morphisms_glue_open_cover : ∀ {X Y : Scheme.{0}} {κ : Type} (U : κ → X.Opens), ⨆ k, U k = ⊤ → ∀ (f : ∀ k, (U k).toScheme ⟶ Y),
    (∀ k l, X.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ f k = X.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ f l) →
    ∃ g : X ⟶ Y, ∀ k, (U k).ι ≫ g = f k := by
  atlas_forward_decl GlobalTheory.glue_homs_of_opens_cover
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modules_iso_of_matching_frames : ∀ {X : Scheme.{0}} {F₁ F₂ E : X.Modules} (m₁ : F₁ ⟶ E) (m₂ : F₂ ⟶ E) [Mono m₂] (r : ℕ),
    (∀ x : X, ∃ (U : X.Opens) (s₁ : Fin r → Γ(F₁, U)) (s₂ : Fin r → Γ(F₂, U)), x ∈ U ∧ IsFrame s₁ ∧ IsFrame s₂ ∧
      ∀ j, m₁.app U (s₁ j) = m₂.app U (s₂ j)) →
    ∃ e : F₁ ≅ F₂, e.hom ≫ m₂ = m₁ := by
  first | exact @GlobalTheory.VB.exists_iso_of_frames_app_eq | exact GlobalTheory.VB.exists_iso_of_frames_app_eq | (intros; apply GlobalTheory.VB.exists_iso_of_frames_app_eq <;> assumption)
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res)
open GlobalTheory.Twist (resM resM_resM app_resM resM_self)

namespace GlobalTheory.FlagZ.LocTaut

variable {S T Y Z : Scheme.{0}}

def compIso (j : S ⟶ T) [IsOpenImmersion j] (f : T ⟶ Y) :
    Scheme.Modules.pullback (j ≫ f) ≅ Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor j :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ f)).ofNatIsoRight
      (Scheme.Modules.pushforwardComp j f).symm).leftAdjointUniq
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (Scheme.Modules.restrictAdjunction j))

theorem compIso_app_pullbackSections (j : S ⟶ T) [IsOpenImmersion j] (f : T ⟶ Y) (G : Y.Modules)
    (h : ⊤ ≤ (j ≫ f) ⁻¹ᵁ ⊤) (h' : j ''ᵁ ⊤ ≤ f ⁻¹ᵁ ⊤) (s : Γ(G, ⊤)) :
    ((compIso j f).hom.app G).app ⊤ (pullbackSections (j ≫ f) G h s) = pullbackSections f G h' s := by
  have := Adjunction.unit_leftAdjointUniq_hom_app
    ((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ f)).ofNatIsoRight
      (Scheme.Modules.pushforwardComp j f).symm)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (Scheme.Modules.restrictAdjunction j)) G
  have H := congr(($this).app ⊤ s)
  refine Eq.trans ?_ H
  exact congrArg _ (QCoh.res_self _ le_rfl _)

theorem pullbackComp_hom_app (b : S ⟶ Y) (a : Y ⟶ Z) (E : Z.Modules) {U : Z.Opens} {V : Y.Opens}
    {W : S.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : W ≤ b ⁻¹ᵁ V) (h : W ≤ (b ≫ a) ⁻¹ᵁ U) (s : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp b a).hom.app E).app W
      (pullbackSections b _ h₂ (pullbackSections a E h₁ s)) = pullbackSections (b ≫ a) E h s := by
  rw [← Vert.DivPull.pullbackComp_inv_app b a E h₁ h₂ h]
  exact congr(($((Scheme.Modules.pullbackComp b a).inv_hom_id_app E)).app W _)

theorem exists_frame_image (j : S ⟶ T) [IsOpenImmersion j] (f : T ⟶ Y) (p : S ⟶ Y) (hp : p = j ≫ f) (q : Y ⟶ Z)
    (E : Z.Modules) (F : Y.Modules) (i : F ⟶ (Scheme.Modules.pullback q).obj E) {κ μ : Type} [Fintype κ] [Fintype μ]
    (e : μ → Γ(E, ⊤)) (c : κ → μ → Γ(S, ⊤)) (s : κ → Γ((Scheme.Modules.pullback p).obj F, ⊤)) (hs : IsFrame s)
    (h₀ : ⊤ ≤ (p ≫ q) ⁻¹ᵁ ⊤)
    (h : ∀ k, ((Scheme.Modules.pullback p).map i ≫ (Scheme.Modules.pullbackComp p q).hom.app E).app ⊤ (s k) =
      ∑ m, c k m • pullbackSections (p ≫ q) E h₀ (e m))
    (V : T.Opens) (hV : V ≤ j ''ᵁ ⊤) (h₁ : V ≤ (f ≫ q) ⁻¹ᵁ ⊤) :
    ∃ t : κ → Γ((Scheme.Modules.pullback f).obj F, V), IsFrame t ∧ ∀ k,
      ((Scheme.Modules.pullback f).map i ≫ (Scheme.Modules.pullbackComp f q).hom.app E).app V (t k) =
        ∑ m, resG T hV ((j.appIso ⊤).inv (c k m)) • pullbackSections (f ≫ q) E h₁ (e m) := by
  subst hp
  let t : κ → Γ((Scheme.Modules.pullback f).obj F, j ''ᵁ ⊤) := fun k => ((compIso j f).hom.app F).app ⊤ (s k)
  have ht : IsFrame t := (isFrame_restrict_iff j t).1 (hs.map_iso ((compIso j f).hom.app F))
  refine ⟨_, ht.res hV, fun k => ?_⟩
  have h2 : ((Scheme.Modules.pullback (j ≫ f)).map i).app ⊤ (s k) =
      ∑ m, c k m • pullbackSections (j ≫ f) _ (V := ⊤) le_top (pullbackSections q E (U := ⊤) le_top (e m)) := by
    refine (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.pullbackComp (j ≫ f) q).hom.app E).app ⊤)).1 ((h k).trans ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Scheme.Modules.Hom.app_smul, pullbackComp_hom_app]
  have h3 : ((Scheme.Modules.pullback f).map i).app (j ''ᵁ ⊤) (t k) =
      ∑ m, (j.appIso ⊤).inv (c k m) • pullbackSections f _ (V := ⊤) le_top (pullbackSections q E (U := ⊤) le_top (e m)) := by
    have hn := congr(($((compIso j f).hom.naturality i)).app ⊤ (s k))
    refine hn.symm.trans ?_
    refine (congrArg (((compIso j f).hom.app _).app ⊤) h2).trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Scheme.Modules.Hom.app_smul, compIso_app_pullbackSections j f _ _ le_top]
    rfl
  refine (app_resM _ hV _).trans ?_
  refine (congrArg (fun x => resM _ hV (((Scheme.Modules.pullbackComp f q).hom.app E).app _ x)) h3).trans ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Scheme.Modules.Hom.app_smul, pullbackComp_hom_app f q E _ _ le_top, Twist.resM_smul]
  exact congrArg _ (res_pullbackSections _ _ _ _ _)

theorem exists_frame_pullback_taut : ∀ (ι : Type) [Fintype ι] (N : ℕ)
    (fl : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N)) N), Taut.IsTaut ι N fl →
    ∀ (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (g' : T ⟶ Fl ι N) (w : g' ≫ flStr ι N = g) (V : T.Opens) (hV : IsAffineOpen V)
    (G : ι → GL (Fin N) Γ(T, V)), V.ι ≫ g' = hV.isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G →
    ∀ (a : ι) (l : Fin (N + 1)),
    ∃ s : Fin l → Γ((Scheme.Modules.pullback g').obj ((fl a).F l), V), IsFrame s ∧ ∀ j,
      ((Scheme.Modules.pullback g').map ((fl a).ι l) ≫
        (Scheme.Modules.pullbackComp g' (flStr ι N)).hom.app (Taut.stdE N) ≫
          (Scheme.Modules.pullbackCongr w).hom.app (Taut.stdE N)).app V (s j) =
        Loc.colSecOn g V (G a).1 (Fin.castLE l.is_le j) := by
  intro ι _ N fl hfl T g g' w V hV G hG a l
  subst w
  obtain ⟨s, hs, h⟩ := hfl Γ(T, V) G a l
  have hp : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G = hV.fromSpec ≫ g' := by
    rw [IsAffineOpen.fromSpec, Category.assoc, hG]
    exact (hV.isoSpec.inv_hom_id_assoc _).symm
  obtain ⟨t, ht, h'⟩ := exists_frame_image hV.fromSpec g' _ hp (flStr ι N) (Taut.stdE N) _ ((fl a).ι l)
    (freeFrame (Sp ℤ) (Fin N)) _ s hs _ h V (QCoh.fromSpec_image_top hV).ge le_top
  refine ⟨t, ht, fun k => (h' k).trans (Finset.sum_congr rfl fun m _ => ?_)⟩
  congr 1
  have := QCoh.fromSpec_appIso_inv_res hV ⊤ ((G a).1 m (Fin.castLE l.is_le k))
  rw [show ∀ x, (Spec Γ(T, V)).presheaf.map (⊤ : (Spec Γ(T, V)).Opens).leTop.op x = x from
    QCoh.res_self_ring (X := Spec Γ(T, V)) le_rfl] at this
  refine (congrArg (resG T _) this).trans ?_
  exact (LB.resG_resG _ _ _).trans (LB.resG_self _ _)

end GlobalTheory.FlagZ.LocTaut
end
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_point_tautological_frame : ∀ (ι : Type) [Fintype ι] (N : ℕ)
    (fl : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N)) N), Taut.IsTaut ι N fl →
    ∀ (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (g' : T ⟶ Fl ι N) (w : g' ≫ flStr ι N = g) (V : T.Opens) (hV : IsAffineOpen V)
    (G : ι → GL (Fin N) Γ(T, V)), V.ι ≫ g' = hV.isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G →
    ∀ (a : ι) (l : Fin (N + 1)),
    ∃ s : Fin l → Γ((Scheme.Modules.pullback g').obj ((fl a).F l), V), IsFrame s ∧ ∀ j,
      ((Scheme.Modules.pullback g').map ((fl a).ι l) ≫
        (Scheme.Modules.pullbackComp g' (flStr ι N)).hom.app (Taut.stdE N) ≫
          (Scheme.Modules.pullbackCongr w).hom.app (Taut.stdE N)).app V (s j) =
        Loc.colSecOn g V (G a).1 (Fin.castLE l.is_le j) := by
  first | exact @GlobalTheory.FlagZ.LocTaut.exists_frame_pullback_taut | exact GlobalTheory.FlagZ.LocTaut.exists_frame_pullback_taut | (intros; apply GlobalTheory.FlagZ.LocTaut.exists_frame_pullback_taut <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.VB GlobalTheory.FlagZ

namespace GlobalTheory.FlagZ

theorem exists_classifying : ∀ (ι : Type) [Fintype ι] (N : ℕ) (fl : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback (GlobalTheory.FlagZ.flStr ι N)).obj (GlobalTheory.FlagZ.Taut.stdE N)) N), GlobalTheory.FlagZ.Taut.IsTaut ι N fl →
  ∀ (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (fl' : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback g).obj (GlobalTheory.FlagZ.Taut.stdE N)) N),
    ∃ g' : T ⟶ GlobalTheory.FlagZ.Fl ι N, ∃ w : g' ≫ GlobalTheory.FlagZ.flStr ι N = g, ∀ a i,
      ∃ e : (Scheme.Modules.pullback g').obj ((fl a).F i) ≅ (fl' a).F i,
        e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g').map ((fl a).ι i) ≫
          (Scheme.Modules.pullbackComp g' (GlobalTheory.FlagZ.flStr ι N)).hom.app (GlobalTheory.FlagZ.Taut.stdE N) ≫
            (Scheme.Modules.pullbackCongr w).hom.app (GlobalTheory.FlagZ.Taut.stdE N) := by
  intro ι _ N fl hfl T g fl'
  choose V hxV hV G hG using fun t : T => GlobalTheory.T.flag_locally_adapted_affine_frame g fl' t
  have hU : ⨆ t, V t = ⊤ := top_le_iff.1 fun t _ => TopologicalSpace.Opens.mem_iSup.2 ⟨t, hxV t⟩
  obtain ⟨g', hg'⟩ := GlobalTheory.T.scheme_morphisms_glue_open_cover V hU
    (fun t => (hV t).isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (G t))
    fun k l => GlobalTheory.T.adapted_frames_agree_on_overlap g fl' (V k) (V l) (hV k) (hV l) (G k) (G l) (hG k) (hG l)
  have w : g' ≫ flStr ι N = g := toZ_ext _ _
  refine ⟨g', w, fun a i => ?_⟩
  obtain ⟨e, he⟩ := GlobalTheory.T.modules_iso_of_matching_frames ((Scheme.Modules.pullback g').map ((fl a).ι i) ≫
      (Scheme.Modules.pullbackComp g' (flStr ι N)).hom.app (Taut.stdE N) ≫
        (Scheme.Modules.pullbackCongr w).hom.app (Taut.stdE N)) ((fl' a).ι i) i fun x => by
    obtain ⟨s₁, hs₁, e₁⟩ := GlobalTheory.T.flag_point_tautological_frame ι N fl hfl T g g' w (V x) (hV x) (G x) (hg' x) a i
    obtain ⟨s₂, hs₂, e₂⟩ := hG x a i
    exact ⟨V x, s₁, s₂, hxV x, hs₁, hs₂, fun j => (e₁ j).trans (e₂ j).symm⟩
  exact ⟨e, he⟩

end GlobalTheory.FlagZ
end
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautological_flag_universal : ∀ (ι : Type) [Fintype ι] (N : ℕ) (fl : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback (GlobalTheory.FlagZ.flStr ι N)).obj (GlobalTheory.FlagZ.Taut.stdE N)) N), GlobalTheory.FlagZ.Taut.IsTaut ι N fl →
  ∀ (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (fl' : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback g).obj (GlobalTheory.FlagZ.Taut.stdE N)) N),
    ∃ g' : T ⟶ GlobalTheory.FlagZ.Fl ι N, ∃ w : g' ≫ GlobalTheory.FlagZ.flStr ι N = g, ∀ a i,
      ∃ e : (Scheme.Modules.pullback g').obj ((fl a).F i) ≅ (fl' a).F i,
        e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g').map ((fl a).ι i) ≫
          (Scheme.Modules.pullbackComp g' (GlobalTheory.FlagZ.flStr ι N)).hom.app (GlobalTheory.FlagZ.Taut.stdE N) ≫
            (Scheme.Modules.pullbackCongr w).hom.app (GlobalTheory.FlagZ.Taut.stdE N) := by
  atlas_forward_decl GlobalTheory.FlagZ.exists_classifying
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

noncomputable section
namespace GlobalTheory.FlagZ.TautPull
open GlobalTheory.VB
open GlobalTheory.QCoh (appLinear appLinear_apply pullbackSections)
open GlobalTheory.Twist (app_resM resM_resM resM_smul resM_self)

private theorem glue_frame {X : Scheme.{0}} {P Q : X.Modules} (m : P ⟶ Q) {l : ℕ} (c : Fin l → Γ(Q, ⊤))
    (hc : ∀ V : X.Opens, LinearIndependent Γ(X, V) fun j => resM Q (le_top : V ≤ ⊤) (c j))
    (H : ∀ y : X, ∃ (W : X.Opens) (t : Fin l → Γ(P, W)), y ∈ W ∧ VB.IsFrame t ∧
      ∀ j, m.app W (t j) = resM Q (le_top : W ≤ ⊤) (c j)) :
    ∃ s : Fin l → Γ(P, ⊤), VB.IsFrame s ∧ ∀ j, m.app ⊤ (s j) = c j := by
  choose W t hy ht hm using H
  have hres (y : X) (V : X.Opens) (h : V ≤ W y) (j : Fin l) :
      m.app V (resM P h (t y j)) = resM Q (le_top : V ≤ ⊤) (c j) := by
    rw [app_resM, hm, resM_resM]
  have hinj (y : X) (V : X.Opens) (h : V ≤ W y) : Function.Injective (m.app V) := by
    rw [← show ⇑(appLinear m V) = ⇑(m.app V) from rfl, injective_iff_map_eq_zero]
    intro s hs
    obtain ⟨a, rfl⟩ := (ht y V h).2 s
    rw [Fintype.linearCombination_apply, map_sum] at hs
    simp only [map_smul, appLinear_apply, hres] at hs
    rw [show a = 0 from funext (Fintype.linearIndependent_iff.1 (hc V) a hs), map_zero]
  have hcov : (⊤ : X.Opens) ≤ iSup W := fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩
  choose s hs using fun j => GlobalTheory.Twist.exists_sec_of_cover (F := P) W (fun _ => le_top) hcov (fun y => t y j)
    fun y z => hinj y _ inf_le_left ((hres y _ _ j).trans (hres z _ _ j).symm)
  refine ⟨s, isFrame_of_forall_exists fun V h x hx => ⟨V ⊓ W x, inf_le_left, ⟨hx, hy x⟩, ?_⟩, fun j => ?_⟩
  · have := ht x (V ⊓ W x) inf_le_right
    simp only [← hs, resM_resM] at this
    exact this
  · refine GlobalTheory.Twist.sec_ext_of_cover W (fun _ => le_top) hcov fun y => ?_
    rw [← app_resM, hs, hm]

private theorem isFrame_colSec (N : ℕ) (A : Type) [CommRing A] (x : Sp A ⟶ Sp ℤ) (g : GL (Fin N) A) :
    VB.IsFrame (GlobalTheory.FlagZ.Taut.colSec x g.1) :=
  isFrame_sum_smul_of_isUnit ((isFrame_freeFrame (Sp ℤ) (Fin N)).pullback x)
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.mapMatrix g.1) (g.isUnit.map _)

private theorem exists_isFrame_sub {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ}
    (P : VB.Sub F) (c : Fin N → Γ(F, U)) (hc : VB.IsFrame c) (l : ℕ) (hl : l ≤ N)
    (hP : ∀ (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V)),
      (∑ j, a j • resM F h (c j)) ∈ P.sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) :
    ∃ e : Fin l → Γ(P.toMod, U), VB.IsFrame e ∧ ∀ j, P.incl.app U (e j) = c (Fin.castLE hl j) := by
  classical
  have hmem (k : Fin l) : c (Fin.castLE hl k) ∈ P.sec U := by
    have := (hP U le_rfl (Pi.single (Fin.castLE hl k) 1)).2 fun j hj => by
      rw [Pi.single_apply, if_neg]
      rintro rfl
      simp at hj
      omega
    simpa [Pi.single_apply, Finset.sum_ite_eq'] using this
  let e : Fin l → Γ(P.toMod, U) := fun k => P.mkSec _ (hmem k)
  have hincl (V : X.Opens) (h : V ≤ U) (b : Fin l → Γ(X, V)) :
      P.incl.app V (Fintype.linearCombination Γ(X, V) (fun k => resM P.toMod h (e k)) b) =
        ∑ k, b k • resM F h (c (Fin.castLE hl k)) := by
    rw [Fintype.linearCombination_apply, ← appLinear_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, appLinear_apply, app_resM]
    rfl
  refine ⟨e, fun V h => ⟨fun b b' hbb => ?_, fun s => ?_⟩, fun _ => rfl⟩
  · have h1 := congrArg (P.incl.app V) hbb
    rw [hincl, hincl] at h1
    exact funext (Fintype.linearIndependent_iffₛ.1
      (((isFrame_iff.1 hc V h).1).comp _ (Fin.castLE_injective hl)) b b' h1)
  · obtain ⟨a, ha⟩ := (hc V h).2 (P.incl.app V s)
    rw [Fintype.linearCombination_apply] at ha
    have hz := (hP V h a).1 (ha ▸ P.incl_app_mem s)
    refine ⟨fun k => a (Fin.castLE hl k), P.incl_app_injective V ?_⟩
    rw [hincl, ← ha]
    exact sum_castLE_eq hl (fun j => a j • resM F h (c j)) fun j hj => by rw [hz j hj, zero_smul]

private theorem exists_frame_cell (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : Fin (N + 1))
    (w : ι → Equiv.Perm (Fin N)) :
    ∃ e : Fin l → Γ(F ι N τ l, cellOpen ι N w), VB.IsFrame e ∧
      ∀ j, (sub ι N τ l).incl.app _ (e j) = cellCol ι N w τ (Fin.castLE l.is_le j) :=
  exists_isFrame_sub (sub ι N τ l) _ (isFrame_cellCol ι N w τ) l l.is_le (mem_sub_iff_cellCol ι N τ l w)

set_option backward.isDefEq.respectTransparency false in

private theorem pull_comb {T Y Z : Scheme.{0}} (x : T ⟶ Y) (q : Y ⟶ Z) (E : Z.Modules) {F : Y.Modules}
    (i : F ⟶ (Scheme.Modules.pullback q).obj E) {μ : Type} [Fintype μ] (e : μ → Γ(E, ⊤)) {U : Y.Opens}
    (s : Γ(F, U)) (a : μ → Γ(Y, U)) (h₁ : U ≤ q ⁻¹ᵁ ⊤) (h₂ : x ⁻¹ᵁ U ≤ (x ≫ q) ⁻¹ᵁ ⊤)
    (hs : i.app U s = ∑ m, a m • pullbackSections q E h₁ (e m)) :
    ((Scheme.Modules.pullback x).map i ≫ (Scheme.Modules.pullbackComp x q).hom.app E).app (x ⁻¹ᵁ U)
        (pullbackSections x F le_rfl s) =
      ∑ m, x.appLE U (x ⁻¹ᵁ U) le_rfl (a m) • pullbackSections (x ≫ q) E h₂ (e m) := by
  have h3 := QCoh.pullback_map_app_pullbackSections x i (le_refl (x ⁻¹ᵁ U)) s
  refine (congrArg (((Scheme.Modules.pullbackComp x q).hom.app E).app _) h3).trans ?_
  rw [hs, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [QCoh.pullbackSections_smul, Scheme.Modules.Hom.app_smul,
    ← Vert.DivPull.pullbackComp_inv_app x q E h₁ le_rfl h₂]
  congr 1
  exact congr(($((Scheme.Modules.pullbackComp x q).inv_hom_id_app E)).app _ _)

set_option backward.isDefEq.respectTransparency false in

private theorem pull_incl_cellCol (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : Fin (N + 1))
    (w : ι → Equiv.Perm (Fin N)) {T : Scheme.{0}} (x : T ⟶ Fl ι N) (s : Γ(F ι N τ l, cellOpen ι N w)) (k : Fin N)
    (hs : (sub ι N τ l).incl.app _ s = cellCol ι N w τ k) :
    ((Scheme.Modules.pullback x).map (incl ι N τ l) ≫
        (Scheme.Modules.pullbackComp x (flStr ι N)).hom.app (GlobalTheory.FlagZ.Taut.stdE N)).app (x ⁻¹ᵁ cellOpen ι N w)
        (QCoh.pullbackSections x (F ι N τ l) le_rfl s) =
      ∑ i, x.appLE (cellOpen ι N w) (x ⁻¹ᵁ cellOpen ι N w) le_rfl
          (cellRing ι N w ((cellGL Prod.fst Prod.snd w τ).1 i k)) •
        resM _ le_top (QCoh.pullbackSections (x ≫ flStr ι N) (GlobalTheory.FlagZ.Taut.stdE N) (by simp)
          (VB.freeFrame (Sp ℤ) (Fin N) i)) := by
  refine (pull_comb x (flStr ι N) (GlobalTheory.FlagZ.Taut.stdE N) (incl ι N τ l) (VB.freeFrame (Sp ℤ) (Fin N)) s
    (fun i => cellRing ι N w ((cellGL Prod.fst Prod.snd w τ).1 i k)) le_top le_top ?_).trans
    (Finset.sum_congr rfl fun i _ => congrArg _ (QCoh.res_pullbackSections _ _ _ _ _).symm)
  refine (congrArg ((freeIso ι N).inv.app _) hs).trans ?_
  rw [cellCol, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, app_resM]
  congr 1
  have h1 : (freeIso ι N).hom.app ⊤ _ = _ := IsFrame.iso_hom_app
    ((VB.isFrame_freeFrame (Sp ℤ) (Fin N)).pullback (flStr ι N)) (VB.isFrame_freeFrame _ (Fin N)) i
  rw [← h1]
  refine Eq.trans (congrArg _ ?_) (QCoh.res_pullbackSections (flStr ι N) _ (U := ⊤) le_top _ _)
  exact congr(($((freeIso ι N).hom_inv_id)).app ⊤ _)

private theorem spMap_cellRing_cell (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N))
    (hU : IsAffineOpen (cellOpen ι N w)) :
    spMap (cellRing ι N w) ≫ cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w = hU.fromSpec := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w) hU
    (isAffineOpen_top _) (Scheme.Hom.preimage_image_eq _ ⊤).ge
  have e₀ : ((cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appIso ⊤).hom =
      (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appLE (cellOpen ι N w) ⊤
        (Scheme.Hom.preimage_image_eq _ ⊤).ge :=
    Scheme.Hom.appIso_hom' _ _
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← e₀] at h
  have e : spMap (cellRing ι N w) = Spec.map ((cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appIso ⊤).inv ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of (CellRing (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd))).inv := by
    exact Spec.map_comp _ _
  rw [e]
  erw [Category.assoc, ← h]
  erw [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]

private theorem spMap_res (A : Type) [CommRing A] (W : (Sp A).Opens) (hW : IsAffineOpen W) :
    spMap ((resG (Sp A) (le_top : W ≤ ⊤)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) = hW.fromSpec := by
  have h := IsAffineOpen.map_fromSpec (isAffineOpen_top (Sp A)) hW (homOfLE le_top).op
  rw [IsAffineOpen.fromSpec_top] at h
  erw [Scheme.isoSpec_Spec_inv] at h
  rw [← h]
  exact Spec.map_comp _ _

private theorem exists_upper_cell (ι : Type) [Fintype ι] (N : ℕ) (A : Type) [CommRing A] (g : ι → GL (Fin N) A) (a : ι)
    (w : ι → Equiv.Perm (Fin N)) (y : Sp A)
    (hy : y ∈ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ⁻¹ᵁ cellOpen ι N w) :
    ∃ (W : (Sp A).Opens) (hW : W ≤ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ⁻¹ᵁ cellOpen ι N w)
      (B : Matrix (Fin N) (Fin N) Γ(Sp A, W)), y ∈ W ∧ (∀ i j : Fin N, j < i → B i j = 0) ∧ IsUnit B.det ∧
      ∀ i j, resG (Sp A) (le_top : W ≤ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((g a).1 i j)) =
        ∑ k, resG (Sp A) hW ((flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g).appLE (cellOpen ι N w)
          (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ⁻¹ᵁ cellOpen ι N w) le_rfl
          (cellRing ι N w ((cellGL Prod.fst Prod.snd w a).1 i k))) * B k j := by
  have hU : IsAffineOpen (cellOpen ι N w) :=
    (isAffineOpen_top (Sp (CellRing (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd))).image_of_isOpenImmersion _
  obtain ⟨W, hWa, hyW, hW⟩ := exists_isAffineOpen_mem_and_subset hy
  have hW : W ≤ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ⁻¹ᵁ cellOpen ι N w := hW
  set x := flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g with hx
  let ψ : A →+* Γ(Sp A, W) := (resG (Sp A) (le_top : W ≤ ⊤)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let φ : CellRing (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd →+* Γ(Sp A, W) :=
    (x.appLE _ W hW).hom.comp (cellRing ι N w)
  have key : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd
      (fun τ => Matrix.GeneralLinearGroup.map φ (cellGL Prod.fst Prod.snd w τ)) =
      flagPt Prod.fst Prod.snd (fun τ => Matrix.GeneralLinearGroup.map ψ (g τ)) := by
    rw [← spMap_flagPt, ← spMap_flagPt, ← hx, ← cell, spMap_res A W hWa,
      ← IsAffineOpen.SpecMap_appLE_fromSpec x hU hWa hW, ← spMap_cellRing_cell ι N w hU]
    rw [spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rfl
  have hB := (flagPt_eq_iff_below _ _ _ _ _ _ _ _).1 key a
  refine ⟨W, hW, ((Matrix.GeneralLinearGroup.map φ (cellGL Prod.fst Prod.snd w a))⁻¹ *
    Matrix.GeneralLinearGroup.map ψ (g a)).1, hyW, fun i j h => hB i j ⟨(a, i.castSucc), rfl, h, le_rfl⟩,
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _), fun i j => ?_⟩
  have e := congrArg (fun m : GL (Fin N) Γ(Sp A, W) => m.1 i j) (mul_inv_cancel_left
    (Matrix.GeneralLinearGroup.map φ (cellGL Prod.fst Prod.snd w a)) (Matrix.GeneralLinearGroup.map ψ (g a)))
  refine e.symm.trans ?_
  rw [Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact congrArg (· * _) (LB.resG_appLE x le_rfl hW _).symm

private theorem isUnit_det_castLE {R : Type} [CommRing R] {N : ℕ} (B : Matrix (Fin N) (Fin N) R)
    (hB : ∀ i j : Fin N, j < i → B i j = 0) (hdet : IsUnit B.det) (l : ℕ) (hl : l ≤ N) :
    IsUnit (B.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have ht : B.BlockTriangular id := fun i j h => hB i j h
  have ht' : (B.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular id := fun i j h => hB _ _ h
  rw [Matrix.det_of_upperTriangular ht] at hdet
  rw [Matrix.det_of_upperTriangular ht']
  exact IsUnit.prod_univ_iff.2 fun i => IsUnit.prod_univ_iff.1 hdet (Fin.castLE hl i)

end GlobalTheory.FlagZ.TautPull

open GlobalTheory.VB GlobalTheory.FlagZ.TautPull in
theorem _root_.GlobalTheory.T.pullback_flag_sections_frame : ∀ (ι : Type) [Fintype ι] (N : ℕ) (A : Type) [CommRing A] (g : ι → GL (Fin N) A) (a : ι) (l : Fin (N + 1)),
    ∃ s : Fin l → Γ((Scheme.Modules.pullback (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g)).obj (F ι N a l), ⊤),
      VB.IsFrame s ∧ ∀ j, ((Scheme.Modules.pullback (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g)).map (incl ι N a l) ≫
        (Scheme.Modules.pullbackComp (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) (flStr ι N)).hom.app
          (GlobalTheory.FlagZ.Taut.stdE N)).app ⊤ (s j) =
        GlobalTheory.FlagZ.Taut.colSec (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ≫ flStr ι N) (g a).1 (Fin.castLE l.is_le j) := by
  intro ι _ N A _ g a l
  haveI : (F ι N a l).IsQuasicoherent := (GlobalTheory.T.tautological_subbundle_rank ι N a l).1.isQuasicoherent
  refine glue_frame _ _ (fun V => ?_) (fun y => ?_)
  · exact ((isFrame_iff.1 (isFrame_colSec N A _ (g a)) V le_top).1).comp _ (Fin.castLE_injective _)
  · obtain ⟨w, hw⟩ := GlobalTheory.FlagZ.exists_mem_range_cell ι (ι × Fin (N + 1)) N Prod.fst Prod.snd
      (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g y)
    have hy : y ∈ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ⁻¹ᵁ cellOpen ι N w := (mem_cellOpen ι N).2 hw
    obtain ⟨W, hW, B, hyW, hBt, hBd, hB⟩ := exists_upper_cell ι N A g a w y hy
    obtain ⟨e, he, hinc⟩ := exists_frame_cell ι N a l w
    have ht0 := he.pullback (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g)
    refine ⟨W, fun j => ∑ k, B.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le) k j • resM _ hW
      (QCoh.pullbackSections (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) (F ι N a l) le_rfl (e k)), hyW,
      isFrame_sum_smul_of_isUnit (ht0.res hW) _
        ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_castLE B hBt hBd l l.is_le)), fun j => ?_⟩
    set q : Fin N → Γ((Scheme.Modules.pullback ((flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) ≫ flStr ι N)).obj (GlobalTheory.FlagZ.Taut.stdE N), ⊤) := fun i =>
      QCoh.pullbackSections ((flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) ≫ flStr ι N) (GlobalTheory.FlagZ.Taut.stdE N) (by simp) (VB.freeFrame (Sp ℤ) (Fin N) i) with hq
    have h1 : ∀ k : Fin l, ((Scheme.Modules.pullback (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g)).map (incl ι N a l) ≫
        (Scheme.Modules.pullbackComp (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) (flStr ι N)).hom.app (GlobalTheory.FlagZ.Taut.stdE N)).app W
          (resM _ hW (QCoh.pullbackSections (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) (F ι N a l) le_rfl (e k))) =
        ∑ i, resG (Sp A) hW ((flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g).appLE (cellOpen ι N w) ((flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) ⁻¹ᵁ cellOpen ι N w) le_rfl
          (cellRing ι N w ((cellGL Prod.fst Prod.snd w a).1 i (Fin.castLE l.is_le k)))) •
            resM _ (le_top : W ≤ ⊤) (q i) := by
      intro k
      rw [GlobalTheory.Twist.app_resM, pull_incl_cellCol ι N a l w (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) (e k) _ (hinc k), map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [GlobalTheory.Twist.resM_smul, GlobalTheory.Twist.resM_resM]
    have h2 : resM _ (le_top : W ≤ ⊤) (GlobalTheory.FlagZ.Taut.colSec ((flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) ≫ flStr ι N) (g a).1 (Fin.castLE l.is_le j)) =
        ∑ i, resG (Sp A) (le_top : W ≤ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((g a).1 i (Fin.castLE l.is_le j))) •
          resM _ (le_top : W ≤ ⊤) (q i) := by
      rw [GlobalTheory.FlagZ.Taut.colSec, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [GlobalTheory.Twist.resM_smul]
    rw [h2, map_sum]
    simp_rw [Scheme.Modules.Hom.app_smul, h1, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul, hB]
    congr 1
    refine Fintype.sum_of_injective (Fin.castLE l.is_le) (Fin.castLE_injective _) _ _ (fun k hk => ?_) fun k => mul_comm _ _
    have hk' : (l : ℕ) ≤ (k : ℕ) := not_lt.1 fun h => hk ⟨⟨k, h⟩, rfl⟩
    rw [hBt k _ (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le j.2 hk')), mul_zero]
end
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)

noncomputable section

namespace GlobalTheory.FlagZ.Univ

def univFlag (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) :
    Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (GlobalTheory.FlagZ.Taut.stdE N)) N where
  F := F ι N τ
  ι := incl ι N τ
  isSubbundle i := (GlobalTheory.T.tautological_subbundle_rank ι N τ i).2
  isVB i := (GlobalTheory.T.tautological_subbundle_rank ι N τ i).1
  step := step ι N τ
  step_ι := step_incl ι N τ
  isIso_last := GlobalTheory.T.isIso_incl_last' ι N τ

theorem isTaut_univFlag (ι : Type) [Fintype ι] (N : ℕ) : GlobalTheory.FlagZ.Taut.IsTaut ι N (univFlag ι N) :=
  fun A _ g a l => GlobalTheory.T.pullback_flag_sections_frame ι N A g a l

theorem exists_lifts (ι : Type) [Fintype ι] (N : ℕ) (T : Scheme.{0}) (g : T ⟶ Sp ℤ)
    (fl' : ι → Vert.Flag ((Scheme.Modules.pullback g).obj (freeModule (Sp ℤ) (Fin N))) N) : ∃ g', Lifts g fl' g' := by
  obtain ⟨g', w, h⟩ := GlobalTheory.T.tautological_flag_universal ι N (univFlag ι N) (isTaut_univFlag ι N) T g fl'
  exact ⟨g', w, h⟩

end GlobalTheory.FlagZ.Univ
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_variety_lift_exists : ∀ (ι : Type) [Fintype ι] (N : ℕ) (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (fl' : ι → Vert.Flag ((Scheme.Modules.pullback g).obj (freeModule (Sp ℤ) (Fin N))) N), ∃ g', Lifts g fl' g' := by
  atlas_forward_decl GlobalTheory.FlagZ.Univ.exists_lifts
end
