import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapCompCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTransfer
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqOfSecConst
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickening
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.SettingConsistentExample

theorem exists_even_one {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] (P : CP G)
    (i : H ⟶ G) (hi : i = 1) : ∃ σ : CubTriv P.c i, σ.Even := by
  subst hi
  obtain ⟨t, ht, hv⟩ := exists_gen P.L.isLB (φ := (PEmpty.elim : PEmpty → (H.left ⟶ G.left))) (ε := PEmpty.elim)
    (K' := Fin 2) (φ' := ![(1 : H ⟶ G).left, (1 : H ⟶ G).left]) (ε' := ![1, -1])
    (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen P.L.L) (LB.isGen_oneGen _)
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ H.left) (z : Z) (J), Good P.L.L z J → val t r z J = 1 :=
    fun Z r z J hJ => (hv Z r z J hJ).trans (val_one _)
  refine ⟨⟨t, ht, fun T x y u z J hJ => ?_⟩, fun T x z J hJ => ?_⟩
  · simp only [v _ _ z J hJ, MonObj.comp_one, (isCub_cubV P.c hJ).face, _root_.mul_one]
  · show val t _ z J = _ * val t _ z J
    rw [v _ _ z J hJ, v _ _ z J hJ, MonObj.comp_one, P.val_sym_one hJ, _root_.mul_one]

section Generic
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']

theorem isCPPullback_cancel {P : CP G} {P' : CP G'} {P'' : CP G''} {f : S' ⟶ S} {g : S'' ⟶ S'} {f₀ : S'' ⟶ S}
    {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left} {F₀ : G''.left ⟶ G.left} (h : IsCPPullback P' P f F)
    (n : IsCPPullback P'' P f₀ F₀) (e₁ : g ≫ f = f₀) (e₂ : F' ≫ F = F₀) (w : F' ≫ G'.hom = G''.hom ≫ g) :
    IsCPPullback P'' P' g F' := by
  subst e₁ e₂
  obtain ⟨h, v, hv⟩ := h
  obtain ⟨n, u, hu⟩ := n
  have hg := h.cancel n w
  obtain ⟨w', h', -⟩ := (isCPMap_comp_cancel _ _ _ f g G G' G'' P P' P'' F _ v F' w n.1.w hv).2
    (fun T x y => Over.OverMorphism.ext (hg.2 T x y _ _ rfl rfl).symm) u hu
  exact ⟨hg, w', h'⟩

variable (hG : IsAbelianScheme G) (hG' : IsAbelianScheme G') (X : Type) [AddCommGroup X] [Subsingleton X]

omit [IsCommMonObj G] [IsCommMonObj G'] in

def abMap (F : G'.left ⟶ G.left) : (TQ.abelian G' hG' X).B.left ⟶ (TQ.abelian G hG X).B.left := F

omit [IsCommMonObj G'] in

def abMap' {Y : Scheme.{0}} (F : G'.left ⟶ Y) : (TQ.abelian G' hG' X).B.left ⟶ Y := F

omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem abMap_q (F : G'.left ⟶ G.left) :
    (TQ.abelian G' hG' X).q.left ≫ abMap hG hG' X F = F ≫ (TQ.abelian G hG X).q.left :=
  (Category.id_comp _).trans (Category.comp_id _).symm

omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem abMap_comp {Y : Scheme.{0}} {F : G'.left ⟶ G.left} {F₁ : G.left ⟶ Y} {F₀ : G'.left ⟶ Y} (h : F ≫ F₁ = F₀) :
    abMap hG hG' X F ≫ abMap' hG X F₁ = abMap' hG' X F₀ := h

theorem abMap_pb {P : CP G} {P' : CP G'} {f : S' ⟶ S} {F : G'.left ⟶ G.left} (h : IsCPPullback P' P f F) :
    IsCPPullback (TQ.Desc.abelian (X := X) hG' P').M (TQ.Desc.abelian (X := X) hG P).M f (abMap hG hG' X F) := h

theorem abMap'_pb {P : CP G} {P' : CP G'} {f : S' ⟶ S} {F : G'.left ⟶ G.left} (h : IsCPPullback P' P f F) :
    IsCPPullback (TQ.Desc.abelian (X := X) hG' P').M P f (abMap' hG' X F) := h

omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem ab_tor {f : S' ⟶ S} {F : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f F) :
    TorusCompat f F (TQ.abelian G' hG' X).i (TQ.abelian G hG X).i := by
  obtain ⟨i', hi', -⟩ := existsUnique_torusCompat hg.1 (TQ.abelian G hG X).i
  have := (TQ.abelian G hG X).i_hom
  have := hi'.isMonHom hg
  have : i' = (TQ.abelian G' hG' X).i := by
    have h1 : 𝟙 (splitTorus S' X) = 1 := point_eq_of_subsingleton _ _
    rw [← Category.id_comp i', h1, MonObj.one_comp]
    exact Hom.one_def
  exact this ▸ hi'

omit hG' in
theorem ab_even (P : CP G) : ∃ σ : CubTriv P.c (TQ.abelian G hG X).i, σ.Even :=
  exists_even_one _ _ (Hom.one_def).symm

end Generic

section Thick
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]

omit [IsDomain R] [GrpObj G] in
theorem thickMap_fst : thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

omit [IsDomain R] [GrpObj G] in
theorem thickMap_snd : thickMap R I e G ≫ (thickObj R I (e + 1) G).hom = (thickObj R I e G).hom ≫ thickTrans R I e :=
  pullback.lift_snd _ _ _

omit [IsDomain R] in

theorem isGrpPullback_thickMap :
    IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (thickTrans_comp R I e).symm (thickMap_fst I e G).symm)
    (thickMap_snd I e G)

theorem isCPPullback_level [IsCommMonObj G] {P : CP G} {P₀ : CP (thickObj R I e G)} (h₀ : IsLevelCP I e P₀ P) :
    IsCPPullback P₀ P (thick R I e) (pullback.fst G.hom (thick R I e)) :=
  ⟨isGrpPullback_pullback G _, h₀⟩

theorem isCPPullback_levels [IsCommMonObj G] {P : CP G} {P₀ : CP (thickObj R I e G)} {P₁ : CP (thickObj R I (e + 1) G)}
    (h₀ : IsLevelCP I e P₀ P) (h₁ : IsLevelCP I (e + 1) P₁ P) :
    IsCPPullback P₀ P₁ (thickTrans R I e) (thickMap R I e G) :=
  isCPPullback_cancel (isCPPullback_level I (e + 1) G h₁) (isCPPullback_level I e G h₀) (thickTrans_comp R I e)
    (thickMap_fst I e G) (thickMap_snd I e G)


end Thick

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

def good (hV : CDVR V) (hG : IsAbelianScheme G) (gen : (Over.pullback (jK V)).obj G ≅ A.A) (hgen : IsMonHom gen.hom)
    (P : CP G) (w : LB.Iso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK V)))) (hw : w.IsGen) :
    HidaSetting V A G where
  cdvr := hV
  semi := isSemiAbelian_of_isAbelianScheme G hG
  gen := gen
  gen_hom := hgen
  P := P
  wA := w
  wA_gen := hw
  X := PUnit
  Q₀ := TQ.abelian _ (isAbelianScheme_pullback_obj _ G hG) PUnit
  P₀ := (exists_isLevelCP _ 0 P).choose
  lev₀ := (exists_isLevelCP _ 0 P).choose_spec
  even₀ := ab_even _ _ _

def goodLev (s : HidaSetting V A G) (hG : IsAbelianScheme G) [Subsingleton s.X] (e : ℕ) :
    Lev (IsLocalRing.maximalIdeal V) s.P s.X e where
  Q := TQ.abelian _ (isAbelianScheme_pullback_obj _ G hG) s.X
  Pe := (exists_isLevelCP _ e s.P).choose
  lev := (exists_isLevelCP _ e s.P).choose_spec
  D := TQ.Desc.abelian _ _

def goodTower (s : HidaSetting V A G) (hG : IsAbelianScheme G) [Subsingleton s.X] : Tower s where
  l := goodLev s hG
  tor e := ab_tor (isAbelianScheme_pullback_obj _ G hG) (isAbelianScheme_pullback_obj _ G hG) s.X
    (isGrpPullback_thickMap (IsLocalRing.maximalIdeal V) e G)
  β e := abMap (isAbelianScheme_pullback_obj _ G hG) (isAbelianScheme_pullback_obj _ G hG) s.X (thickMap V _ e G)
  β_pb e := abMap_pb _ _ s.X (isCPPullback_levels _ e G (goodLev s hG e).lev (goodLev s hG (e + 1)).lev)
  β_q e := abMap_q _ _ s.X _

def goodAlg (s : HidaSetting V A G) (hG : IsAbelianScheme G) [Subsingleton s.X] (ha : RelAmple G s.P.L.L) :
    (goodTower s hG).Alg where
  B := G
  isAb := hG
  M := s.P
  ample := ha
  b e := abMap' (isAbelianScheme_pullback_obj _ G hG) s.X (pullback.fst G.hom (thick V _ e))
  b_pb e := abMap'_pb _ s.X (isCPPullback_level _ e G (goodLev s hG e).lev)
  b_β e := abMap_comp _ _ s.X (thickMap_fst _ e G)








def curveTwoAdic : WeierstrassCurve ℤ_[2] := ⟨0, 0, 1, 0, 0⟩

instance isElliptic_curveTwoAdic : curveTwoAdic.IsElliptic := ⟨by
  have h : curveTwoAdic.Δ = -(3 : ℤ_[2]) ^ 3 := by
    simp only [curveTwoAdic, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    ring
  have h3 : IsUnit (3 : ℤ_[2]) := by
    have : ‖((3 : ℕ) : ℤ_[2])‖ = 1 := PadicInt.norm_natCast_eq_one_iff.2 (by norm_num)
    exact PadicInt.isUnit_iff.2 (by simpa using this)
  rw [h]
  exact (h3.pow 3).neg⟩


end GlobalTheory.UU.SettingConsistentExample
end
