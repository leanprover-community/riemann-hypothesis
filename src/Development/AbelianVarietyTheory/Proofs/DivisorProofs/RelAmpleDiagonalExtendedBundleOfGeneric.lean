import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmplePowerOfExtensionGenericFibreAbelianMode
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusEqPreimageModuliAndPrincipal

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ModelAmpleExt

theorem pw_pw' {X : Scheme.{0}} (H : LB X) (a b : ℤ) :
    GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw H a) b = GlobalTheory.AbLaw.pw H (a * b) :=
  congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X)) (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem relAmple_of_generic : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → ∀ M : LB G.left, M.IsLB → Out.RelAmple A (M.pull φ) → Out.RelAmple G M := by
  intro W L _ _ _ _ _ _ G _ A _ φ hG hφ M hM hA
  have hAab : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hφ
  obtain ⟨d, hd, hex⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy L A (M.pull φ) (pull_isLB hM φ)).1 hA

  rw [← GlobalTheory.TrivLocus.pull_pw M φ (d : ℤ)] at hex
  obtain ⟨m, s, hs⟩ := hex
  set f := spMap (algebraMap W L) with hf
  set g := spMap (algebraMap L L) with hg
  have hg1 : g = 𝟙 _ := by
    simp [hg, spMap]
  haveI : IsIso g := by rw [hg1]; infer_instance
  have h1 : inv (pullback.fst A.hom g) ≫ pullback.snd A.hom g = A.hom := by
    rw [IsIso.inv_comp_eq, pullback.condition, hg1, Category.comp_id]
  let i : pullback G.hom f ≅ pullback A.hom g :=
    hφ.1.isoPullback.symm ≪≫ (asIso (pullback.fst A.hom g)).symm
  have hi : i.hom ≫ pullback.snd A.hom g = pullback.snd G.hom f := by
    simp only [i, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, h1]
    exact hφ.1.isoPullback_inv_snd
  let e : (Over.pullback f).obj G ≅ (Over.pullback g).obj A := Over.isoMk i hi
  have he : e.hom.left ≫ pullback.fst A.hom g = hφ.1.isoPullback.inv := by
    simp [e, i]
  have hMd := GlobalTheory.AbLaw.isLB_pw hM (d : ℤ)
  obtain ⟨w, hw⟩ : LBIso ((GlobalTheory.AbLaw.pw M (d : ℤ)).pull (pullback.fst G.hom f))
      (((GlobalTheory.AbLaw.pw M (d : ℤ)).pull φ).pull (e.hom.left ≫ pullback.fst A.hom g)) :=
    LBIso.chartPull
      (chartPullSame (GlobalTheory.AbLaw.pw M (d : ℤ)) (fun _ : PUnit => pullback.fst G.hom f) (fun _ => φ) (fun _ => 1)
        (e.hom.left ≫ pullback.fst A.hom g) fun _ => by rw [he]; exact hφ.1.isoPullback_inv_fst.symm)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) ⟨_, Geo.Tor.idIso_isGen (pull_isLB hMd φ)⟩
  obtain ⟨n, hn, hex2⟩ := GlobalTheory.ModelAmple.veryAmpleBy_pw_of_generic L W L A hAab G hG e
    ((GlobalTheory.AbLaw.pw M (d : ℤ)).pull φ) m s (GlobalTheory.AbLaw.pw M (d : ℤ)) w (pull_isLB hMd φ) hs hMd hw
  rw [pw_pw', show (d : ℤ) * (n : ℤ) = ((d * n : ℕ) : ℤ) by push_cast; rfl] at hex2
  exact (GlobalTheory.Unif.relAmple_iff_veryAmpleBy W G M hM).2 ⟨d * n, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero
    (Nat.one_le_iff_ne_zero.1 hd) (Nat.one_le_iff_ne_zero.1 hn)), hex2⟩

end GlobalTheory.ModelAmpleExt
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DiagAmpleExt

theorem diag_comm {S S' : Scheme.{0}} {G : Over S} {A : Over S'} (φ : A.left ⟶ G.left)
    (φ₂ : (G2 A).left ⟶ (G2 G).left) (h : IsSquare φ φ₂) :
    φ ≫ (lift (𝟙 G) (𝟙 G)).left = (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ := by
  apply pullback.hom_ext
  · change φ ≫ (lift (𝟙 G) (𝟙 G)).left ≫ (fst G G).left = (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ ≫ (fst G G).left
    rw [h.1, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id, ← Category.assoc,
      ← Over.comp_left, lift_fst, Over.id_left, Category.id_comp]
  · change φ ≫ (lift (𝟙 G) (𝟙 G)).left ≫ (snd G G).left = (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ ≫ (snd G G).left
    rw [h.2, ← Over.comp_left, lift_snd, Over.id_left, Category.comp_id, ← Category.assoc,
      ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp]

theorem relAmple_diag_of_generic : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ (P : LB (G2 A).left) (P' : LB (G2 G).left), P.IsLB → P'.IsLB → LBIso P (P'.pull φ₂) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → Out.RelAmple G (P'.pull (lift (𝟙 G) (𝟙 G)).left) := by
  intro W L _ _ _ _ _ _ G _ A _ φ φ₂ hG hφ hsq P P' hP hP' e hA
  have hAab : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hφ
  have := hAab.proper
  set dG := (lift (𝟙 G) (𝟙 G)).left
  set dA := (lift (𝟙 A) (𝟙 A)).left
  have hM : (P'.pull dG).IsLB := pull_isLB hP' _
  refine GlobalTheory.ModelAmpleExt.relAmple_of_generic W L G A φ hG hφ (P'.pull dG) hM ?_
  have i1 : LBIso ((P'.pull dG).pull φ) (P'.pull (φ ≫ dG)) :=
    GlobalTheory.OriginCohom.lbIso_pull_pull_comp hP' dG φ
  have i2 : LBIso (P'.pull (dA ≫ φ₂)) ((P'.pull φ₂).pull dA) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP' dA rfl
  have i3 : LBIso ((P'.pull φ₂).pull dA) (P.pull dA) :=
    GlobalTheory.GenSpread.lbIso_pullback e.symm dA
  rw [diag_comm φ φ₂ hsq] at i1
  have hφ2 := pull_isLB hP' φ₂
  have j : LBIso (P.pull dA) ((P'.pull dG).pull φ) :=
    (LBIso.trans (pull_isLB hM φ) (pull_isLB hP' _) (pull_isLB hP dA) i1 (LBIso.trans (pull_isLB hP' _)
      (pull_isLB hφ2 dA) (pull_isLB hP dA) i2 i3)).symm
  have hsq' : IsPullback (𝟙 A.left) A.hom A.hom (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull hsq' (pull_isLB hP dA) (pull_isLB hM φ)
    (LBIso.trans (pull_isLB hM φ) (pull_isLB hP dA) (pull_isLB (pull_isLB hP dA) _) j.symm
      (GlobalTheory.GenSpread.lbIso_pull_pull hP (𝟙 _) (a := dA) (Category.id_comp _).symm)) hA

end GlobalTheory.DiagAmpleExt
end
end
