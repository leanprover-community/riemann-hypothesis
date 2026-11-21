import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleTrivialOnAxesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidLineBundleIsoDescentAlongGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalExtendedBundleOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionDescendsGaloisCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionDescendsFiniteEtaleGaloisCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompDiagonalBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudePrimeToPPullbackSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticSimilitudeActionOnLevelFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelOverCyclotomicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSymplecticSimilitudeClassifyingMapsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliMapDescendsGaloisCoverStatement

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ZM.IsGaloisCover

theorem eq_of_local_eq_pullback : ∀ (X Y S Z : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (g : S ⟶ Y) (h₁ h₂ : S ⟶ Z), GlobalTheory.ZM.IsGaloisCover Ga ρ π → (∀ q : ↥(pullback g π), ∃ V : (pullback g π).Opens, q ∈ V ∧ V.ι ≫ pullback.fst g π ≫ h₁ = V.ι ≫ pullback.fst g π ≫ h₂) → h₁ = h₂ := by
  intro X Y S Z π Ga _ ρ g h₁ h₂ h hloc
  have hp : IsPullback (pullback.snd g π) (pullback.fst g π) π g := (IsPullback.of_hasPullback g π).flip
  have : Etale (pullback.fst g π) := MorphismProperty.of_isPullback (P := @Etale) hp h.etale
  have : IsFinite (pullback.fst g π) := MorphismProperty.of_isPullback (P := @IsFinite) hp h.fin
  have : Surjective (pullback.fst g π) := MorphismProperty.of_isPullback (P := @Surjective) hp h.onto
  have e : pullback.fst g π ≫ h₁ = pullback.fst g π ≫ h₂ :=
    Scheme.hom_ext_of_forall _ _ fun q ↦ hloc q
  exact (cancel_epi (pullback.fst g π)).1 e

end GlobalTheory.ZM.IsGaloisCover
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.GaloisActDesc

theorem exists_oActN_descend : ∀ (O : Type) [Ring O] (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (act : OActN O A), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → GlobalTheory.ZM.IsGaloisCover Ga ν φ → (∀ a, IsGrpPullback A A (ρ a) (ν a)) → (∀ a c, (act.act c).left ≫ ν a = ν a ≫ (act.act c).left) → ∃ act₀ : OActN O A₀, ∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left := by
  intro O _ X Y π Ga _ ρ A _ _ A₀ _ _ φ ν act hπ _ _ hp hφ _ hcomm
  have : Flat π := by have := hπ.etale; infer_instance
  have : Surjective π := hπ.onto
  have eφ : Epi φ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hφ
  have hi : ∀ c, ∃ f : A₀ ⟶ A₀, (act.act c).left ≫ φ = φ ≫ f.left := by
    intro c
    obtain ⟨g, hg, -⟩ := hφ.existsUnique_desc ((act.act c).left ≫ φ) (fun a ↦ by
      rw [← Category.assoc, ← hcomm, Category.assoc, hφ.inv])
    have hw : g ≫ A₀.hom = A₀.hom := by
      rw [← cancel_epi φ, reassoc_of% hg, hp.1.w, Over.w_assoc]
    exact ⟨Over.homMk g hw, hg.symm⟩
  choose f hf using hi
  refine ⟨⟨f, fun x ↦ ?_, ?_, fun x y ↦ ?_, fun x y ↦ ?_⟩, hf⟩
  · have := act.hom x
    exact GlobalTheory.ActDescent.isMonHom_descend hp hp (act.act x) (f x) (hf x)
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    rw [← hf, act.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    rw [← hf, act.mul, Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    let φ₀ : Over.mk (A.hom ≫ π) ⟶ A₀ := Over.homMk φ hp.1.w
    have h := hp.2 A (act.act x) (act.act y) (φ₀ ≫ f x) (φ₀ ≫ f y) (hf x).symm (hf y).symm
    rw [← MonObj.comp_mul] at h
    rw [← hf, act.add, ← h]
    rfl

end GlobalTheory.GaloisActDesc
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LevelSecDesc

theorem levelSections_descend : ∀ (O : Type) [Ring O] (La : Type) [AddCommGroup La] [Module O La] (N : ℕ) (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (act : OActN O A) (act₀ : OActN O A₀) (eta : La → (𝟙_ (Over X) ⟶ A)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsGrpPullback A A₀ π φ → GlobalTheory.ZM.IsGaloisCover Ga ν φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ a y, (eta y).left ≫ ν a = ρ a ≫ (eta y).left) → (∀ x y, eta (x + y) = eta x * eta y) → (∀ (c : O) x, eta (c • x) = eta x ≫ act.act c) → (∀ x, eta (N • x) = 1) → ∃ eta₀ : La → (𝟙_ (Over Y) ⟶ A₀), (∀ x y, eta₀ (x + y) = eta₀ x * eta₀ y) ∧ (∀ (c : O) x, eta₀ (c • x) = eta₀ x ≫ act₀.act c) ∧ (∀ x, eta₀ (N • x) = 1) ∧ ∀ y, (eta y).left ≫ φ = π ≫ (eta₀ y).left := by
  intro O _ La _ _ N X Y π Ga _ ρ A _ _ A₀ _ _ φ ν act act₀ eta hπ gp hφ hact heq hadd hlin htor
  have := hπ.etale
  have := hπ.onto
  have : Epi π := Flat.epi_of_flat_of_surjective π
  have desc : ∀ y, ∃ e : 𝟙_ (Over Y) ⟶ A₀, (eta y).left ≫ φ = π ≫ e.left := fun y => by
    obtain ⟨g, hg, -⟩ := (GlobalTheory.ZM.galoisCover_descent X Y π Ga ρ hπ).1 A₀.left ((eta y).left ≫ φ) fun a => by
      rw [← Category.assoc, ← heq a y, Category.assoc, hφ.inv a]
    exact GlobalTheory.ObjDesc.exists_sec gp (eta y) g hg
  choose eta₀ heta using desc
  have hse : ∀ y, GlobalTheory.ObjPull.secPull gp (eta₀ y) = eta y := fun y => GlobalTheory.ObjDesc.secPull_eq gp (heta y)
  refine ⟨eta₀, fun x y => GlobalTheory.ObjDesc.secPull_injective gp (by rw [map_mul, hse, hse, hse, hadd]),
    fun c x => ?_, fun x => GlobalTheory.ObjDesc.secPull_injective gp (by rw [map_one, hse, htor]), heta⟩
  apply Over.OverMorphism.ext
  rw [← cancel_epi π, ← heta, hlin, Over.comp_left, Over.comp_left, Category.assoc, hact c, ← Category.assoc,
    heta, Category.assoc]

end GlobalTheory.LevelSecDesc

end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.DescSymm

open GlobalTheory.CechPic

theorem eSec_swap {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    eSec (A ⊗ A) ≫ (lift (snd A A) (fst A A)).left = eSec (A ⊗ A) := by
  apply GlobalTheory.SquareDescent.square_hom_ext A
  · rw [Category.assoc, ← Over.comp_left, lift_fst, GlobalTheory.SquareDescent.eSec_snd, GlobalTheory.SquareDescent.eSec_fst]
  · rw [Category.assoc, ← Over.comp_left, lift_snd, GlobalTheory.SquareDescent.eSec_fst, GlobalTheory.SquareDescent.eSec_snd]

theorem lbIso_swap : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) := by
  intro X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ hπ hA hA₀ gp hsq hP hP₀ iP ⟨r, hr⟩ iS
  have := hπ.fin
  have := hπ.etale
  have := hπ.onto
  have hA₂₀ : IsAbelianScheme (G2 A₀) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA₀ hA₀
  have hpb := GlobalTheory.SiegelDescent.isPullback_square gp.1 φ₂ hsq
  have hsw : (lift (snd A A) (fst A A)).left ≫ φ₂ = φ₂ ≫ (lift (snd A₀ A₀) (fst A₀ A₀)).left := by
    apply GlobalTheory.SquareDescent.square_hom_ext A₀
    · rw [Category.assoc, hsq.1, Category.assoc, ← Over.comp_left, lift_fst, ← Category.assoc, ← Over.comp_left,
        lift_fst, hsq.2]
    · rw [Category.assoc, hsq.2, Category.assoc, ← Over.comp_left, lift_snd, ← Category.assoc, ← Over.comp_left,
        lift_snd, hsq.1]
  have h₂ := pull_isLB hP₀ (lift (snd A₀ A₀) (fst A₀ A₀)).left
  have hN := LB.isLB_div h₂ hP₀
  have cN := (CechPic.cls_div h₂ hP₀ hN).trans (by rw [CechPic.cls_pull hP₀ _ h₂])
  have z₀ : CechPic.pull (eSec (G2 A₀)) (CechPic.cls _ hP₀) = 0 :=
    (CechPic.cls_eq_zero_iff (pull_isLB hP₀ _)).2 ⟨r, hr⟩
  have c₁ : CechPic.cls _ hP = CechPic.pull φ₂ (CechPic.cls _ hP₀) :=
    (CechPic.cls_eq_iff hP (pull_isLB hP₀ _)).2 iP
  have c₂ : CechPic.cls _ hP = CechPic.pull (lift (snd A A) (fst A A)).left (CechPic.cls _ hP) :=
    ((CechPic.cls_eq_iff hP (pull_isLB hP _)).2 iS).trans (CechPic.cls_pull hP _ _)
  refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns Y X π (G2 A₀) _ hA₂₀ hN
    inferInstance inferInstance inferInstance ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
    ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
  · rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, eSec_swap, z₀, sub_zero]
  · rw [CechPic.cls_pull hN, cN, ← hpb.isoPullback_inv_fst, CechPic.pull_comp, map_sub, ← CechPic.pull_comp φ₂,
      ← hsw, CechPic.pull_comp, ← c₁, ← c₂, sub_self, map_zero]

end GlobalTheory.DescSymm
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_birigidified_bundle_swap_symmetric : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) := by
  first | exact @GlobalTheory.DescSymm.lbIso_swap | exact GlobalTheory.DescSymm.lbIso_swap | (intros; apply GlobalTheory.DescSymm.lbIso_swap; all_goals assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.DescGal

theorem relAmple_diag_descends : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → Out.RelAmple A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) := by
  intro X Y _ π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ hπ _ hA₀ gp sq hP hP₀ hw hamp
  have hc : (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left :=
    (GlobalTheory.DiagAmpleExt.diag_comm φ φ₂ sq).symm
  have H₁ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P₀.pull φ₂).pull (lift (𝟙 A) (𝟙 A)).left) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull P _ _ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (P₀.pull φ₂) _ _ rfl) hw
  have H₂ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) (P₀.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn P₀ (fun _ : PUnit => φ₂) (fun _ => 1) _) H₁
  have H₃ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) :=
    LBIso.chartPull (chartPullId _)
      (chartPullOut P₀ (fun _ : PUnit => (lift (𝟙 A₀) (𝟙 A₀)).left) (fun _ => 1) φ
        (fun _ => (lift (𝟙 A) (𝟙 A)).left ≫ φ₂) fun _ => hc) H₂
  exact (GlobalTheory.relAmple_kTriv_of_finite_etale_cover Y X π A₀ A φ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left)
    (P.pull (lift (𝟙 A) (𝟙 A)).left) hπ.fin hπ.etale hπ.onto hA₀ (pull_isLB hP₀ _) (pull_isLB hP _) gp H₃).1 hamp

end GlobalTheory.DescGal
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_diagonal_descends_finiteEtaleGalois : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → Out.RelAmple A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) := by
  first | exact @GlobalTheory.DescGal.relAmple_diag_descends | exact GlobalTheory.DescGal.relAmple_diag_descends | (intros; apply GlobalTheory.DescGal.relAmple_diag_descends; all_goals assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DescPolKer

theorem pow_eq_one_of_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (e : ℕ), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ (T : Over X) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over Y) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ e hG hA hA₀ hφ hsq hP hP₀ hw hker T x ⟨t, ht⟩
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact pow_zero x
  let T₁ : Over X := Over.mk (pullback.snd T.hom π)
  let ε : T₁.left ⟶ T.left := pullback.fst T.hom π
  have hε : Epi ε := GlobalTheory.GaloisCartDesc.epi_pullback_fst hG T.hom
  let x₁ : T₁ ⟶ A := Over.homMk (hφ.1.lift (ε ≫ x.left) (pullback.snd T.hom π)
    (by simp [ε, pullback.condition])) (hφ.1.lift_snd _ _ _)
  have hx₁ : x₁.left ≫ φ = ε ≫ x.left := hφ.1.lift_fst _ _ _

  have p₀ : IsPullback (snd A₀ T).left (fst A₀ T).left T.hom A₀.hom :=
    (IsPullback.of_hasPullback A₀.hom T.hom).flip
  have w₀ : ((snd A T₁).left ≫ ε) ≫ T.hom = ((fst A T₁).left ≫ φ) ≫ A₀.hom := by
    have a₁ := Over.w (snd A T₁)
    have a₂ := Over.w (fst A T₁)
    simp only [T₁, Over.mk_hom] at a₁
    rw [Category.assoc, Category.assoc, hφ.1.w, ← Category.assoc (fst A T₁).left, a₂, ← a₁, Category.assoc]
    simp [ε, pullback.condition]
    rfl
  let hm : (A ⊗ T₁).left ⟶ (A₀ ⊗ T).left := p₀.lift _ _ w₀
  have hc : (lift (snd A T₁ ≫ x₁) (fst A T₁)).left ≫ φ₂ = hm ≫ (lift (snd A₀ T ≫ x) (fst A₀ T)).left := by
    have p₂ : IsPullback (snd A₀ A₀).left (fst A₀ A₀).left A₀.hom A₀.hom :=
      (IsPullback.of_hasPullback A₀.hom A₀.hom).flip
    apply p₂.hom_ext
    · rw [Category.assoc, hsq.2, ← Category.assoc, GlobalTheory.TripleDescent.lift_left_snd, Category.assoc,
        GlobalTheory.TripleDescent.lift_left_snd, p₀.lift_snd]
    · rw [Category.assoc, hsq.1, ← Category.assoc, GlobalTheory.TripleDescent.lift_left_fst, Category.assoc,
        GlobalTheory.TripleDescent.lift_left_fst, Over.comp_left, Over.comp_left, Category.assoc, hx₁,
        ← Category.assoc, ← Category.assoc, p₀.lift_fst]
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨t', ht', -⟩ := GlobalTheory.FamFieldPull.exists_genPull w hwg hP₀ hP (K := PUnit)
    (fun _ => (lift (snd A T₁ ≫ x₁) (fst A T₁)).left) (fun _ => (lift (snd A₀ T ≫ x) (fst A₀ T)).left)
    (fun _ => 1) hm (fun _ => hc) t ht
  have h₁ : x₁ ^ e = 1 := hker T₁ x₁ ⟨t', ht'⟩

  let j : Over.mk (T₁.hom ≫ π) ⟶ T := Over.homMk ε (by simp [T₁, ε, pullback.condition])
  have hj : (j ≫ x).left = x₁.left ≫ φ := by simp [j, hx₁]
  have hpow : ∀ n : ℕ, ((j ≫ x) ^ (n + 1)).left = (x₁ ^ (n + 1)).left ≫ φ := by
    intro n
    induction n with
    | zero => simpa using hj
    | succ n ih =>
      rw [pow_succ, pow_succ x₁]
      exact hφ.2 T₁ (x₁ ^ (n + 1)) x₁ _ _ ih hj
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have hy : (j ≫ x) ^ (k + 1) * (j ≫ x) ^ (k + 1) = (j ≫ x) ^ (k + 1) := by
    apply Over.OverMorphism.ext
    rw [← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, hpow, hpow,
      show 2 * k + 1 + 1 = (k + 1) + (k + 1) by ring, pow_add, h₁, _root_.one_mul]
  have hy1 := mul_eq_left.1 hy
  apply Over.OverMorphism.ext
  rw [← cancel_epi ε]
  have e₁ : ε ≫ (x ^ (k + 1)).left = (j ≫ x ^ (k + 1)).left := by rw [Over.comp_left]; rfl
  have e₂ : ε ≫ (1 : T ⟶ A₀).left = (j ≫ (1 : T ⟶ A₀)).left := by rw [Over.comp_left]; rfl
  rw [e₁, e₂, MonObj.comp_pow, hy1, MonObj.comp_one]

end GlobalTheory.DescPolKer
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_polarisation_kernel_killed_same_integer : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (e : ℕ), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ (T : Over X) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over Y) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | (exact @GlobalTheory.DescPolKer.pow_eq_one_of_descent) | (exact GlobalTheory.DescPolKer.pow_eq_one_of_descent) | (intros; apply GlobalTheory.DescPolKer.pow_eq_one_of_descent  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LieDesc

theorem lieMult_descend : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∀ i, LieMult (act₀.toF D) x (β.comp (b.t i)) D.m) := by
  intro p _ D R _ b X Y π sY Ga _ ρ A _ _ A₀ _ _ φ act act₀ hG _ _ hpb hact hX k _ _ x β hx i
  haveI : Surjective π := hG.onto
  haveI : IsFinite π := hG.fin
  obtain ⟨y, rfl⟩ := GlobalTheory.ObjDesc.exists_geomPt_lift π k x
  have hc : ∀ c, ((act.toF D).act c).left ≫ φ = φ ≫ ((act₀.toF D).act c).left := fun c => hact _
  exact (GlobalTheory.LiePull.lieMult_pull _ _ _ A₀ A π φ (act₀.toF D) (act.toF D) hpb hc k y _ D.m).1
    (hX k y β (by rw [← Category.assoc]; exact hx) i)

end GlobalTheory.LieDesc
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_multiplicities_geometric_points_descend : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∀ i, LieMult (act₀.toF D) x (β.comp (b.t i)) D.m) := by
  first | exact @GlobalTheory.LieDesc.lieMult_descend | exact GlobalTheory.LieDesc.lieMult_descend | (intros; apply GlobalTheory.LieDesc.lieMult_descend; all_goals assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.GeomDesc

theorem diag_comp {X Y : Scheme.{0}} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (G2 A).left ⟶ (G2 A₀).left} (sq : IsSquare φ φ₂) :
    (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left := by
  apply pullback.hom_ext
  · have h1 := sq.1
    have e1 : (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A) (𝟙 A))
    have e2 : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (fst A₀ A₀).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A₀) (𝟙 A₀))
    show _ ≫ (fst A₀ A₀).left = _ ≫ (fst A₀ A₀).left
    rw [Category.assoc, h1, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]
  · have h2 := sq.2
    have e1 : (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A) (𝟙 A))
    have e2 : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (snd A₀ A₀).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A₀) (𝟙 A₀))
    show _ ≫ (snd A₀ A₀).left = _ ≫ (snd A₀ A₀).left
    rw [Category.assoc, h2, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]

theorem diag_lbIso {X Y : Scheme.{0}} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (G2 A).left ⟶ (G2 A₀).left} (sq : IsSquare φ φ₂) {P : LB (G2 A).left} {P₀ : LB (G2 A₀).left}
    (hP : P.IsLB) (hP₀ : P₀.IsLB) (pol : LBIso P (P₀.pull φ₂)) :
    LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) := by
  have h₁ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) (P₀.pull (φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left)) :=
    MapComp.lbIso_pull_comp pol _ (diag_comp sq).symm
  have h₂ : LBIso ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) (P₀.pull (φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left)) :=
    MapComp.lbIso_pull_comp (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hP₀ _)) φ rfl
  exact LBIso.trans (pull_isLB hP _) (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP₀ _) _) h₁ h₂.symm

end GlobalTheory.UPel.HT.GeomDesc

open GlobalTheory.UPel.HT.GeomDesc in

theorem GlobalTheory.UPel.HT.geom_descends_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀) (N : ℕ) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (eta : D.La → (𝟙_ (Over X) ⟶ A)) (eta₀ : D.La → (𝟙_ (Over Y) ⟶ A₀)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ y, (eta y).left ≫ φ = π ≫ (eta₀ y).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A₀) (fun c g => g ≫ act₀.act c) (fun n g g' z => Out.WeilIs A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta₀ y = I.ev N y) := by
  intro p _ D R _ b X Y π sY Ga _ ρ A _ _ A₀ _ _ φ act act₀ N φ₂ P P₀ eta eta₀ hG hA hA₀ gp hact sq hP hP₀ pol heta hgeom k _ _ x β hx
  have := hG.etale
  have := hG.onto
  obtain ⟨y, rfl⟩ := GlobalTheory.ObjDesc.exists_geomPt_lift π k x
  obtain ⟨I, hI⟩ := hgeom k y β (by rw [← Category.assoc, hx])
  have iso := diag_lbIso sq hP hP₀ pol
  refine ⟨GlobalTheory.UPel.HT.TateIsoO.transport (GlobalTheory.ObjPull.pushEquiv gp (Over.mk y)) (fun c g => ?_)
    (fun n g g' c hc => ?_) I, fun a => ?_⟩
  · apply Over.OverMorphism.ext
    show (g ≫ act.act c).left ≫ φ = (GlobalTheory.ObjPull.pushEquiv gp (Over.mk y) g ≫ act₀.act c).left
    rw [Over.comp_left, Over.comp_left, Category.assoc, hact c, GlobalTheory.ObjPull.pushEquiv_left, Category.assoc]
  · exact (GlobalTheory.weilIs_grpPullback_of_comm Y X A₀ A π φ _ _ (pull_isLB hP₀ _) (pull_isLB hP _) gp iso
      (Over.mk y) n g g' _ _ _ (GlobalTheory.ObjPull.pushEquiv_left gp (Over.mk y) g)
      (GlobalTheory.ObjPull.pushEquiv_left gp (Over.mk y) g')).1 hc
  · rw [GlobalTheory.UPel.HT.TateIsoO.transport_ev, ← hI a]
    apply Over.OverMorphism.ext
    rw [GlobalTheory.ObjPull.pushEquiv_left]
    show (toUnit (Over.mk (y ≫ π)) ≫ eta₀ a).left = (toUnit (Over.mk y) ≫ eta a).left ≫ φ
    rw [Over.comp_left, Over.comp_left, Category.assoc, heta a, ← Category.assoc]
    congr 1

end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_tate_level_condition_descends_galois_cover : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀) (N : ℕ) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (eta : D.La → (𝟙_ (Over X) ⟶ A)) (eta₀ : D.La → (𝟙_ (Over Y) ⟶ A₀)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ y, (eta y).left ≫ φ = π ≫ (eta₀ y).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A₀) (fun c g => g ≫ act₀.act c) (fun n g g' z => Out.WeilIs A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta₀ y = I.ev N y) := by
  first | exact @GlobalTheory.UPel.HT.geom_descends_galoisCover | exact GlobalTheory.UPel.HT.geom_descends_galoisCover | (intros; apply GlobalTheory.UPel.HT.geom_descends_galoisCover; all_goals assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_similitude_fixing_point_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 3 ≤ N → N.Coprime p → 0 < M →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev → ∀ ρ : sympSimGrp h M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : sympSimGrp h M), y ≫ ρ a = y → a = 1 := by
  first | (exact @GlobalTheory.HTQuotRigid.eq_one_of_fixes_point) | (exact GlobalTheory.HTQuotRigid.eq_one_of_fixes_point) | (intros; apply GlobalTheory.HTQuotRigid.eq_one_of_fixes_point  <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.HTQuot

theorem objMap_comp_φ_of_comp {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂}
    {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

theorem obj_descends_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R]
    (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (G : Type)
    [Group G] (ρ : G → (X ⟶ X)) (o : Obj b N (π ≫ sY)), GlobalTheory.ZM.IsGaloisCover G ρ π → IsQProjOver (π ≫ sY) →
    IsQProjOver sY → (∀ a, Nonempty (ObjMap o o (ρ a))) → ∃ oY : Obj b N sY, Nonempty (ObjMap o oY π) := by
  intro p _ D R _ _ b N hN hNp X Y π sY G _ ρ o hG hq hqY hmaps
  have : IsLocallyNoetherian Y := by
    obtain ⟨M, i, hi, -, hi'⟩ := hqY
    have := isProper_str R M
    exact LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str R M)
  have m : ∀ a, ObjMap o o (ρ a) := fun a => (hmaps a).some
  let ν : G → (o.A.left ⟶ o.A.left) := fun a => (m a).φ
  have uniq : ∀ {f f' : X ⟶ X} (_ : f = f') (m₁ : ObjMap o o f) (m₂ : ObjMap o o f'), m₁.φ = m₂.φ := by
    rintro f f' rfl m₁ m₂
    exact GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique p D R b N hN hNp X X _ _ o o f m₁ m₂
  have ν1 : ν 1 = 𝟙 _ := by
    have key : ∀ {f : X ⟶ X} (_ : f = 𝟙 X) (m₁ : ObjMap o o f), m₁.φ = 𝟙 _ := by
      rintro f rfl m₁
      exact GlobalTheory.UPel.HT.Rigid.eq_id p D R b N hN hNp X _ o m₁
    exact key hG.one (m 1)
  have νmul : ∀ a c, ν (a * c) = ν a ≫ ν c := by
    intro a c
    obtain ⟨m', hm'⟩ := objMap_comp_φ_of_comp (m a) (m c)
    exact (uniq (hG.mul a c) (m (a * c)) m').trans hm'
  have hcart : ∀ a, IsGrpPullback o.A o.A (ρ a) (ν a) := fun a => (m a).cart
  have hqA : IsQProjOver (o.A.hom ≫ π ≫ sY) :=
    GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth R X (π ≫ sY) o.A _ hq (pull_isLB o.isLB _) o.ample
  obtain ⟨A₀, _, φ, hA₀, gp, hφ⟩ :=
    GlobalTheory.abelianScheme_descends_galoisCover_noetherian R X Y π sY G ρ o.A ν hG hqA o.ab hcart ν1 νmul
  have := hA₀.comm
  obtain ⟨act₀, hact⟩ := GlobalTheory.GaloisActDesc.exists_oActN_descend D.O X Y π G ρ o.A A₀ φ ν o.act hG o.ab hA₀ gp hφ
    hcart (fun a c => (m a).act c)
  obtain ⟨P₀, φ₂, hP₀, hsq, iso, rig0⟩ := GlobalTheory.SquareDescent.exists_bundle_descent X Y π G ρ o.A A₀ φ ν o.P hG o.ab
    hA₀ gp hφ hcart ν1 νmul o.isLB o.rig₁ (fun a => ⟨(m a).φ₂, (m a).sq, (m a).pol⟩)
  obtain ⟨rig₁, rig₂⟩ := GlobalTheory.T.descended_birigidified_bundle_trivial_on_axes X Y π G ρ o.A A₀ φ φ₂ o.P P₀ hG o.ab hA₀ gp hsq o.isLB hP₀ iso rig0 o.rig₁ o.rig₂
  have symm := GlobalTheory.T.descended_birigidified_bundle_swap_symmetric X Y π G ρ o.A A₀ φ φ₂ o.P P₀ hG o.ab hA₀ gp hsq o.isLB hP₀ iso rig0 o.symm
  have ample := GlobalTheory.T.relAmple_diagonal_descends_finiteEtaleGalois X Y π G ρ o.A A₀ φ φ₂ o.P P₀ hG o.ab hA₀ gp hsq o.isLB hP₀ iso o.ample
  have kerP : ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over Y) (x : T ⟶ A₀),
      (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1 := by
    obtain ⟨e, he, hk⟩ := o.kerP
    exact ⟨e, he, GlobalTheory.T.descended_polarisation_kernel_killed_same_integer X Y π G ρ o.A A₀ φ φ₂ o.P P₀ e hG o.ab hA₀ gp hsq o.isLB hP₀ iso hk⟩
  have rosati := GlobalTheory.T.rosati_condition_descends_galois_cover D.O (fun c => (D.star c).unop) X Y π G ρ o.A A₀ φ φ₂ o.P P₀ o.act act₀ hG o.ab hA₀ gp
    hsq o.isLB hP₀ iso rig0 hact o.rosati
  obtain ⟨eta₀, eta_add, eta_lin, eta_ker, heta⟩ := GlobalTheory.LevelSecDesc.levelSections_descend D.O D.La N X Y π G ρ o.A A₀ φ
    ν o.act act₀ o.eta hG gp hφ hact (fun a y => (m a).eta y) o.eta_add o.eta_lin o.eta_ker
  have lie := GlobalTheory.T.lie_condition_descends_finite_etale_galois_cover p D R b X Y π sY G ρ o.A A₀ φ o.act act₀ hG o.ab hA₀ gp hact o.lie
  have lieRank := GlobalTheory.T.lie_multiplicities_geometric_points_descend p D R b X Y π sY G ρ o.A A₀ φ o.act act₀ hG o.ab hA₀ gp hact o.lieRank
  have geom := GlobalTheory.T.geometric_tate_level_condition_descends_galois_cover p D R b X Y π sY G ρ o.A A₀ φ o.act act₀ N φ₂ o.P P₀ o.eta eta₀ hG o.ab hA₀ gp hact hsq
    o.isLB hP₀ iso heta o.geom
  let oY : Obj b N sY :=
    { A := A₀, ab := hA₀, act := act₀, P := P₀, isLB := hP₀, rig₁ := rig₁, rig₂ := rig₂, symm := symm
      ample := ample, kerP := kerP, rosati := rosati, lie := lie, lieRank := lieRank, eta := eta₀,
      eta_add := eta_add, eta_lin := eta_lin, eta_ker := eta_ker, geom := geom }
  exact ⟨oY, ⟨⟨φ, φ₂, gp, hsq, hact, iso, heta⟩⟩⟩

theorem exists_repFam_of_levelCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R]
    [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (u : Obj b N s) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)),
    IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) →
    (∀ a, Nonempty (ObjMap u u (ρ a))) →
    (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) →
    (∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
      ∃ (S₁ : Scheme.{0}) (π₁ : S₁ ⟶ S) (ρ₁ : Ga → (S₁ ⟶ S₁)) (y : S₁ ⟶ X) (o' : Obj b N (π₁ ≫ t)),
        GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ ∧ (∀ a, ρ₁ a ≫ y = y ≫ ρ a) ∧ y ≫ s = π₁ ≫ t ∧
        Nonempty (ObjMap o' o π₁) ∧ Nonempty (ObjMap o' u y)) →
    (∀ (T : Scheme.{0}) (t : T ⟶ Sp R) (o : Obj b N t) (x x' : T ⟶ X), x ≫ s = t → x' ≫ s = t →
      Nonempty (ObjMap o u x) → Nonempty (ObjMap o u x') →
      ∀ q : T, ∃ (V : T.Opens) (a : Ga), q ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x') →
    ∃ F : RepFam b N, IsQProjOver F.s := by
  intro p _ D R _ _ b N hN hNp X s u Ga _ _ ρ hq h1 hmul hbase hmaps hfree hcov huniq
  obtain ⟨Y, π, sY, hπs, hgal, hsep, hlft, -⟩ :=
    GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver_noetherian R X s Ga ρ hq h1 hmul hbase hfree
  have hqY : IsQProjOver sY := GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover R X Y π sY Ga ρ
    hgal hsep hlft (by rw [hπs]; exact hq)
  subst hπs
  obtain ⟨uY, ⟨mu⟩⟩ := obj_descends_galoisCover p D R b N hN hNp X Y π sY Ga ρ u hgal hq hqY hmaps
  have hrep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : Obj b N s'),
      ∃! f : S ⟶ Y, f ≫ sY = s' ∧ Nonempty (ObjMap o uY f) := by
    intro S s' o
    obtain ⟨S₁, π₁, ρ₁, y, o', hgal₁, hequi, hys, ⟨m₁⟩, ⟨m₂⟩⟩ := hcov S s' o
    have hinv : ∀ a, ρ₁ a ≫ (y ≫ π) = y ≫ π := by
      intro a; rw [← Category.assoc, hequi a, Category.assoc, hgal.inv a]
    obtain ⟨f, hf, hfu⟩ := hgal₁.existsUnique_desc (y ≫ π) hinv
    have canc : ∀ {Z : Scheme.{0}} (h₁ h₂ : S ⟶ Z), π₁ ≫ h₁ = π₁ ≫ h₂ → h₁ = h₂ := by
      intro Z h₁ h₂ e
      obtain ⟨w, -, hwu⟩ := hgal₁.existsUnique_desc (π₁ ≫ h₁) (fun a => by rw [← Category.assoc, hgal₁.inv a])
      exact (hwu h₁ rfl).trans (hwu h₂ e.symm).symm
    have hfs : f ≫ sY = s' := canc _ _ (by rw [← Category.assoc, hf, Category.assoc, hys])
    have hmf : Nonempty (ObjMap o uY f) := by
      obtain ⟨m₃⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ o' u uY y π m₂ mu
      rw [← hf] at m₃
      exact GlobalTheory.T.harrisTaylor_moduliMap_descends_galoisCover p D R b N S S₁ Y s' sY π₁ Ga ρ₁ f o o' uY hN hNp hgal₁ m₁ m₃
    refine ⟨f, ⟨hfs, hmf⟩, ?_⟩
    rintro f' ⟨hf's, ⟨m'⟩⟩
    obtain ⟨m₄⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ o' o uY π₁ f' m₁ m'
    obtain ⟨oT, ⟨mT⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S₁ (pullback (π₁ ≫ f') π) (π₁ ≫ s')
      (pullback.fst (π₁ ≫ f') π) o'
    obtain ⟨mT1⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ oT o' u _ y mT m₂
    obtain ⟨mT2⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ oT o' uY _ _ mT m₄
    rw [pullback.condition] at mT2
    obtain ⟨mT3⟩ := (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ oT u uY
      (pullback.snd (π₁ ≫ f') π) π).2 ⟨mT2⟩ ⟨mu⟩
    have key : y ≫ π = π₁ ≫ f' := by
      apply GlobalTheory.ZM.IsGaloisCover.eq_of_local_eq_pullback X Y S₁ Y π Ga ρ (π₁ ≫ f') (y ≫ π) (π₁ ≫ f') hgal
      intro q
      obtain ⟨V, a, hqV, hV⟩ := huniq _ _ oT (pullback.fst (π₁ ≫ f') π ≫ y) (pullback.snd (π₁ ≫ f') π)
        (by rw [Category.assoc, hys])
        (by rw [← Category.assoc, ← pullback.condition]; simp [hf's]) ⟨mT1⟩ ⟨mT3⟩ q
      refine ⟨V, hqV, ?_⟩
      calc V.ι ≫ pullback.fst (π₁ ≫ f') π ≫ y ≫ π
          = (V.ι ≫ (pullback.fst (π₁ ≫ f') π ≫ y) ≫ ρ a) ≫ π := by simp [hgal.inv]
        _ = (V.ι ≫ pullback.snd (π₁ ≫ f') π) ≫ π := by rw [hV]
        _ = V.ι ≫ pullback.fst (π₁ ≫ f') π ≫ π₁ ≫ f' := by rw [Category.assoc, ← pullback.condition]
    exact hfu f' key.symm
  exact ⟨⟨Y, sY, uY, hrep⟩, hqY⟩

theorem exists_representing_family_of_level_structure : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M → ∃ F : RepFam b N, IsQProjOver F.s := by
  intro p _ D R _ _ b N M e hN hNp hM hodd hMp hep hMe hperf hrep
  obtain ⟨X, s, s₁, u, lev, hlev, hq, huniv⟩ := hrep
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨ρ, h1, hmul, hact⟩ := GlobalTheory.T.exists_symplecticSimilitude_action_on_levelFamily p D R b N _ M (by omega) X s s₁ u lev hlev huniv
  exact exists_repFam_of_levelCover p D R b N hN hNp X s u _ ρ hq h1 hmul (fun a => (hact a).1)
    (fun a => let ⟨m, _⟩ := (hact a).2.2; ⟨m⟩)
    (GlobalTheory.T.harrisTaylor_similitude_fixing_point_eq_one p D R b N _ M hN hNp (by omega) X s s₁ u lev hlev ρ hact)
    (GlobalTheory.T.symplectic_level_over_cyclotomic p D R b N M e hN hNp hM hodd hMp hep hMe hperf X s s₁ u lev hlev huniv ρ hact)
    (GlobalTheory.T.exists_local_symplecticSimilitude_classifyingMaps p D R b N _ M hN hNp hM hodd hMp X s s₁ u lev hlev huniv ρ hact)

end GlobalTheory.HTQuot
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_representingFamily_of_auxiliaryRepresentation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M → ∃ F : RepFam b N, IsQProjOver F.s := by
  first | (exact @GlobalTheory.HTQuot.exists_representing_family_of_level_structure) | (exact GlobalTheory.HTQuot.exists_representing_family_of_level_structure) | (intros; apply GlobalTheory.HTQuot.exists_representing_family_of_level_structure <;> assumption)
end
