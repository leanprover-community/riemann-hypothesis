import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOfPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.PerFactor
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullEqZeroOfChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymLam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteMulByNatAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointPicardClassEqTranslateOfTrivialLambda
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTrivialRigidTranslateLineBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumCompatibleOfLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentCocycleDefectOfCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescentFiniteFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPolarizationFormPrimitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleObstructionZeroOfRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftSquareZeroOfMumfordBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotient
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDiv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxisTrivialLineBundleGroupPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetryHypothesisSpreadFromGenericFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivAdicCompletionLocalizationProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparablePointOfGeometricallyDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFiniteCommGroupSchemeCobounda
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKillingSquareTripleFibreCocycleMulTwo

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HensNbhd



end GlobalTheory.HensNbhd
end

section
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open MonoidalCategory CartesianMonoidalCategory Limits
open GlobalTheory.CechPic (Pic cls lam)
open MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleKerFibre

theorem relAmple_kTriv_of_lam_eq : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L₀ : LB B.left) (h₀ : L₀.IsLB), Out.RelAmple B L₀ → Out.KTriv B L₀ → ∀ (N : LB B.left) (hN : N.IsLB), lam (cls N hN) (fst B B) (snd B B) = lam (cls L₀ h₀) (fst B B) (snd B B) → Out.RelAmple B N ∧ Out.KTriv B N := by
  intro K _ _ B _ hB L₀ h₀ hA hK N hN hlam
  have := hB.comm
  obtain ⟨O, hO, eO⟩ := CechPic.cls_surj (cls N hN - cls L₀ h₀)
  have lamO : lam (cls O hO) (fst B B) (snd B B) = 0 := by
    rw [eO, GlobalTheory.PrimitiveOverField.lam_sub, hlam, sub_self]
  obtain ⟨x, hx⟩ := GlobalTheory.PointTranslate.exists_point_cls_eq_lam K B hB L₀ h₀ hK O hO lamO
  have hR : (GlobalTheory.RigidTranslate.rigTransl L₀ x).IsLB := LB.isLB_linComb h₀ _ _
  have hcls : cls _ hR = cls N hN := by
    rw [CechPic.cls_linComb h₀, Fin.sum_univ_two]
    have e1 : cls N hN = cls O hO + cls L₀ h₀ := by rw [eO]; abel
    rw [e1, hx, GlobalTheory.PrimitiveOverField.lam_const, Over.id_left, CechPic.pull_id]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul]
    rw [GlobalTheory.PrimitiveOverField.pull_const, GlobalTheory.PolTranslate.transl, _root_.mul_comm (𝟙 B)]
    abel
  have hiso := (CechPic.cls_eq_iff hR hN).1 hcls
  refine ⟨?_, GlobalTheory.MulDescent.kTriv_of_lbIso hR hN hiso
    (GlobalTheory.RigidTranslate.kTriv_rigTransl_any _ B L₀ h₀ x hK)⟩
  have hAR := GlobalTheory.RigidTranslate.relAmple_rigTransl_point K B hB L₀ h₀ x hA
  obtain ⟨w, hw⟩ : LBIso N ((GlobalTheory.RigidTranslate.rigTransl L₀ x).pull (𝟙 B.left)) :=
    hiso.symm.chartPull (Geo.Tor.chartPullId N) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl)
  exact relAmple_pull (A' := B) (IsPullback.id_horiz B.hom) hR hN ((isGen_iff w).1 hw) ⊤
    (isAffineOpen_top _) (fun _ => trivial) hAR

end GlobalTheory.AmpleKerFibre
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBAlgComplete

open GlobalTheory.CechPic GlobalTheory.ZV

theorem exists_lineBundle_of_reductions : GlobalTheory.Published.FormalAlgebraisation → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProjBy X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → (∀ e, LBIso (N e) ((N (e + 1)).pull (β e))) → ∃ M : LB X.left, M.IsLB ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro hP R _ _ I hI X hX Y β b hb hc N hN hv
  have hpr : IsProper X.hom := isProper_of_isProjBy R _ _ hX
  obtain ⟨H, hH, m, σ, hσ⟩ := hX
  have hA : IsAmpleLB H := isAmpleLB_of_veryAmpleBy hσ
  have hY : ∀ e, IsProper (Y e).hom := fun e => MorphismProperty.of_isPullback (P := @IsProper) (hb e) hpr
  have hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e) := fun e => by
    refine IsPullback.of_right (h₁₂ := b (e + 1)) (h₂₂ := thick R I (e + 1)) (v₁₃ := X.hom) ?_ ?_ (hb (e + 1))
    · rw [hc, thickTrans_comp]
      exact hb e
    · have : Mono (thick R I (e + 1)) := by
        have : IsClosedImmersion (thick R I (e + 1)) :=
          IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
        infer_instance
      rw [← cancel_mono (thick R I (e + 1)), Category.assoc, Category.assoc, thickTrans_comp, ← (hb (e + 1)).w,
        ← Category.assoc, hc, (hb e).w]
  have hL : ∀ e, (H.pull (b e)).IsLB := fun e => LB.isLB_pull hH _
  have hA₀ : IsAmpleLB (H.pull (b 0)) := by
    have : IsClosedImmersion (thick R I 0) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : IsClosedImmersion (b 0) :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hb 0).flip this
    exact hA.pull_of_isClosedImmersion _
  have := hY 0
  obtain ⟨t, ht⟩ := (AmpleDominates.eventually_isAmpleLB (Y 0).hom hA₀ (hN 0)).exists
  have hT : ∀ e, (LB.div (lbPow (H.pull (b e)) t) (N e)).IsLB := fun e =>
    LB.isLB_div (isLB_lbPow (hL e) t) (hN e)
  have eT : ∀ e, cls _ (hT e) = t • CechPic.pull (b e) (cls H hH) - cls _ (hN e) := fun e => by
    rw [cls_div (isLB_lbPow (hL e) t) (hN e), cls_lbPow (hL e), cls_pull hH]
  obtain ⟨X', M, b', hX', hM, -, hb', hc', hM'⟩ := hP.2 R I hI Y β hβ hY
    (fun e => LB.div (lbPow (H.pull (b e)) t) (N e)) hT
    (fun e => (cls_eq_iff (hT e) (LB.isLB_pull (hT (e + 1)) _)).1 (by
      rw [cls_pull (hT (e + 1)), eT, eT, (cls_eq_iff (hN e) (LB.isLB_pull (hN (e + 1)) _)).2 (hv e),
        cls_pull (hN (e + 1)), map_sub, map_nsmul, ← CechPic.pull_comp, hc]))
    ((relAmple_iff_isAmpleLB_of_isAffine (Y 0) (hT 0)).2 ht)
  obtain ⟨g, hg, -⟩ := hP.1.exists_iso hI hb hc hb' hc'
  have hMg : (M.pull g.hom.left).IsLB := LB.isLB_pull hM _
  have hF : (LB.div (lbPow H t) (M.pull g.hom.left)).IsLB := LB.isLB_div (isLB_lbPow hH t) hMg
  refine ⟨_, hF, fun e => (cls_eq_iff (hN e) (LB.isLB_pull hF _)).1 ?_⟩
  have e₁ := (cls_eq_iff (hT e) (LB.isLB_pull hM _)).2 (hM' e)
  rw [eT, cls_pull hM] at e₁
  rw [cls_pull hF, cls_div (isLB_lbPow hH t) hMg, cls_lbPow hH, cls_pull hM, map_sub, map_nsmul,
    ← CechPic.pull_comp, hg, ← e₁, sub_sub_cancel]

end GlobalTheory.LBAlgComplete
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_diagonal_pullback_baseChange : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (t : T ⟶ S) (B : Over T) (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left), IsPullback β B.hom A.hom t → IsSquare β β₂ → RelAmple B ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) := by
  first | exact @GlobalTheory.DiagAmpleBC.relAmple_diag_pull | exact GlobalTheory.DiagAmpleBC.relAmple_diag_pull | (intros; apply GlobalTheory.DiagAmpleBC.relAmple_diag_pull <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

namespace GlobalTheory.TowerStep
variable (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (e : ℕ)

theorem isGrpPullback_thickMap_factor : IsGrpPullback (thickObj R (maximalIdeal R) e B) (thickObj R (maximalIdeal R) (e + 1) B)
    (spMap (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
      R ⧸ maximalIdeal R ^ (e + 1 + 1) →+* R ⧸ maximalIdeal R ^ (e + 1))) (thickMap R (maximalIdeal R) e B) :=
  GlobalTheory.WtTower.isGrpPullback_thickMap (maximalIdeal R) B e

theorem thickMap_fst : thickMap R (maximalIdeal R) e B ≫ pullback.fst B.hom (thick R (maximalIdeal R) (e + 1)) =
    pullback.fst B.hom (thick R (maximalIdeal R) e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem isAbelianScheme_thickObj (hB : IsAbelianScheme B) : IsAbelianScheme (thickObj R (maximalIdeal R) (e + 1) B) :=
  GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B (thick R (maximalIdeal R) (e + 1)))

theorem exists_isSquare_thickMap : ∃ i₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left,
    IsSquare (thickMap R (maximalIdeal R) e B) i₂ :=
  GlobalTheory.ZM.SiegPull.exists_isSquare (G := thickObj R (maximalIdeal R) (e + 1) B) (G' := thickObj R (maximalIdeal R) e B)
    (f := thickTrans R (maximalIdeal R) e) (pullback.lift_snd _ _ _)

theorem ker_factor_sq {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ^ 2 = 0 := by
  have hle : RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ≤
      (I ^ (e + 1)).map (Ideal.Quotient.mk _) := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.mem_map_of_mem _ hx
  refine le_bot_iff.1 ((Ideal.pow_right_mono hle _).trans ?_)
  rw [← Ideal.map_pow, ← pow_mul, le_bot_iff, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact Ideal.pow_le_pow_right (by omega)

theorem isSquare_fst_comp {i₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left}
    {b₂' : (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left ⟶ (G2 B).left}
    (si : IsSquare (thickMap R (maximalIdeal R) e B) i₂)
    (sb : IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) (e + 1))) b₂') :
    IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) e)) (i₂ ≫ b₂') := by
  have h := GlobalTheory.ZM.SiegPull.isSquare_comp si sb
  rwa [thickMap_fst] at h

end GlobalTheory.TowerStep

open GlobalTheory.TowerStep in

theorem GlobalTheory.TowerStep.step : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (P : LB (G2 B).left), P.IsLB → (∃ u : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen) → (∃ u : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen) → ∀ (e : ℕ) (L : LB (thickObj R (maximalIdeal R) e B).left), L.IsLB → (∀ b₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 B).left, IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) e)) b₂ → LBIso (abelian₂ (thickObj R (maximalIdeal R) e B) L) (P.pull b₂)) → ∃ L' : LB (thickObj R (maximalIdeal R) (e + 1) B).left, L'.IsLB ∧ (∀ b₂ : (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left ⟶ (G2 B).left, IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) (e + 1))) b₂ → LBIso (abelian₂ (thickObj R (maximalIdeal R) (e + 1) B) L') (P.pull b₂)) ∧ LBIso (L'.pull (thickMap R (maximalIdeal R) e B)) L := by
  intro R _ _ B _ _ hB P hP h₁ h₂ e L hL hyp
  haveI := GlobalTheory.WtTower.isLocalRing_quotient_pow R e
  haveI := GlobalTheory.WtTower.isLocalRing_quotient_pow R (e + 1)
  have hπ := Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) :
    maximalIdeal R ^ (e + 1 + 1) ≤ maximalIdeal R ^ (e + 1))
  have gp₁ := isGrpPullback_pullback B (thick R (maximalIdeal R) (e + 1))
  have hab₁ := isAbelianScheme_thickObj R B e hB
  have hgp := isGrpPullback_thickMap_factor R B e
  obtain ⟨b₂', sb⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare gp₁.1.w
  obtain ⟨i₂, si⟩ := exists_isSquare_thickMap R B e
  have s₀ := isSquare_fst_comp R B e si sb
  have hP' : (P.pull b₂').IsLB := pull_isLB hP _
  have hLam : (abelian₂ (thickObj R (maximalIdeal R) e B) L).IsLB := DVR.linComb_isLB _ hL _ _
  have k : LBIso (abelian₂ (thickObj R (maximalIdeal R) e B) L) ((P.pull b₂').pull i₂) :=
    LBIso.trans hLam (pull_isLB hP _) (pull_isLB hP' _) (hyp _ s₀)
      (GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GtBaseChange.lbIso_refl hP') i₂).symm
  obtain ⟨L', hL', hLL⟩ := GlobalTheory.T.exists_lineBundle_lift_squareZero_of_mumfordBundle _ _ _ hπ (ker_factor_sq (maximalIdeal R) e) (thickObj R (maximalIdeal R) (e + 1) B)
    (thickObj R (maximalIdeal R) e B) (thickMap R (maximalIdeal R) e B) i₂ hab₁ hgp si (P.pull b₂') L hP' hL k
  obtain ⟨a₁, a₂⟩ := GlobalTheory.T.axisTrivial_lineBundle_groupPullback _ _ B P hP h₁ h₂ (thick R (maximalIdeal R) (e + 1)) (thickObj R (maximalIdeal R) (e + 1) B) _ b₂' gp₁ sb
  have rig := GlobalTheory.T.lineBundleIso_mumfordLambda_of_local_quotient _ _ _ hπ (thickObj R (maximalIdeal R) (e + 1) B) (thickObj R (maximalIdeal R) e B)
    (thickMap R (maximalIdeal R) e B) i₂ hab₁ hgp si (P.pull b₂') hP' a₁ a₂ L' L hL' hL hLL k
  refine ⟨L', hL', fun b₂ hb => ?_, hLL⟩
  rw [GlobalTheory.ZM.SiegPull.isSquare_unique hb sb rfl]
  exact rig
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_thickening_square_theorem : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (P : LB (G2 B).left), P.IsLB → (∃ u : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen) → (∃ u : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen) → ∀ (e : ℕ) (L : LB (thickObj R (maximalIdeal R) e B).left), L.IsLB → (∀ b₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 B).left, IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) e)) b₂ → LBIso (abelian₂ (thickObj R (maximalIdeal R) e B) L) (P.pull b₂)) → ∃ L' : LB (thickObj R (maximalIdeal R) (e + 1) B).left, L'.IsLB ∧ (∀ b₂ : (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left ⟶ (G2 B).left, IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) (e + 1))) b₂ → LBIso (abelian₂ (thickObj R (maximalIdeal R) (e + 1) B) L') (P.pull b₂)) ∧ LBIso (L'.pull (thickMap R (maximalIdeal R) e B)) L := by
  atlas_forward_decl GlobalTheory.TowerStep.step
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

namespace GlobalTheory.PolRootComplete

theorem root_given {S T : Scheme.{0}} {A : Over S} [GrpObj A] {P : LB (G2 A).left} (hP : P.IsLB) {t : T ⟶ S}
    (h : Root A P t) {B : Over T} [GrpObj B] [IsCommMonObj B] {β : B.left ⟶ A.left}
    {β₂ : (G2 B).left ⟶ (G2 A).left} (hβ : IsGrpPullback B A t β) (hsq : IsSquare β β₂) :
    ∃ L : LB B.left, L.IsLB ∧ LBIso (abelian₂ B L) (P.pull β₂) := by
  obtain ⟨C, _, _, c, c₂, hc, hsqc, L, hL, H⟩ := h
  let φ : B.left ⟶ C.left := hc.1.lift β B.hom hβ.1.w
  have hφc : φ ≫ c = β := hc.1.lift_fst _ _ _
  have hφw : φ ≫ C.hom = B.hom ≫ 𝟙 T := (hc.1.lift_snd _ _ _).trans (Category.comp_id _).symm
  have hφ : IsGrpPullback B C (𝟙 T) φ := hc.cancel (hβ.congr (Category.id_comp t).symm hφc.symm) hφw
  obtain ⟨φ₂, hφ₂⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare hφw
  have e : φ₂ ≫ c₂ = β₂ :=
    GlobalTheory.ZM.SiegPull.isSquare_unique (GlobalTheory.ZM.SiegPull.isSquare_comp hφ₂ hsqc) hsq hφc
  have hLφ : (L.pull φ).IsLB := pull_isLB hL φ
  refine ⟨L.pull φ, hLφ, ?_⟩
  have h1 : LBIso (abelian₂ B (L.pull φ)) ((abelian₂ C L).pull φ₂) :=
    GlobalTheory.ZM.SiegPull.lbIso_lam_pull hφ (GlobalTheory.GtBaseChange.lbIso_refl hLφ) hφ₂
  have h2 : LBIso ((abelian₂ C L).pull φ₂) (P.pull (φ₂ ≫ c₂)) := GlobalTheory.ZM.SiegPull.lbIso_pull_comp H φ₂
  rw [e] at h2
  exact LBIso.trans (LB.isLB_linComb hLφ _ _) (pull_isLB (LB.isLB_linComb hL _ _) _) (pull_isLB hP _) h1 h2

theorem root_of_closedFibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (maximalIdeal R) R) (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) (P : LB (G2 B).left) (hP : P.IsLB)
    (g1 : ∃ u : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen)
    (g2 : ∃ u : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen)
    (gamp : RelAmple B (P.pull (lift (𝟙 B) (𝟙 B)).left))
    (h0 : ∃ L₀ : LB (thickObj R (maximalIdeal R) 0 B).left, L₀.IsLB ∧
      ∀ b₂ : (G2 (thickObj R (maximalIdeal R) 0 B)).left ⟶ (G2 B).left,
        IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) 0)) b₂ →
          LBIso (abelian₂ (thickObj R (maximalIdeal R) 0 B) L₀) (P.pull b₂)) :
    ∃ L : LB B.left, L.IsLB ∧ LBIso (abelian₂ B L) P := by
  let Q : ∀ e, LB (thickObj R (maximalIdeal R) e B).left → Prop := fun e L => L.IsLB ∧
    ∀ b₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 B).left,
      IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) e)) b₂ →
        LBIso (abelian₂ (thickObj R (maximalIdeal R) e B) L) (P.pull b₂)
  have step : ∀ e (L : {L // Q e L}), ∃ L' : {L' // Q (e + 1) L'},
      LBIso (L'.1.pull (thickMap R (maximalIdeal R) e B)) L.1 := fun e L => by
    obtain ⟨L', h1', h2', h3'⟩ := GlobalTheory.T.line_bundle_thickening_square_theorem R B hB P hP g1 g2 e L.1 L.2.1 L.2.2
    exact ⟨⟨L', h1', h2'⟩, h3'⟩
  choose F hF using step
  obtain ⟨L₀, hL₀⟩ := h0
  let N : ∀ e, {L // Q e L} := fun e => Nat.rec ⟨L₀, hL₀⟩ (fun e L => F e L) e
  have hN : ∀ e, LBIso ((N (e + 1)).1.pull (thickMap R (maximalIdeal R) e B)) (N e).1 := fun e => hF e (N e)
  have hproj : GlobalTheory.AbLaw.IsProjBy B.hom := GlobalTheory.WtTower.isProjBy_of_relAmple B (pull_isLB hP _) gamp
  obtain ⟨M, hM, HM⟩ := GlobalTheory.LBAlgComplete.exists_lineBundle_of_reductions GlobalTheory.formalAlgebraisation R
    (maximalIdeal R) hR B hproj (fun e => thickObj R (maximalIdeal R) e B)
    (fun e => thickMap R (maximalIdeal R) e B) (fun e => pullback.fst B.hom (thick R (maximalIdeal R) e))
    (fun e => (isGrpPullback_pullback B (thick R (maximalIdeal R) e)).1)
    (fun e => (pullback.lift_fst _ _ _).trans (Category.comp_id _)) (fun e => (N e).1) (fun e => (N e).2.1)
    (fun e => (hN e).symm)
  haveI := GlobalTheory.WtTower.isLocalRing_quotient_pow R 0
  obtain ⟨b₂, hb₂⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare (isGrpPullback_pullback B (thick R (maximalIdeal R) 0)).1.w
  exact ⟨M, hM, GlobalTheory.T.lineBundleIso_mumfordLambda_of_local_quotient R (R ⧸ maximalIdeal R ^ (0 + 1)) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective B (thickObj R (maximalIdeal R) 0 B) (pullback.fst _ _) b₂ hB
    (isGrpPullback_pullback B _) hb₂ P hP g1 g2 M (N 0).1 hM (N 0).2.1 (HM 0).symm ((N 0).2.2 b₂ hb₂)⟩

theorem root_of_residue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ t : Sp R ⟶ S, Root A P (spMap (residue R) ≫ t) → Root A P t := by
  intro S A _ _ hA P hP h1 h2 hamp R _ _ _ hR t hroot
  obtain ⟨B, _, β, hβ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A t
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hβ
  haveI : IsCommMonObj B := hB.comm
  obtain ⟨β₂, hsq⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare hβ.1.w
  obtain ⟨g1, g2⟩ := GlobalTheory.T.axisTrivial_lineBundle_groupPullback S (Sp R) A P hP h1 h2 t B β β₂ hβ hsq
  have gamp := GlobalTheory.T.relAmple_diagonal_pullback_baseChange S (Sp R) A hA P hP hamp t B β β₂ hβ.1 hsq
  have le : maximalIdeal R ≤ maximalIdeal R ^ (0 + 1) := by rw [zero_add, pow_one]
  have ethick : thick R (maximalIdeal R) 0 =
      spMap (Ideal.Quotient.factor le) ≫ spMap (residue R) := by
    simp only [thick, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hres : Root A P (thick R (maximalIdeal R) 0 ≫ t) := by
    rw [ethick, Category.assoc]
    exact hroot.comp hA _
  have hY := isGrpPullback_pullback B (thick R (maximalIdeal R) 0)
  obtain ⟨b₂, hb₂⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare hY.1.w
  obtain ⟨L₀, hL₀, H₀⟩ := root_given hP hres (hY.comp hβ) (GlobalTheory.ZM.SiegPull.isSquare_comp hb₂ hsq)
  obtain ⟨L, hL, HL⟩ := root_of_closedFibre R hR B hB (P.pull β₂) (pull_isLB hP _) g1 g2 gamp
    ⟨L₀, hL₀, fun b₂' hb₂' => by
      have e : b₂' = b₂ := GlobalTheory.ZM.SiegPull.isSquare_unique hb₂' hb₂ rfl
      subst e
      exact LBIso.trans (LB.isLB_linComb hL₀ _ _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) H₀
        (GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.GtBaseChange.lbIso_refl (pull_isLB hP β₂)) b₂').symm⟩
  exact ⟨B, inferInstance, inferInstance, β, β₂, hβ, hsq, L, hL, HL⟩

end GlobalTheory.PolRootComplete
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_root_lifts_from_residue_complete_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ t : Sp R ⟶ S, Root A P (spMap (residue R) ≫ t) → Root A P t := by
  atlas_forward_decl GlobalTheory.PolRootComplete.root_of_residue
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

noncomputable section

open GlobalTheory

namespace GlobalTheory.RootFG

theorem lbIso_of_factor {Y Y' X₀ : Scheme.{0}} {M N : LB X₀} (a : Y ⟶ X₀) (j : Y' ⟶ Y) (a' : Y' ⟶ X₀)
    (e : a' = j ≫ a) (h : LBIso (M.pull a) (N.pull a)) : LBIso (M.pull a') (N.pull a') :=
  LBIso.chartPull (chartPullSame M _ _ _ j fun _ => e) (chartPullSame N _ _ _ j fun _ => e) h

theorem exists_fg_lbIso_of_isPullback {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C] {X : Scheme.{0}}
    (pB : X ⟶ Sp k) [QuasiCompact pB] [QuasiSeparated pB] {R₀ : Subalgebra k C} (h₀ : R₀.FG) {Y₀ Y : Scheme.{0}}
    (q₀ : Y₀ ⟶ Sp R₀) (a₀ : Y₀ ⟶ X) (hY₀ : IsPullback a₀ q₀ pB (spMap (algebraMap k R₀)))
    (y : Y ⟶ Y₀) (q : Y ⟶ Sp C) (hY : IsPullback y q q₀ (spMap R₀.val.toRingHom))
    (M N : LB Y₀) (hM : M.IsLB) (hN : N.IsLB) (H : LBIso (M.pull y) (N.pull y)) :
    ∃ (R : Subalgebra k C) (hR : R₀ ≤ R), R.FG ∧ ∀ (Y₁ : Scheme.{0}) (q₁ : Y₁ ⟶ Sp R) (y₁ : Y₁ ⟶ Y₀),
      y₁ ≫ q₀ = q₁ ≫ spMap (Subalgebra.inclusion hR).toRingHom → LBIso (M.pull y₁) (N.pull y₁) := by
  let e : pullback pB (spMap (algebraMap k R₀)) ⟶ Y₀ :=
    hY₀.lift (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  have e₁ : e ≫ a₀ = pullback.fst _ _ := hY₀.lift_fst _ _ _
  have e₂ : e ≫ q₀ = pullback.snd _ _ := hY₀.lift_snd _ _ _
  let f : pullback pB (spMap (algebraMap k C)) ⟶ Y :=
    hY.lift (baseChangeMap pB R₀.val ≫ e) (pullback.snd _ _) (by
      rw [Category.assoc, e₂, baseChangeMap_snd])
  have hf : f ≫ y = baseChangeMap pB R₀.val ≫ e := hY.lift_fst _ _ _
  have H₀ : LBIso ((M.pull e).pull (baseChangeMap pB R₀.val)) ((N.pull e).pull (baseChangeMap pB R₀.val)) := by
    have := lbIso_of_factor y f _ hf.symm H
    exact LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) (pull_isLB (pull_isLB hN _) _)
      (Spread.lbIso_pull_pull hM _ rfl).symm
      (LBIso.trans (pull_isLB hM _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) this
        (Spread.lbIso_pull_pull hN _ rfl))
  obtain ⟨R, hR, hRfg, H₁⟩ := exists_fg_lbIso pB h₀ (M.pull e) (N.pull e) (pull_isLB hM _) (pull_isLB hN _) H₀
  refine ⟨R, hR, hRfg, fun Y₁ q₁ y₁ w => ?_⟩
  have H₂ : LBIso (M.pull (baseChangeMap pB (Subalgebra.inclusion hR) ≫ e))
      (N.pull (baseChangeMap pB (Subalgebra.inclusion hR) ≫ e)) :=
    LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hN _)
      (Spread.lbIso_pull_pull hM _ rfl)
      (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hN _) H₁
        (Spread.lbIso_pull_pull hN _ rfl).symm)
  have hs : spMap (Subalgebra.inclusion hR).toRingHom ≫ spMap (algebraMap k R₀) = spMap (algebraMap k R) := by
    rw [spMap_comp_ring]; rfl
  let m : Y₁ ⟶ pullback pB (spMap (algebraMap k R)) :=
    pullback.lift (y₁ ≫ a₀) q₁ (by rw [Category.assoc, hY₀.w, ← Category.assoc, w, Category.assoc, hs])
  refine lbIso_of_factor _ m y₁ ?_ H₂
  apply hY₀.hom_ext
  · rw [Category.assoc, Category.assoc, e₁, baseChangeMap_fst, pullback.lift_fst]
  · rw [Category.assoc, Category.assoc, e₂, baseChangeMap_snd, pullback.lift_snd_assoc, w]

end GlobalTheory.RootFG

open GlobalTheory GlobalTheory.RootFG in

theorem GlobalTheory.RootFG.root_fg : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left),
    P.IsLB → ∀ (k : Type) [Field k] (t : Sp k ⟶ S) (C : Type) [CommRing C] [Algebra k C],
    Root A P (spMap (algebraMap k C) ≫ t) → ∃ B : Subalgebra k C, B.FG ∧ Root A P (spMap (algebraMap k B) ≫ t) := by
  intro S A _ hA P hP k _ t C _ _ hRt
  obtain ⟨B', _, _, β, β₂, hβ, hsq, L, hL, H⟩ := hRt
  obtain ⟨A₀, _, φ₀, h₀⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A t
  have hA₀ : IsAbelianScheme A₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₀
  have := hA₀.proper
  have : IsProper (A₀ ⊗ A₀).hom := by
    change IsProper (pullback.fst A₀.hom A₀.hom ≫ A₀.hom)
    infer_instance

  let φ' : B'.left ⟶ A₀.left := h₀.1.lift β (B'.hom ≫ spMap (algebraMap k C)) (by rw [hβ.1.w, Category.assoc])
  have hφ'₁ : φ' ≫ φ₀ = β := h₀.1.lift_fst _ _ _
  have hφ'₂ : φ' ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k C) := h₀.1.lift_snd _ _ _
  have hB'₀ : IsGrpPullback B' A₀ (spMap (algebraMap k C)) φ' :=
    IsGrpPullback.cancel h₀ (by rw [hφ'₁]; exact hβ) hφ'₂

  obtain ⟨R₁, M, ρ, hR₁, hM, hρ₁, hρ₂, HL⟩ := GlobalTheory.LBDescent.exists_fg_lb A₀.hom B'.hom φ' hB'₀.1 L hL
  obtain ⟨B₁, _, β₁, h₁⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A₀ (spMap (algebraMap k R₁))
  have hB₁ : IsAbelianScheme B₁ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ h₁
  haveI : IsCommMonObj B₁ := hB₁.comm
  let e₁ : B₁.left ⟶ pullback A₀.hom (spMap (algebraMap k R₁)) := h₁.1.isoPullback.hom
  let L₁ : LB B₁.left := M.pull e₁
  have hL₁ : L₁.IsLB := pull_isLB hM _
  let σ : Sp C ⟶ Sp R₁ := spMap R₁.val.toRingHom
  have hσ : σ ≫ spMap (algebraMap k R₁) = spMap (algebraMap k C) := by
    rw [spMap_comp_ring]; rfl
  let ψ : B'.left ⟶ B₁.left := h₁.1.lift φ' (B'.hom ≫ σ) (by rw [hφ'₂, Category.assoc, hσ])
  have hψ₁ : ψ ≫ β₁ = φ' := h₁.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ B₁.hom = B'.hom ≫ σ := h₁.1.lift_snd _ _ _
  have hψ : IsGrpPullback B' B₁ σ ψ := IsGrpPullback.cancel h₁ (by rw [hψ₁, hσ]; exact hB'₀) hψ₂
  have hρψ : ρ = ψ ≫ e₁ := by
    apply pullback.hom_ext
    · rw [hρ₁, Category.assoc, IsPullback.isoPullback_hom_fst, hψ₁]
    · rw [hρ₂, Category.assoc, IsPullback.isoPullback_hom_snd, hψ₂]
  have HL₁ : LBIso L (L₁.pull ψ) :=
    LBIso.trans hL (pull_isLB hM _) (pull_isLB hL₁ _) HL (Spread.lbIso_pull_pull hM ψ hρψ)

  have hc : IsGrpPullback B₁ A (spMap (algebraMap k R₁) ≫ t) (β₁ ≫ φ₀) := h₁.comp h₀
  let β₂₁ := (lift (pushPt hc.1.w (fst B₁ B₁)) (pushPt hc.1.w (snd B₁ B₁))).left
  have hsq₁ : IsSquare (β₁ ≫ φ₀) β₂₁ := GlobalTheory.LamPull.exists_isSquare hc.1.w
  let V := lift (pushPt hψ.1.w (fst B' B')) (pushPt hψ.1.w (snd B' B'))
  have hsqψ : IsSquare ψ V.left := GlobalTheory.LamPull.exists_isSquare hψ.1.w
  have c₁ : LBIso (abelian₂ B' L) ((abelian₂ B₁ L₁).pull V.left) :=
    GlobalTheory.SymSpread.lbIso_cube hψ hL₁ hL HL₁ (x2 B₁) (x2 B') V (fun i => by fin_cases i <;> simp [V, x2])
  have hβ₂ : β₂ = V.left ≫ β₂₁ := by
    have h' := GlobalTheory.ZM.SiegPull.isSquare_comp hsqψ hsq₁
    have eβ : ψ ≫ β₁ ≫ φ₀ = β := by rw [← Category.assoc, hψ₁, hφ'₁]
    rw [eβ] at h'
    apply pullback.hom_ext
    · exact hsq.1.trans h'.1.symm
    · exact hsq.2.trans h'.2.symm
  have hΛ₁ : (abelian₂ B₁ L₁).IsLB := LB.isLB_linComb hL₁ _ _
  have hΛ' : (abelian₂ B' L).IsLB := LB.isLB_linComb hL _ _
  have HV : LBIso ((abelian₂ B₁ L₁).pull V.left) ((P.pull β₂₁).pull V.left) :=
    LBIso.trans (pull_isLB hΛ₁ _) hΛ' (pull_isLB (pull_isLB hP _) _) c₁.symm
      (LBIso.trans hΛ' (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) H (Spread.lbIso_pull_pull hP V.left hβ₂))

  obtain ⟨R₂, h₁₂, hR₂, HD⟩ := exists_fg_lbIso_of_isPullback (A₀ ⊗ A₀).hom hR₁ (B₁ ⊗ B₁).hom _
    (GlobalTheory.SymSpread.isPullback_square h₁) V.left (B' ⊗ B').hom (GlobalTheory.SymSpread.isPullback_square hψ)
    (abelian₂ B₁ L₁) (P.pull β₂₁) hΛ₁ (pull_isLB hP _) HV
  let τ : Sp R₂ ⟶ Sp R₁ := spMap (Subalgebra.inclusion h₁₂).toRingHom
  have hτ : τ ≫ spMap (algebraMap k R₁) = spMap (algebraMap k R₂) := by
    rw [spMap_comp_ring]; rfl
  obtain ⟨B₂, _, κ, hκ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback B₁ τ
  have hB₂ : IsAbelianScheme B₂ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB₁ hκ
  haveI : IsCommMonObj B₂ := hB₂.comm
  refine ⟨R₂, hR₂, ?_⟩
  rw [← hτ, Category.assoc]
  let W := lift (pushPt hκ.1.w (fst B₂ B₂)) (pushPt hκ.1.w (snd B₂ B₂))
  have hsqW : IsSquare κ W.left := GlobalTheory.LamPull.exists_isSquare hκ.1.w
  have hL₂ : (L₁.pull κ).IsLB := pull_isLB hL₁ κ
  refine ⟨B₂, inferInstance, inferInstance, κ ≫ β₁ ≫ φ₀, W.left ≫ β₂₁, hκ.comp hc,
    GlobalTheory.ZM.SiegPull.isSquare_comp hsqW hsq₁, L₁.pull κ, hL₂, ?_⟩
  have d₁ : LBIso (abelian₂ B₂ (L₁.pull κ)) ((abelian₂ B₁ L₁).pull W.left) :=
    GlobalTheory.SymSpread.lbIso_cube hκ hL₁ hL₂ (lbIso_refl hL₂) (x2 B₁) (x2 B₂) W (fun i => by fin_cases i <;> simp [W, x2])
  have d₂ : LBIso ((abelian₂ B₁ L₁).pull W.left) ((P.pull β₂₁).pull W.left) :=
    HD _ (B₂ ⊗ B₂).hom W.left (GlobalTheory.SymSpread.isPullback_square hκ).w
  exact LBIso.trans (LB.isLB_linComb hL₂ _ _) (pull_isLB hΛ₁ _) (pull_isLB hP _) d₁
    (LBIso.trans (pull_isLB hΛ₁ _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) d₂
      (Spread.lbIso_pull_pull hP W.left rfl).symm)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundleRoot_exists_over_fg_subalgebra : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → ∀ (k : Type) [Field k] (t : Sp k ⟶ S) (C : Type) [CommRing C] [Algebra k C], Root A P (spMap (algebraMap k C) ≫ t) → ∃ B : Subalgebra k C, B.FG ∧ Root A P (spMap (algebraMap k B) ≫ t) := by
  atlas_forward_decl GlobalTheory.RootFG.root_fg
end

section
namespace GlobalTheory.PowerInRangeTensorRight

open TensorProduct

theorem exists_pow_pow_mem_range_includeRight (k K B : Type) [Field k] [Field K] [Algebra k K]
    [IsPurelyInseparable k K] [CommRing B] [Nontrivial B] [Algebra k B] (q : ℕ) [ExpChar k q]
    (z : TensorProduct k K B) :
    ∃ n : ℕ, z ^ q ^ n ∈
      AlgHom.range (Algebra.TensorProduct.includeRight : B →ₐ[k] TensorProduct k K B) := by
  rcases subsingleton_or_nontrivial (TensorProduct k K B) with hs | hnt
  · exact ⟨0, by rw [Subsingleton.elim (z ^ q ^ 0) 0]; exact zero_mem _⟩
  have : ExpChar (TensorProduct k K B) q :=
    expChar_of_injective_algebraMap (algebraMap k (TensorProduct k K B)).injective q
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x b =>
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem k q x
    refine ⟨n, (AlgHom.mem_range _).mpr ⟨c • b ^ q ^ n, ?_⟩⟩
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_pow, ← hc,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨n1, h1⟩ := hx
    obtain ⟨n2, h2⟩ := hy
    refine ⟨n1 + n2, ?_⟩
    have e1 : x ^ q ^ (n1 + n2) = (x ^ q ^ n1) ^ q ^ n2 := by rw [pow_add, pow_mul]
    have e2 : y ^ q ^ (n1 + n2) = (y ^ q ^ n2) ^ q ^ n1 := by rw [pow_add, mul_comm, pow_mul]
    rw [add_pow_expChar_pow, e1, e2]
    exact add_mem (pow_mem h1 _) (pow_mem h2 _)

end GlobalTheory.PowerInRangeTensorRight
end

section
section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

theorem pow_mem_range_includeRight_of_isPurelyInseparable (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [Nontrivial B] [Algebra k B]
    (q : ℕ) [ExpChar k q] (z : K ⊗[k] B) :
    ∃ n : ℕ, z ^ q ^ n ∈
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).range := by
  first
  | exact @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
  | exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
  | (apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight ..)

theorem idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [IsLocalRing B] [Algebra k B]
    (e : K ⊗[k] B) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  obtain ⟨n, b, hb⟩ :=
    pow_mem_range_includeRight_of_isPurelyInseparable k K B (ringExpChar k) e
  have hpos : ringExpChar k ^ n ≠ 0 := (pow_pos (expChar_pos k _) n).ne'
  have h1 : e ^ (ringExpChar k ^ n) = e := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    rw [hm]; exact he.pow_succ_eq m
  rw [h1] at hb
  have hb' : (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) b = e := hb
  have hbi : b * b = b := by
    apply hinj
    rw [map_mul, hb']; exact he
  rcases isUnit_or_isUnit_one_sub_self b with hu | hu
  · right
    have : b = 1 := hu.mul_left_cancel (by rw [hbi, mul_one])
    rw [← hb', this, map_one]
  · left
    have : b = 0 := hu.mul_left_cancel (by rw [sub_mul, hbi, one_mul, sub_self, mul_zero])
    rw [← hb', this, map_zero]

end GlobalTheory
end

open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable' : ∀ (k K B : Type) [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [IsLocalRing B] [Algebra k B] (e : K ⊗[k] B), IsIdempotentElem e → e = 0 ∨ e = 1 := by
  atlas_forward_decl GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable
end

section
section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

theorem isRegularLocalRing_atPrime_of_ringEquiv_isLocalization {B T T' : Type} [CommRing B]
    [IsRegularRing B] [CommRing T] [CommRing T'] [Algebra B T'] (M : Submonoid B)
    [IsLocalization M T'] (e : T ≃+* T') (𝔫 : Ideal T) [𝔫.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime 𝔫) := by
  letI : Algebra B T := ((e.symm : T' →+* T).comp (algebraMap B T')).toAlgebra
  let e' : T' ≃ₐ[B] T := AlgEquiv.ofRingEquiv (f := e.symm) (fun x => rfl)
  haveI : IsLocalization M T := IsLocalization.isLocalization_of_algEquiv M e'
  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔫) (𝔫.comap (algebraMap B T)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime 𝔫) 𝔫
  haveI : IsRegularLocalRing (Localization.AtPrime (𝔫.comap (algebraMap B T))) :=
    IsRegularRing.isRegularLocalRing_localization _
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (𝔫.comap (algebraMap B T)).primeCompl
      (Localization.AtPrime (𝔫.comap (algebraMap B T))) (Localization.AtPrime 𝔫)).toRingEquiv

theorem isRegularLocalRing_atPrime_localization_tensor : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (r : ℕ) (𝔪 : Ideal (MvPolynomial (Fin r) k)) [𝔪.IsPrime] (𝔫 : Ideal (Localization.AtPrime 𝔪 ⊗[k] K)) [𝔫.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔫) := by
  intro k K _ _ _ r 𝔪 _ 𝔫 _
  letI : Algebra (MvPolynomial (Fin r) k ⊗[k] K)
      (Localization.AtPrime 𝔪 ⊗[MvPolynomial (Fin r) k] (MvPolynomial (Fin r) k ⊗[k] K)) :=
    Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin r) k ⊗[k] K) 𝔪.primeCompl)
      (Localization.AtPrime 𝔪 ⊗[MvPolynomial (Fin r) k] (MvPolynomial (Fin r) k ⊗[k] K)) :=
    IsLocalization.tensorRight (Localization.AtPrime 𝔪) 𝔪.primeCompl
  let h : (MvPolynomial (Fin r) k ⊗[k] K) ≃+* MvPolynomial (Fin r) K :=
    (Algebra.TensorProduct.comm k (MvPolynomial (Fin r) k) K).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv
  haveI := IsLocalization.isLocalization_of_base_ringEquiv
    (Algebra.algebraMapSubmonoid (MvPolynomial (Fin r) k ⊗[k] K) 𝔪.primeCompl)
    (Localization.AtPrime 𝔪 ⊗[MvPolynomial (Fin r) k] (MvPolynomial (Fin r) k ⊗[k] K)) h
  letI : Algebra (MvPolynomial (Fin r) K)
      (Localization.AtPrime 𝔪 ⊗[MvPolynomial (Fin r) k] (MvPolynomial (Fin r) k ⊗[k] K)) :=
    ((algebraMap (MvPolynomial (Fin r) k ⊗[k] K) _).comp h.symm.toRingHom).toAlgebra
  exact isRegularLocalRing_atPrime_of_ringEquiv_isLocalization
    (Submonoid.map h (Algebra.algebraMapSubmonoid (MvPolynomial (Fin r) k ⊗[k] K) 𝔪.primeCompl))
    (Algebra.TensorProduct.cancelBaseChange k (MvPolynomial (Fin r) k) (Localization.AtPrime 𝔪)
      (Localization.AtPrime 𝔪) K).symm.toRingEquiv 𝔫

end GlobalTheory
end

open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularLocalRing_localization_atPrime_tensor_field : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (r : ℕ) (𝔪 : Ideal (MvPolynomial (Fin r) k)) [𝔪.IsPrime] (𝔫 : Ideal (Localization.AtPrime 𝔪 ⊗[k] K)) [𝔫.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔫) := by
  atlas_forward_decl GlobalTheory.isRegularLocalRing_atPrime_localization_tensor
end

section
section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.SepRing

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem isDomain_tensor_of_reg (k K S : Type) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsPurelyInseparable k K] [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [Algebra k S]
    (hreg : ∀ (𝔫 : Ideal (S ⊗[k] K)) [𝔫.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔫)) :
    IsDomain (K ⊗[k] AdicCompletion (maximalIdeal S) S) := by
  have hinj : Function.Injective (algebraMap S (S ⊗[k] K)) :=
    Algebra.TensorProduct.includeLeft_injective (R := k) (S := k) (A := S) (B := K)
      (algebraMap k K).injective
  have hker : RingHom.ker (algebraMap S (S ⊗[k] K)) ≤ maximalIdeal S := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [hinj (hx.trans (map_zero _).symm)]
    exact zero_mem _
  obtain ⟨𝔫, h𝔫max, h𝔫⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S ⊗[k] K)
    (maximalIdeal S) hker
  haveI := h𝔫max.isPrime
  obtain ⟨S', _, e, -⟩ := GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod S (S ⊗[k] K)
    (Localization.AtPrime 𝔫) 𝔫 h𝔫
  haveI : IsRegularLocalRing (Localization.AtPrime 𝔫) := hreg 𝔫
  haveI : IsRegularLocalRing (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔫))
      (Localization.AtPrime 𝔫)) := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion _
  haveI hdom : IsDomain (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔫))
      (Localization.AtPrime 𝔫)) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  let f : K ⊗[k] AdicCompletion (maximalIdeal S) S ≃+* _ :=
    (Algebra.TensorProduct.comm k K (AdicCompletion (maximalIdeal S) S)).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange k S (AdicCompletion (maximalIdeal S) S)
      (AdicCompletion (maximalIdeal S) S) K).symm.toRingEquiv.trans e)
  have hS' : Subsingleton S' := by
    have hid : IsIdempotentElem (f.symm (0, 1)) := by
      show f.symm (0,1) * f.symm (0,1) = f.symm (0,1)
      rw [← map_mul]; simp
    rcases GlobalTheory.T.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable' k K (AdicCompletion (maximalIdeal S) S) (f.symm (0, 1)) hid with h | h
    · have h2 := congrArg (fun z => (f z).2) h
      simp at h2
      exact subsingleton_of_zero_eq_one h2.symm
    · have h2 := congrArg (fun z => (f z).1) h
      simp at h2
  exact Function.Injective.isDomain ((RingHom.fst _ _).comp f.toRingHom) (by
    intro x y hxy
    apply f.injective
    exact Prod.ext hxy (Subsingleton.elim _ _))

end GlobalTheory.SepRing

namespace GlobalTheory.SepRing

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem exists_complete_local_geomDomain : ∀ (k k' : Type) [Field k] [CommRing k'] [IsDomain k']
    [Algebra k k'], Module.Finite k k' → ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C)
    (_ : IsNoetherianRing C) (_ : Algebra k C), IsAdicComplete (maximalIdeal C) C ∧
    Nonempty (k' →ₐ[k] ResidueField C) ∧ ∀ (K : Type) [Field K] [Algebra k K],
    FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] C) := by
  intro k k' _ _ _ _ hfin
  haveI : Algebra.FiniteType k k' := inferInstance
  obtain ⟨r, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp this
  have hk' : IsField k' :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap k k').injective).mp (Field.toIsField k)
  letI : Field k' := hk'.toField
  let 𝔪 : Ideal (MvPolynomial (Fin r) k) := RingHom.ker φ.toRingHom
  haveI h𝔪 : 𝔪.IsMaximal := RingHom.ker_isMaximal_of_surjective φ.toRingHom hφ
  let S := Localization.AtPrime 𝔪
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing 𝔪.primeCompl S inferInstance
  refine ⟨AdicCompletion (maximalIdeal S) S, inferInstance, inferInstance,
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion S _, inferInstance, inferInstance, ?_, ?_⟩
  · let C := AdicCompletion (maximalIdeal S) S
    let g : MvPolynomial (Fin r) k →ₐ[k] ResidueField C :=
      IsScalarTower.toAlgHom k (MvPolynomial (Fin r) k) (ResidueField C)
    have hg : ∀ a ∈ 𝔪, g a = 0 := by
      intro a ha
      have h1 : algebraMap (MvPolynomial (Fin r) k) S a ∈ maximalIdeal S := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ ha
      have h2 : algebraMap S C (algebraMap _ S a) ∈ maximalIdeal C := by
        rw [AdicCompletion.maximalIdeal_eq_map]; exact Ideal.mem_map_of_mem _ h1
      show algebraMap _ (ResidueField C) a = 0
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin r) k) C (ResidueField C),
        IsScalarTower.algebraMap_apply (MvPolynomial (Fin r) k) S C]
      exact (residue_eq_zero_iff _).mpr h2
    exact ⟨(Ideal.Quotient.liftₐ 𝔪 g hg).comp
      (Ideal.quotientKerAlgEquivOfSurjective hφ).symm.toAlgHom⟩
  · intro K _ _ hK hpi
    exact isDomain_tensor_of_reg k K S (fun 𝔫 _ => GlobalTheory.T.isRegularLocalRing_localization_atPrime_tensor_field k K r 𝔪 𝔫)

end GlobalTheory.SepRing
end

open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_local_geomDomain' : ∀ (k k' : Type) [Field k] [CommRing k'] [IsDomain k'] [Algebra k k'], Module.Finite k k' → ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C) (_ : Algebra k C), IsAdicComplete (maximalIdeal C) C ∧ Nonempty (k' →ₐ[k] ResidueField C) ∧ ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] C) := by
  atlas_forward_decl GlobalTheory.SepRing.exists_complete_local_geomDomain
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqDatum

theorem mem_lbPow_U {X : Scheme.{0}} {M : LB X} {n : ℕ} {x : X} {i : PUnit → M.ι} :
    x ∈ (lbPow M n).U i ↔ x ∈ M.U (i PUnit.unit) :=
  ⟨fun h => by simpa using Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => by simpa using h⟩

theorem lbPow_U_le {X : Scheme.{0}} (M : LB X) (n : ℕ) (i : PUnit → M.ι) :
    (lbPow M n).U i ≤ M.U (i PUnit.unit) := fun _ h => mem_lbPow_U.1 h

theorem chart_le {X Y : Scheme.{0}} (f : X ⟶ Y) (M : LB X) (n : ℕ) (i j : PUnit → M.ι) :
    chart f (lbPow M n) i j ≤ chart f M (i PUnit.unit) (j PUnit.unit) :=
  inf_le_inf (Scheme.Hom.preimage_mono _ (lbPow_U_le M n i)) (Scheme.Hom.preimage_mono _ (lbPow_U_le M n j))

theorem gm_lbPow_g {X Z : Scheme.{0}} (M : LB X) (n : ℕ) (p : Z ⟶ X) (z : Z) (i i' : PUnit → M.ι)
    (hi : p z ∈ M.U (i PUnit.unit)) (hi' : p z ∈ M.U (i' PUnit.unit)) :
    gm p z _ ((lbPow M n).g i i') = gm p z _ (M.g (i PUnit.unit) (i' PUnit.unit)) ^ n := by
  show gm p z _ (∏ _k : PUnit, (res _ (pullU (𝟙 X) _ (M.g (i PUnit.unit) (i' PUnit.unit)))) ^ ((n : ℕ) : ℤ)) = _
  rw [Fintype.prod_unique, map_zpow, zpow_natCast]
  congr 1
  refine (gm_res p z _ (show p z ∈ LB.wchart M (fun _ : PUnit => 𝟙 X) i ⊓ LB.wchart M (fun _ : PUnit => 𝟙 X) i' from
    ⟨(mem_lbPow_U (n := n)).2 hi, (mem_lbPow_U (n := n)).2 hi'⟩) _).trans ?_
  refine (gm_pull p (𝟙 X) z _ (by simpa using And.intro hi hi') _).trans ?_
  rw [Category.comp_id]

theorem gm_pullTop {X Y : Scheme.{0}} (p : X ⟶ Y) (w : X) (u : Γ(Y, ⊤)ˣ) :
    gm (𝟙 X) w ⊤ (GlobalTheory.CharKer.pullTop p u) = gm p w ⊤ u := by
  apply Units.ext
  rw [gm_val _ w ⊤ trivial, gm_val _ w ⊤ trivial]
  simp [GlobalTheory.CharKer.pullTop]
  rfl

end GlobalTheory.SqDatum

namespace GlobalTheory.SqDatum

theorem commGroup_mul_eq_mul_mul_div {G : Type*} [CommGroup G] (a b c d x y z : G) (h₁ : d * c = a * b) (h₂ : d ^ 2 * x * y = z) :
    (a ^ 2 * x) * (b ^ 2 * y) = c ^ 2 * z := by
  rw [← h₂]
  calc (a ^ 2 * x) * (b ^ 2 * y) = (a * b) ^ 2 * x * y := by simp only [mul_pow]; ac_rfl
    _ = (d * c) ^ 2 * x * y := by rw [h₁]
    _ = c ^ 2 * (d ^ 2 * x * y) := by simp only [mul_pow]; ac_rfl

def psi {X Y : Scheme.{0}} (f : X ⟶ Y) (M : LB X) (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ)
    (u : Γ(pullback f f, ⊤)ˣ) : ∀ i j, Γ(pullback f f, chart f (lbPow M 2) i j)ˣ :=
  fun i j => res (chart_le f M 2 i j) (φ (i PUnit.unit) (j PUnit.unit)) ^ 2 * res le_top u

theorem gm_psi {X Y Z : Scheme.{0}} (f : X ⟶ Y) (M : LB X) (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ)
    (u : Γ(pullback f f, ⊤)ˣ) (p : Z ⟶ pullback f f) (z : Z) (i j : PUnit → M.ι)
    (h : p z ∈ chart f (lbPow M 2) i j) :
    gm p z _ (psi f M φ u i j) = gm p z _ (φ (i PUnit.unit) (j PUnit.unit)) ^ 2 * gm p z ⊤ u := by
  dsimp only [psi]
  rw [map_mul, map_pow, gm_res p z _ h, gm_res p z _ h]

theorem pullback_fst_snd_triple_eq_snd_fst {X Y : Scheme.{0}} (f : X ⟶ Y) (w : Triple f) :
    pullback.fst f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) =
      pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]

theorem pullback_fst_tripleFibreProductProjOneThree {X Y : Scheme.{0}} (f : X ⟶ Y) (w : Triple f) :
    pullback.fst f f (pr13 f w) = pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pr13, pullback.lift_fst]

theorem pullback_snd_tripleFibreProductProjOneThree {X Y : Scheme.{0}} (f : X ⟶ Y) (w : Triple f) :
    pullback.snd f f (pr13 f w) = pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pr13, pullback.lift_snd]

theorem exists_sq_descent : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB →
    ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ) (u : Γ(pullback f f, ⊤)ˣ),
    DescCompat f M φ → Defect f M φ D → KillsSq f D u →
    ∃ (M₂ : LB X) (ψ : ∀ i j, Γ(pullback f f, chart f M₂ i j)ˣ),
      M₂.IsLB ∧ LBIso (lbPow M 2) M₂ ∧ DescCompat f M₂ ψ ∧ DescCocycle f M₂ ψ := by
  intro X Y f M hM φ D u hC hD hK
  have h₂ : (lbPow M 2).IsLB := LB.isLB_linComb hM _ _
  refine ⟨lbPow M 2, psi f M φ u, h₂, GlobalTheory.lbIso_refl h₂, ?_, ?_⟩
  · intro z i i' j j' hi hi' hj hj'
    rw [gm_psi f M φ u (𝟙 _) z i' j' ⟨hi', hj'⟩, gm_psi f M φ u (𝟙 _) z i j ⟨hi, hj⟩,
      gm_lbPow_g M 2 _ z i i' (mem_lbPow_U.1 hi) (mem_lbPow_U.1 hi'),
      gm_lbPow_g M 2 _ z j' j (mem_lbPow_U.1 hj') (mem_lbPow_U.1 hj),
      hC z _ _ _ _ (mem_lbPow_U.1 hi) (mem_lbPow_U.1 hi') (mem_lbPow_U.1 hj) (mem_lbPow_U.1 hj')]
    simp only [mul_pow]
    ac_rfl
  · intro w i j k hi hj hk
    have hj' : pullback.fst f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) ∈ (lbPow M 2).U j := by
      rw [pullback_fst_snd_triple_eq_snd_fst]; exact hj
    have h13 : pr13 f w ∈ chart f (lbPow M 2) i k := by
      refine ⟨?_, ?_⟩
      · exact (show pullback.fst f f (pr13 f w) ∈ (lbPow M 2).U i by rw [pullback_fst_tripleFibreProductProjOneThree]; exact hi)
      · exact (show pullback.snd f f (pr13 f w) ∈ (lbPow M 2).U k by rw [pullback_snd_tripleFibreProductProjOneThree]; exact hk)
    rw [gm_psi f M φ u _ w i j ⟨hi, hj⟩, gm_psi f M φ u _ w j k ⟨hj', hk⟩, gm_psi f M φ u _ w i k h13]
    have hd := hD (Triple f) (𝟙 _) w (i PUnit.unit) (j PUnit.unit) (k PUnit.unit)
      (mem_lbPow_U.1 hi) (mem_lbPow_U.1 hj) (mem_lbPow_U.1 hk)
    simp only [Category.id_comp] at hd
    have hk' := congrArg (gm (𝟙 _) w ⊤) hK
    simp only [map_mul, map_pow, gm_pullTop] at hk'
    exact commGroup_mul_eq_mul_mul_div _ _ _ _ _ _ _ hd hk'

end GlobalTheory.SqDatum
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareBundle_descent_of_defect_killed : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ) (u : Γ(pullback f f, ⊤)ˣ), DescCompat f M φ → Defect f M φ D → KillsSq f D u → ∃ (M₂ : LB X) (ψ : ∀ i j, Γ(pullback f f, chart f M₂ i j)ˣ), M₂.IsLB ∧ LBIso (lbPow M 2) M₂ ∧ DescCompat f M₂ ψ ∧ DescCocycle f M₂ ψ := by
  atlas_forward_decl GlobalTheory.SqDatum.exists_sq_descent
end

section
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm

namespace GlobalTheory.PolRoot

private theorem gm_charPullTop {X T : Scheme.{0}} (r : T ⟶ X) (t : T) (a : Γ(X, ⊤)ˣ) :
    gm (𝟙 T) t ⊤ (GlobalTheory.CharKer.pullTop r a) = gm r t ⊤ a :=
  (gm_pull (𝟙 T) r t ⊤ trivial a).trans (by rw [Category.id_comp])

theorem defect_tri {X Y T : Scheme.{0}} {f : X ⟶ Y} {M : LB X} {φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ}
    {D : Γ(Triple f, ⊤)ˣ} (h : Defect f M φ D) (a b c : T ⟶ X) (h₁ : a ≫ f = b ≫ f) (h₂ : b ≫ f = c ≫ f)
    (t : T) (i j k : M.ι) (hi : a t ∈ M.U i) (hj : b t ∈ M.U j) (hk : c t ∈ M.U k) :
    gm (tri f a b c h₁ h₂) t ⊤ D * gm (pullback.lift a c (h₁.trans h₂)) t _ (φ i k) =
      gm (pullback.lift a b h₁) t _ (φ i j) * gm (pullback.lift b c h₂) t _ (φ j k) := by
  have e₁ : tri f a b c h₁ h₂ ≫ pullback.fst (pullback.snd f f) (pullback.fst f f) = pullback.lift a b h₁ :=
    pullback.lift_fst _ _ _
  have e₂ : tri f a b c h₁ h₂ ≫ pullback.snd (pullback.snd f f) (pullback.fst f f) = pullback.lift b c h₂ :=
    pullback.lift_snd _ _ _
  have e₃ : tri f a b c h₁ h₂ ≫ pr13 f = pullback.lift a c (h₁.trans h₂) := by
    apply pullback.hom_ext
    · rw [pr13, Category.assoc, pullback.lift_fst, reassoc_of% e₁, pullback.lift_fst]
      try rw [pullback.lift_fst]
    · rw [pr13, Category.assoc, pullback.lift_snd, reassoc_of% e₂, pullback.lift_snd]
      try rw [pullback.lift_snd]
  have := h T (tri f a b c h₁ h₂) t i j k
    (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reassoc_of% e₁, pullback.lift_fst]; exact hi)
    (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reassoc_of% e₁, pullback.lift_snd]; exact hj)
    (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reassoc_of% e₂, pullback.lift_snd]; exact hk)
  rwa [e₁, e₂, e₃] at this

theorem triCocycle_of_defect : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ), Defect f M φ D → TriCocycle f D := by
  intro X Y f M hM φ D h T a b c d h₁ h₂ h₃
  refine unit_ext fun t _ => ?_
  obtain ⟨i, hi⟩ := exists_chart hM (a t)
  obtain ⟨j, hj⟩ := exists_chart hM (b t)
  obtain ⟨k, hk⟩ := exists_chart hM (c t)
  obtain ⟨l, hl⟩ := exists_chart hM (d t)
  have e₁ := defect_tri h a b c h₁ h₂ t i j k hi hj hk
  have e₂ := defect_tri h a c d (h₁.trans h₂) h₃ t i k l hi hk hl
  have e₃ := defect_tri h b c d h₂ h₃ t j k l hj hk hl
  have e₄ := defect_tri h a b d h₁ (h₂.trans h₃) t i j l hi hj hl
  rw [map_mul, map_mul, gm_charPullTop, gm_charPullTop, gm_charPullTop, gm_charPullTop]
  apply mul_right_cancel (b := gm (pullback.lift a d ((h₁.trans h₂).trans h₃)) t _ (φ i l))
  rw [_root_.mul_assoc, _root_.mul_assoc, e₂, e₄, ← _root_.mul_assoc, e₁, _root_.mul_left_comm, e₃, _root_.mul_assoc]

end GlobalTheory.PolRoot
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descentCocycleDefect_isTripleCocycle : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ), Defect f M φ D → TriCocycle f D := by
  atlas_forward_decl GlobalTheory.PolRoot.triCocycle_of_defect
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolBundleLoc

open GlobalTheory.PolRoot GlobalTheory.CechPic GlobalTheory.LamOfDouble

theorem exists_rigLB_cubical (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) (L : LB B.left) (hL : L.IsLB) : ∃ M : RigLB B, M.L = L ∧ Nonempty (CubicalStr B M) := by
  have hR : Out.Rigidified B L := GlobalTheory.LB.exists_isGen_of_isLocalRing (R := R) (pull_isLB hL _)
  exact GlobalTheory.Moduli.cubicalStr_of_triv_theta GlobalTheory.abelianSchemeLaws_all.1 _ B hB L hL hR
    (GlobalTheory.HodgeWeil.triv_theta GlobalTheory.CubeTop.cubeTheorem hB hL)

theorem exists_descent_two {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {M : LB A.left} (hM : M.IsLB)
    (H : LBIso (M.pull (pullback.fst ((𝟙 A) ^ 2 : A ⟶ A).left ((𝟙 A) ^ 2 : A ⟶ A).left))
      (M.pull (pullback.snd ((𝟙 A) ^ 2 : A ⟶ A).left ((𝟙 A) ^ 2 : A ⟶ A).left))) :
    ∃ L : LB A.left, L.IsLB ∧ LBIso (lbPow M 2) (L.pull ((𝟙 A) ^ 2 : A ⟶ A).left) := by
  have hf := GlobalTheory.MulFinite.isFinite_mul K A hA 2 (by norm_num)
  have hm : IsMonHom ((𝟙 A) ^ 2 : A ⟶ A) := by
    rw [← GlobalTheory.GrpTangent.mulN_eq_pow]; infer_instance
  obtain ⟨hfl, hsu⟩ := GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K A hA _ hm hf
  have := hA.smooth
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨φ, hφ⟩ := GlobalTheory.LBDescent.descCompat_of_lbIso _ M hM H
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_descentCocycleDefect_of_compatible _ M φ hM hφ
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_unit_killing_square_tripleFibreCocycle_mulTwo K A hA hf D (GlobalTheory.T.descentCocycleDefect_isTripleCocycle _ _ _ M hM φ D hD)
  obtain ⟨M₂, ψ, hM₂, e, hc, hco⟩ := GlobalTheory.T.exists_squareBundle_descent_of_defect_killed _ _ _ M hM φ D u hφ hD hu
  obtain ⟨L, hL, e'⟩ := GlobalTheory.T.exists_lineBundle_descent_finiteFlat _ _ ((𝟙 A) ^ 2 : A ⟶ A).left M₂ hM₂ ψ hc hco
  have hP : (lbPow M 2).IsLB := LB.isLB_linComb hM _ _
  exact ⟨L, hL, (cls_eq_iff hP (pull_isLB hL _)).1
    (((cls_eq_iff hP hM₂).2 e).trans ((cls_eq_iff hM₂ (pull_isLB hL _)).2 e'))⟩

theorem ev_symm {S : Scheme.{0}} {A : Over S} {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (hs : LBIso P (P.pull (lift (snd A A) (fst A A)).left)) (T : Over S) (x y : T ⟶ A) :
    ev (cls P hP) x y = ev (cls P hP) y x := by
  have e : cls P hP = ev (cls P hP) (snd A A) (fst A A) := (cls_eq_iff hP (pull_isLB hP _)).2 hs
  calc ev (cls P hP) x y = pull (lift x y).left (ev (cls P hP) (snd A A) (fst A A)) := by rw [← e]; rfl
    _ = ev (cls P hP) y x := by rw [pull_ev, lift_fst, lift_snd]

theorem exists_ample_root {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {P : LB (G2 A).left} (hP : P.IsLB)
    (r₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (r₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (hs : LBIso P (P.pull (lift (snd A A) (fst A A)).left)) (ha : RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)) :
    ∃ L : LB A.left, L.IsLB ∧ LBIso (abelian₂ A L) P ∧ RelAmple A L := by
  have hLaws : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  have hM : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have bP : Biadd (cls P hP) := biadd_of_axes hLaws.globalFns hA _ hM ha _ hP r₁ r₂
  have sy := ev_symm hP hs
  set p := cls P hP with hp
  have hm : ∀ (T : Over (Sp K)) (x : T ⟶ A), pull x.left (cls _ hM) = ev p x x := fun T x =>
    (pull_ev x p (𝟙 A) (𝟙 A)).trans (by rw [Category.comp_id])
  have h1 : ∀ (T : Over (Sp K)) (y : T ⟶ A), ev p 1 y = 0 := fun T y => by
    have := (bP T 1 1 y).1
    rw [_root_.mul_one] at this
    exact left_eq_add.1 this
  have hψ : ∀ {T : Over (Sp K)} (x : T ⟶ A), x ≫ ((𝟙 A) ^ 2 : A ⟶ A) = x * x := fun x => by
    rw [MonObj.comp_pow, Category.comp_id, pow_two]

  have hker : ∀ (T : Over (Sp K)) (t : T ⟶ A), t * t = 1 → ev p t t = 0 := by
    intro T t ht
    have hf := GlobalTheory.MulFinite.isFinite_mul K A hA 2 (by norm_num)
    let N := pullback ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left
    have hfin : IsFinite (pullback.snd ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left) := inferInstance
    haveI : IsAffine (𝟙_ (Over (Sp K))).left := inferInstanceAs (IsAffine (Sp K))
    have haff : IsAffine N := isAffine_of_isAffineHom (pullback.snd ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left)
    haveI : IsAffine (𝟙_ (Over (Sp K))).left := inferInstanceAs (IsAffine (Sp K))
    have hN : Finite N := by
      haveI : IsFinite (𝟙_ (Over (Sp K))).hom := inferInstanceAs (IsFinite (𝟙 (Sp K)))
      have hq := ((pullback.snd ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left) ≫ (𝟙_ (Over (Sp K))).hom).finite_preimage_singleton
        (⊥ : PrimeSpectrum K)
      exact Set.finite_univ_iff.1 (hq.subset fun x _ => Subsingleton.elim _ _)
    have w : t.left ≫ ((𝟙 A) ^ 2 : A ⟶ A).left = T.hom ≫ (η[A]).left := by
      rw [← Over.comp_left, hψ, ht]; rfl
    have z : pull (pullback.fst ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left) (cls _ hM) = 0 :=
      (cls_eq_zero_iff (pull_isLB hM _)).2 (GlobalTheory.exists_isGen_of_finite (pull_isLB hM _))
    rw [← hm, ← pullback.lift_fst t.left T.hom w, pull_comp, z, map_zero]
  obtain ⟨L, hL, e⟩ := exists_descent_two A hA hM (by
    let f := ((𝟙 A) ^ 2 : A ⟶ A).left
    let T : Over (Sp K) := Over.mk (pullback.fst f f ≫ A.hom)
    let x : T ⟶ A := Over.homMk (pullback.fst f f) rfl
    let y : T ⟶ A := Over.homMk (pullback.snd f f) (by
      show pullback.snd f f ≫ A.hom = pullback.fst f f ≫ A.hom
      rw [← Over.w ((𝟙 A) ^ 2 : A ⟶ A), ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ A.hom) pullback.condition.symm)
    have exy : x * x = y * y := by
      rw [← hψ, ← hψ]
      exact Over.OverMorphism.ext pullback.condition
    have ht : (x⁻¹ * y) * (x⁻¹ * y) = 1 := by
      rw [_root_.mul_mul_mul_comm, ← exy, ← mul_inv, inv_mul_cancel]
    refine (cls_eq_iff (pull_isLB hM _) (pull_isLB hM _)).1 ((hm T x).trans (Eq.trans ?_ (hm T y).symm))
    have ey : y = x * (x⁻¹ * y) := by rw [mul_inv_cancel_left]
    generalize x⁻¹ * y = t at ht ey
    have h2 : ev p t x + ev p t x = 0 := by rw [← (bP T t t x).1, ht, h1]
    rw [ey, (bP T _ _ _).1, (bP T _ _ _).2, (bP T _ _ _).2, hker T t ht, sy T x t, add_zero, add_assoc, h2, add_zero])
  have hΛ := GlobalTheory.SymBiextHalf.lam_iso hLaws hA hM ha hP bP sy hL e
  refine ⟨L, hL, hΛ, ?_⟩
  have hLam : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hPow : (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) 2).IsLB := LB.isLB_linComb hM _ _
  have hL2 : (lbPow L 2).IsLB := LB.isLB_linComb hL _ _
  have c₁ : p = lam (cls L hL) (fst A A) (snd A A) :=
    ((cls_eq_iff hLam hP).2 hΛ).symm.trans (cls_cube_two hL _ _ hLam)
  have c₂ : 2 • cls _ hM = pull ((𝟙 A) ^ 2 : A ⟶ A).left (cls L hL) :=
    (cls_lbPow hM 2 hPow).symm.trans ((cls_eq_iff hPow (pull_isLB hL _)).2 e)
  have c₃ : cls _ hM = lam (cls L hL) (𝟙 A) (𝟙 A) := by
    have := hm A (𝟙 A)
    rw [Over.id_left, pull_id] at this
    rw [this, ev, c₁, pull_lam, lift_fst, lift_snd]
  have c₄ : pull (1 : A ⟶ A).left (cls L hL) = 0 := by
    have z : pull (η[A]).left (cls L hL) = 0 :=
      (cls_eq_zero_iff (pull_isLB hL _)).2 (GlobalTheory.LB.exists_isGen_of_isLocalRing (R := K) (pull_isLB hL _))
    show pull (toUnit A ≫ η[A]).left _ = 0
    rw [Over.comp_left, pull_comp, z, map_zero]
  have c₅ : cls _ hL2 = cls _ hM := by
    rw [cls_lbPow hL 2 hL2]
    rw [lam, c₄, ← pow_two, ← c₂, Over.id_left, pull_id] at c₃
    linear_combination (norm := abel) c₃
  have := hA.proper
  rw [relAmple_iff_isAmpleLB_of_isAffine A hL, ← isAmpleLB_pow_iff hL (k := 2) (by norm_num),
    isAmpleLB_congr hL2 hM ((cls_eq_iff hL2 hM).1 c₅), ← relAmple_iff_isAmpleLB_of_isAffine A hM]
  exact ha

section Siegel

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ)

theorem root_of_siegPB {S' : Scheme.{0}} {s' : S' ⟶ Sp o} (c : SiegPre g n ζ s') (x : S' ⟶ F.X)
    (h : SiegPB c F.univ x) (L : LB c.A.left) (hL : L.IsLB) (e : LBIso (abelian₂ c.A L) c.P) :
    Root F.univ.A F.univ.P x := by
  obtain ⟨φ, φ₂, pb, sq, iso, -⟩ := h
  have hΛ : (abelian₂ c.A L).IsLB := LB.isLB_linComb hL _ _
  exact ⟨c.A, inferInstance, inferInstance, φ, φ₂, pb, sq, L, hL,
    LBIso.trans hΛ c.isLB (pull_isLB F.univ.isLB _) e iso⟩

theorem root_geom (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ F.X) : Root F.univ.A F.univ.P x := by
  obtain ⟨⟨c, hc⟩, hpr⟩ := GlobalTheory.siegPre_pullback g n o ζ F.X (Sp K) F.s (x ≫ F.s) x F.univ rfl
  have hcp := hpr c hc F.princ
  obtain ⟨L, hL, e, -⟩ := exists_ample_root c.A c.ab c.isLB c.rig₁ c.rig₂ c.symm hcp.1
  exact root_of_siegPB F c x hc L hL e

end Siegel

end GlobalTheory.PolBundleLoc
end
end
