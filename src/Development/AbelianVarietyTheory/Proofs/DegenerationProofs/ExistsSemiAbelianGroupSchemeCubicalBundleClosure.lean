import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLawOfHasTestsOfIndep
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitChartsTorusExtensionOverField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightedProjectiveChartsSplitGenericPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDenseClosedPointsChartSplitting
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfSplitAll
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoExtendOfNormalBaseStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BaseChangeTestOfSurjectiveMulAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormsOfTests
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointLiftingResiduePoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyThetaExtensionTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleOfNormOneGenerators
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RegularOfBoundedAtPadicAlgClPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective

section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.FewAtTest

open GlobalTheory.CechPic

theorem pic_eq_zero_of_generic {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {H : Scheme.{0}}
    (p : H ⟶ Sp V) (e : Sp V ⟶ H) (hs : Smooth p) (hi : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (c : Pic H)
    (h₁ : pull (pullback.fst p (Out.jK V)) c = 0) (h₂ : pull e c = 0) : c = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  let eK : Sp (FractionRing V) ⟶ pullback p (Out.jK V) := pullback.lift (Out.jK V ≫ e) (𝟙 _) (by
    rw [Category.assoc, he, Category.id_comp]; exact Category.comp_id _)
  have heK : eK ≫ pullback.fst p (Out.jK V) = Out.jK V ≫ e := pullback.lift_fst _ _ _
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (pull_isLB hM (pullback.fst p (Out.jK V) ≫ 𝟙 H))).1 (by
    rw [cls_pull hM, pull_comp, pull_id, h₁])
  obtain ⟨ρ, hρ⟩ := (cls_eq_zero_iff (pull_isLB hM (e ≫ 𝟙 H))).1 (by
    rw [cls_pull hM, pull_comp, pull_id, h₂])
  obtain ⟨u, hu, cu⟩ := DVR.exists_normalized_to hM _ _ t ht (pullback.snd p (Out.jK V)) eK
    (pullback.lift_snd _ _ _) _ _ (LB.pullGen M _ _ ρ (Out.jK V)) (DVR.pullGen_isGen _ _ _ _ hρ _) (by
      congr 1
      funext k
      rw [← Category.assoc, heK, Category.assoc])
  obtain ⟨s, ⟨hs₁, -⟩, -⟩ := GenExtend.existsUnique_gen_extend V (FractionRing V) H H p e hs hi he eK heK M hM
    PUnit (fun _ => 𝟙 H) (fun _ => 1) u ρ hu hρ cu
  have := (cls_eq_zero_iff (pull_isLB hM (𝟙 H))).2 ⟨s, hs₁⟩
  rwa [cls_pull hM, pull_id] at this

theorem lbIso_of_generic {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {G : Over (Sp V)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (L M : RigLB G)
    (h : LBIso (L.L.pull (pullback.fst G.hom (Out.jK V))) (M.L.pull (pullback.fst G.hom (Out.jK V)))) :
    LBIso L.L M.L := by
  refine (cls_eq_iff L.isLB M.isLB).1 (sub_eq_zero.1 (pic_eq_zero_of_generic G.hom (eSec G) hG.smooth
    (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hG.smooth hG.geomConnected)
    (Over.w η[G]) _ ?_ ?_))
  · rw [map_sub, sub_eq_zero]
    exact (cls_eq_iff (pull_isLB L.isLB _) (pull_isLB M.isLB _)).2 h
  · have a := (cls_eq_zero_iff (pull_isLB L.isLB (eSec G))).2 ⟨L.rig, L.rigGen⟩
    have b := (cls_eq_zero_iff (pull_isLB M.isLB (eSec G))).2 ⟨M.rig, M.rigGen⟩
    rw [cls_pull L.isLB] at a
    rw [cls_pull M.isLB] at b
    exact (map_sub _ _ _).trans (sub_eq_zero.2 (a.trans b.symm))

theorem natCast_ne_zero_of_isUnit {Z : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ Z) {n : ℕ}
    (h : IsUnit (n : Γ(Z, ⊤))) : (n : K) ≠ 0 := by
  have := (h.map x.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
  rw [map_natCast, map_natCast] at this
  exact this.ne_zero

theorem range_rPt {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsLocalRing V] (j : V →+* OO p) [IsLocalHom j] :
    Set.range (rPt p ≫ spMap j : Sp (kb p) ⟶ Sp V) = {IsLocalRing.closedPoint V} := by
  have key : ∀ x : Sp (kb p), (rPt p ≫ spMap j : Sp (kb p) ⟶ Sp V) x = IsLocalRing.closedPoint V := fun x => by
    have hx : x = IsLocalRing.closedPoint (kb p) := Subsingleton.elim (α := PrimeSpectrum (kb p)) _ _
    subst hx
    exact (congrArg (PrimeSpectrum.comap j) (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans
      (IsLocalRing.comap_closedPoint j)
  ext x
  exact ⟨fun ⟨a, ha⟩ => ha ▸ key a, fun h => ⟨IsLocalRing.closedPoint (kb p), (key _).trans h.symm⟩⟩

end GlobalTheory.FewAtTest

namespace GlobalTheory.ZJ

open GlobalTheory.FewAtTest

theorem theta_few : GlobalTheory.ZH.ThmUSt → Out.Laws → Out.Laws2 → ∀ (C : Core) (T : C.Theta), Out.RelAmple C.A T.L.L → Out.KTriv C.A T.L.L → T.L.IsSymmetric → GlobalTheory.ZH.HypS C.A T.L.L → ∀ N n : ℕ, 4 ≤ N → IsUnit (n : Γ(C.Z, ⊤)) → 6 * (N ^ C.g * C.g.factorial) < n ^ 2 → T.Few n := by
  intro hU laws laws₂ C T hA hK hs hS N n hN hn hlt p _ y τ E c
  obtain ⟨-, h0, hG⟩ := (core_basic C).2.2.2.2.2.2.2.2.2.2.2.2 p y τ
  have hL := pull_isLB T.L.isLB τ.φ
  have hi := PolBaseChange.lbIso_refl hL
  obtain ⟨hab, hamp, hkt⟩ := pol_pull _ _ C.A ((Over.pullback (Out.jK τ.V)).obj τ.H) τ.yK τ.φ T.L.L (T.L.L.pull τ.φ)
    T.L.isLB hL C.ab τ.φ_cart hi
  let A : Out.PolAV (Sp (FractionRing τ.V)) :=
    { A := (Over.pullback (Out.jK τ.V)).obj τ.H
      isAb := hab
      g := C.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback τ.φ_cart.1 C.dim
      L := T.L.L.pull τ.φ
      isLB := hL
      rigid := PolBaseChange.rigidified_pull τ.φ_cart ⟨T.L.rig, T.L.rigGen⟩
      sym := PolBaseChange.sym_pull τ.φ_cart (CechPic.sym_of_isSymmetric T.L hs)
      ample := hamp hA
      ktriv := hkt hK }
  have := hab.comm
  have hS' := SymBaseChange.hypS_baseChange _ _ C.A ((Over.pullback (Out.jK τ.V)).obj τ.H) τ.yK τ.φ T.L.L
    (T.L.L.pull τ.φ) T.L.isLB hL τ.φ_cart hi hS
  obtain ⟨D, U, hgen⟩ := hU τ.V τ.complete A τ.H hG τ.split hS' (Iso.refl _)
    (inferInstanceAs (IsMonHom (𝟙 ((Over.pullback (Out.jK τ.V)).obj τ.H))))
  have e₁ : LBIso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))) := U.ext
  rw [hgen] at e₁
  have e₂ : LBIso (E.L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))) (A.L.pull (𝟙 _)) :=
    LBIso.trans (pull_isLB E.L.isLB _) hL (pull_isLB hL _) (LBIso.symm ⟨E.w, E.w_gen⟩)
      (CechPic.iso_of_chart hL (Geo.Tor.chartPullPull _ _ _ rfl)).symm
  have e := lbIso_of_generic hG E.L U.LG
    (LBIso.trans (pull_isLB E.L.isLB _) (pull_isLB hL _) (pull_isLB U.LG.isLB _) e₂ e₁)
  have := isAlgClosed_kb (p := p)
  have := τ.j_loc
  exact GlobalTheory.FewZeros.card_torsion_translate_zeros_lt laws laws₂ τ.V τ.complete D A τ.H U E.L.L E.θ E.L.isLB e E.θ_ne (kb p) (rPt p ≫ spMap τ.j) N n
    (range_rPt τ.j) hN (natCast_ne_zero_of_isUnit (rPt p ≫ y) hn) hlt c

end GlobalTheory.ZJ
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.FibreSplit

theorem exists_residue_factor {K : Type} [Field K] {Z : Scheme.{0}} (s : Sp K ⟶ Z) [SurjectiveOnStalks s]
    (z : Z) (hz : s (IsLocalRing.closedPoint K) = z) :
    ∃ f : Sp (Z.residueField z) ⟶ Sp K, f ≫ s = Z.fromSpecResidueField z := by
  subst hz
  let ρ := Z.descResidueField (Scheme.stalkClosedPointTo s)
  have hs : Function.Surjective (Scheme.stalkClosedPointTo s).hom := by
    unfold Scheme.stalkClosedPointTo
    exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of K)).hom).2.comp (s.stalkMap_surjective _)
  have hρ : Function.Surjective ρ.hom := by
    have h := congrArg CommRingCat.Hom.hom (Z.residue_descResidueField (Scheme.stalkClosedPointTo s))
    rw [← h] at hs
    rw [CommRingCat.hom_comp, RingHom.coe_comp] at hs
    exact Function.Surjective.of_comp hs
  have : IsIso ρ := (ConcreteCategory.isIso_iff_bijective ρ).2 ⟨ρ.hom.injective, hρ⟩
  refine ⟨inv (Spec.map ρ), ?_⟩
  rw [IsIso.inv_comp_eq]
  exact (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z s).symm

theorem exists_splitExt_of_split (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom]
    [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (h : C.Split c) :
    ∃ E : SplitExt (Sp K), E.IsGt H := by
  obtain ⟨hc, i, hT⟩ := h
  obtain ⟨B, gB, q, hB, hq, hf, hs, ha, hk, -⟩ := GlobalTheory.T.splitCharts_torus_extension_over_field K H C d c i hc hT
  exact GlobalTheory.exists_splitExt_isGt_of_torusExtension K H ⟨{
    X := Fin d → ℤ, B := B, grpB := gB, isAbelian := hB, i := i, q := q, i_hom := hT.hom, q_hom := hq,
    q_flat := hf, q_surjective := hs, q_quasiCompact := inferInstance, isKernel := hk }⟩

theorem splitAll_and_isSemiAbelian : ∀ (C : Core) (L : C.Law), C.HasTests → C.HasCharts → letI := L.grp; letI := L.comm; SplitAll C.GG ∧ IsSemiAbelian C.GG := by
  intro C L hT hC
  let := L.grp
  let := L.comm
  obtain ⟨hsep, -, hqc, -⟩ := core_basic C
  have := L.smooth
  have hsm : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have h : SplitAll C.GG := by
    intro z
    obtain ⟨R, _, _, _, t, _, ht, Ch, d, c, Sg, hd, hS, -⟩ := DenseSplit.exists_dense_splitOn C L hT hC z
    have : Smooth ((Over.pullback t).obj C.GG).hom := inferInstanceAs (Smooth (pullback.snd C.GG.hom t))
    have : IsSeparated ((Over.pullback t).obj C.GG).hom := inferInstanceAs (IsSeparated (pullback.snd C.GG.hom t))
    have : QuasiCompact ((Over.pullback t).obj C.GG).hom := inferInstanceAs (QuasiCompact (pullback.snd C.GG.hom t))
    have : Smooth ((Over.pullback (Out.jK R)).obj ((Over.pullback t).obj C.GG)).hom :=
      inferInstanceAs (Smooth (pullback.snd ((Over.pullback t).obj C.GG).hom _))
    have : IsSeparated ((Over.pullback (Out.jK R)).obj ((Over.pullback t).obj C.GG)).hom :=
      inferInstanceAs (IsSeparated (pullback.snd ((Over.pullback t).obj C.GG).hom _))
    have : QuasiCompact ((Over.pullback (Out.jK R)).obj ((Over.pullback t).obj C.GG)).hom :=
      inferInstanceAs (QuasiCompact (pullback.snd ((Over.pullback t).obj C.GG).hom _))
    have : IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom (Out.jK R)) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
    obtain ⟨E, hE⟩ := exists_splitExt_of_split (FractionRing R) _ _ d _
      (GlobalTheory.T.weightedProjectiveCharts_split_generic_point R ((Over.pullback t).obj C.GG) Ch d c Sg hd hS)
    have : IsPreimmersion (Out.jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
    obtain ⟨f, hf⟩ := exists_residue_factor (Out.jK R ≫ t) z (by
      rw [← ht]
      refine (Scheme.Hom.comp_apply (Out.jK R) t _).trans (congrArg t (PrimeSpectrum.ext ?_))
      change Ideal.comap (algebraMap R (FractionRing R)) (IsLocalRing.maximalIdeal _) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)])
    have : IsMonHom (pullCompIso (Out.jK R) t C.GG).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso (Out.jK R) t C.GG).inv)
    obtain ⟨D⟩ := isGt_of_iso (pullCompIso (Out.jK R) t C.GG).symm hE
    have : IsMonHom (pullCompIso f (Out.jK R ≫ t) C.GG).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso f (Out.jK R ≫ t) C.GG).inv)
    have key : ∀ s : Sp (C.Z.residueField z) ⟶ C.Z, f ≫ Out.jK R ≫ t = s →
        ∃ E : SplitExt (Sp (C.Z.residueField z)), E.IsGt ((Over.pullback s).obj C.GG) := by
      rintro _ rfl
      exact ⟨_, isGt_of_iso (pullCompIso f (Out.jK R ≫ t) C.GG).symm (GtBaseChange.isGt_extBC f E _ D)⟩
    exact key _ hf
  exact ⟨h, (isSemiAbelian_of_splitAll C.Z C.GG h).1⟩

end GlobalTheory.ZJ.FibreSplit
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem etale_mulN_and_isOpen_om (C : Core) (L : C.Law) (T : C.Theta) :
    letI := L.grp; Etale (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m).left ∧ IsOpen (T.Om L) := by
  letI := L.grp
  letI := L.comm
  have := L.smooth
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have h : Etale (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m).left := GlobalTheory.GrpTangent.etale_mulN C.GG T.m_unit
  exact ⟨h, (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m).left.isOpenMap _ (Out.nonzeroLocus T.s).isOpen⟩

theorem etale_mulN_and_isOpen_om_of_isSemiAbelian : ∀ (C : Core) (L : C.Law) (T : C.Theta), letI := L.grp; letI := L.comm; IsSemiAbelian C.GG → Out.MulNSt → Etale (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m).left ∧ IsOpen (T.Om L) :=
  fun C L T _ _ => etale_mulN_and_isOpen_om C L T

end GlobalTheory.ZJ
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChangeTest_of_surjective_mul_abelianVariety : (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : K) ≠ 0 → Surjective (mulN B n).left) → ∀ (C : Core) (L : C.Law) (T : C.Theta), T.BTest L := by
  first | exact @GlobalTheory.ZJ.bTest_of_surjective_mulN | exact GlobalTheory.ZJ.bTest_of_surjective_mulN | (intros; apply GlobalTheory.ZJ.bTest_of_surjective_mulN <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.nonempty_thetaExtension_test : Semi.extend_existsSt.{0} → ∀ (C : Core) (T : C.Theta) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.TestCart → Nonempty (T.Ext τ) := by
  first | exact @GlobalTheory.ZJ.Core.Theta.nonempty_ext | exact GlobalTheory.ZJ.Core.Theta.nonempty_ext | (intros; apply GlobalTheory.ZJ.Core.Theta.nonempty_ext <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_notMem_of_ncard_lt_card {H : Type} [Finite H] (S : Set H)
    (h : S.ncard < Nat.card H) : ∃ x : H, x ∉ S := by
  by_contra hx
  have hS : S = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    by_contra hx'
    exact hx ⟨x, hx'⟩
  rw [hS, Set.ncard_univ] at h
  exact lt_irrefl _ h

theorem exists_pair_avoiding_small_sets :
    ∀ (H : Type) [CommGroup H] [Finite H] (B₀ B₁ : Set H), 6 * Nat.card B₀ < Nat.card H →
      6 * Nat.card B₁ < Nat.card H →
      ∃ b c : H, b ∉ B₀ ∧ c ∉ B₀ ∧ b * c ∉ B₀ ∧ b ∉ B₁ ∧ c ∉ B₁ ∧ b * c ∉ B₁ := by
  intro H _ _ B₀ B₁ h₀ h₁
  rw [Nat.card_coe_set_eq] at h₀ h₁
  have hS : (B₀ ∪ B₁).ncard ≤ B₀.ncard + B₁.ncard := Set.ncard_union_le _ _
  obtain ⟨b, hb⟩ := exists_notMem_of_ncard_lt_card (B₀ ∪ B₁) (by omega)
  have hT : ((fun x => b⁻¹ * x) '' (B₀ ∪ B₁)).ncard ≤ (B₀ ∪ B₁).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  have hU : ((B₀ ∪ B₁) ∪ (fun x => b⁻¹ * x) '' (B₀ ∪ B₁)).ncard ≤
      (B₀ ∪ B₁).ncard + ((fun x => b⁻¹ * x) '' (B₀ ∪ B₁)).ncard := Set.ncard_union_le _ _
  obtain ⟨c, hc⟩ := exists_notMem_of_ncard_lt_card
    ((B₀ ∪ B₁) ∪ (fun x => b⁻¹ * x) '' (B₀ ∪ B₁)) (by omega)
  have hbc : b * c ∉ B₀ ∪ B₁ := fun h => hc (Or.inr ⟨b * c, h, by simp⟩)
  exact ⟨b, c, fun h => hb (Or.inl h), fun h => hc (Or.inl (Or.inl h)), fun h => hbc (Or.inl h),
    fun h => hb (Or.inr h), fun h => hc (Or.inl (Or.inr h)), fun h => hbc (Or.inr h)⟩

end GlobalTheory
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.TwoSections

theorem exists_torsion_pair (M : Type) [CommGroup M] (P : M → Prop) (n : ℕ) (x : M)
    (h : ∀ c : M, 6 * Nat.card {h : M // h ^ n = 1 ∧ ¬ P (c * h)} < Nat.card {h : M // h ^ n = 1}) :
    ∃ b c : M, b ^ n = 1 ∧ c ^ n = 1 ∧ P b ∧ P c ∧ P (b * c) ∧ P (x * b) ∧ P (x * c) ∧ P (x * b * c) := by
  let H : Subgroup M := (powMonoidHom n : M →* M).ker
  have hH : Nat.card H = Nat.card {h : M // h ^ n = 1} := rfl
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by have := h 1; omega)
  have hB : ∀ c : M, 6 * Nat.card {h : H | ¬ P (c * h)} < Nat.card H := fun c => by
    have e : {h : H | ¬ P (c * h)} ≃ {h : M // h ^ n = 1 ∧ ¬ P (c * h)} :=
      Equiv.subtypeSubtypeEquivSubtypeInter (fun h : M => h ^ n = 1) (fun h => ¬ P (c * h))
    rw [Nat.card_congr e, hH]
    exact h c
  obtain ⟨b, c, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.exists_pair_avoiding_small_sets H _ _ (hB 1) (hB x)
  simp only [Set.mem_ofPred_eq, not_not, _root_.one_mul, Subgroup.coe_mul] at h1 h2 h3 h4 h5 h6
  exact ⟨b, c, b.2, c.2, h1, h2, h3, h4, h5, by rwa [_root_.mul_assoc]⟩

theorem exists_pushHom {S S' X : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (q : X ⟶ S') (s : X ⟶ S) (e : q ≫ f = s) :
    ∃ ρ : (Over.mk q ⟶ G') →* (Over.mk s ⟶ G), ∀ c, (ρ c).left = c.left ≫ φ := by
  subst e
  exact ⟨pushHom h (Over.mk q), fun _ => rfl⟩

theorem exists_residue_point (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (w : X)
    (hw : IsClosed ({w} : Set X)) : ∃ (p : ℕ) (_ : Fact p.Prime) (x : Sp (kb p) ⟶ X), ∀ s, x s = w := by
  have := (GlobalTheory.jacobson_closedPoints_tools_int X π).2.1 w hw
  obtain ⟨p, hp⟩ := CharP.exists (X.residueField w)
  have hpp : Fact p.Prime := ⟨CharP.char_is_prime (X.residueField w) p⟩
  have : CharP (kb p) p := charP_kb
  have : IsAlgClosed (kb p) := isAlgClosed_kb
  letI : Algebra (ZMod p) (X.residueField w) := ZMod.algebra _ p
  letI : Algebra (ZMod p) (kb p) := ZMod.algebra _ p
  have : Module.Finite (ZMod p) (X.residueField w) := Module.Finite.of_finite
  let r : X.residueField w →+* kb p := (IsAlgClosed.lift (R := ZMod p) (S := X.residueField w) (M := kb p)).toRingHom
  refine ⟨p, hpp, Spec.map (CommRingCat.ofHom r) ≫ X.fromSpecResidueField w, fun s => ?_⟩
  have : (Spec.map (CommRingCat.ofHom r) ≫ X.fromSpecResidueField w) s ∈ Set.range (X.fromSpecResidueField w) :=
    ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rwa [Scheme.range_fromSpecResidueField] at this

end GlobalTheory.ZJ.TwoSections

namespace GlobalTheory.ZJ
open TwoSections

theorem Core.Law.six_of_few : Semi.extend_existsSt.{0} → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), C.HasTests → T.BTest L → C.TorsSec n → T.Few n → L.CompanionTheory (T.Om L) := by
  intro hext C L T n hT hB hS hF w hw
  letI := L.grp
  letI := L.comm
  have := C.lft
  have := C.flat
  have hlft : LocallyOfFiniteType C.GG.hom := (GlobalTheory.ZJ.core_basic C).2.1
  have hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π) := inferInstance
  obtain ⟨p, hp, x, hx⟩ := @exists_residue_point C.G.toScheme (C.GG.hom ≫ C.π) hlft' w hw
  obtain ⟨hlift, hcl⟩ := GlobalTheory.exists_integral_point_lifting_residue_point C.Z C.π C.U C.ne p
  obtain ⟨y, hy, hyU⟩ := hlift (x ≫ C.GG.hom)
  obtain ⟨τ⟩ := hT p y hyU
  obtain ⟨E⟩ := GlobalTheory.T.nonempty_thetaExtension_test hext C T p y τ fun p _ y τ => (L.test p y τ).1
  let s₀ : Sp (kb p) := IsLocalRing.closedPoint (kb p)
  have hs : ∀ s : Sp (kb p), s = s₀ := fun s => Subsingleton.elim (α := PrimeSpectrum (kb p)) _ _
  have hr : rPt p s₀ = cPt p := IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
  have hz : y (cPt p) = (x ≫ C.GG.hom) s₀ := by rw [← hy, Scheme.Hom.comp_apply, hr]
  obtain ⟨N, hN, hsec⟩ := hS _ (hcl (x ≫ C.GG.hom) s₀)
  have hrange : Set.range (x ≫ C.GG.hom) ⊆ Set.range N.ι := by
    rintro _ ⟨s, rfl⟩
    rw [hs s, Scheme.Opens.range_ι]
    exact hN
  let t : Sp (kb p) ⟶ N.toScheme := IsOpenImmersion.lift N.ι (x ≫ C.GG.hom) hrange
  have ht : t ≫ N.ι = x ≫ C.GG.hom := IsOpenImmersion.lift_fac _ _ _
  have e : (rPt p ≫ spMap τ.j) ≫ τ.y₀ = t ≫ N.ι := by rw [Category.assoc, τ.fac, hy, ht]
  have hpb := (L.test p y τ).1
  let c₀ : Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H :=
    Over.homMk (hpb.lift x (rPt p ≫ spMap τ.j) (ht.symm.trans e.symm)) (hpb.lift_snd _ _ _)
  have hc₀ : c₀.left ≫ τ.f = x := hpb.lift_fst _ _ _
  obtain ⟨ρ, hρ⟩ := exists_pushHom (L.test p y τ) _ _ e
  obtain ⟨b, c, hb, hc, h1, h2, h3, h4, h5, h6⟩ := exists_torsion_pair (Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H)
    (fun c => ⊤ ≤ c.left ⁻¹ᵁ Out.nonzeroLocus E.θ) n c₀ (hF p y τ E)
  obtain ⟨b₁, hb₁, hb₂⟩ := hsec p y τ t b hz (ht.trans hy.symm) hb
  obtain ⟨c₁, hc₁, hc₂⟩ := hsec p y τ t c hz (ht.trans hy.symm) hc
  have key : ∀ d : Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H, ⊤ ≤ d.left ⁻¹ᵁ Out.nonzeroLocus E.θ →
      Set.range (ρ d).left ⊆ T.Om L := by
    rintro d hd _ ⟨s, rfl⟩
    have := τ.j_loc
    have h0 : τ.H.hom (d.left s) = IsLocalRing.closedPoint τ.V := by
      rw [← Scheme.Hom.comp_apply, Over.w d, hs s]
      exact (Scheme.Hom.comp_apply _ _ _).trans
        ((congrArg (spMap τ.j) hr).trans (IsLocalRing.comap_closedPoint τ.j))
    rw [hρ]
    exact (Scheme.Hom.comp_apply _ _ _).symm ▸ (hB p y τ E _ h0).2 (hd trivial)
  refine ⟨N, Over.homMk b₁ hb₁, Over.homMk c₁ hc₁, kb p, inferInstance, t, ρ c₀, ρ b, ρ c, ?_,
    (hρ b).trans hb₂.symm, (hρ c).trans hc₂.symm, ?_⟩
  · rw [hρ, hc₀]
    ext v
    exact ⟨fun ⟨s, h⟩ => h ▸ hx s, fun h => ⟨s₀, (hx _).trans h.symm⟩⟩
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false, ← map_mul] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [key _ h1, key _ h2, key _ h3, key _ h4, key _ h5, key _ h6]

end GlobalTheory.ZJ
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.companionTheory_om_of_tests_torsionSections : Semi.extend_existsSt.{0} → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), C.HasTests → T.BTest L → C.TorsSec n → T.Few n → L.CompanionTheory (T.Om L) := by
  atlas_forward_decl GlobalTheory.ZJ.Core.Law.six_of_few
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory
namespace ThetaLocal
open NormGlue

theorem isUnit_gs_iff_mem {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    IsUnit (gs f y U a) ↔ f y ∈ X.basicOpen a := by
  rw [gs_eq f y U h, ← Scheme.mem_basicOpen Y _ y h, ← Scheme.preimage_basicOpen]
  rfl

theorem fn_eq_of_generic {X : Scheme.{0}} [IsIntegral X] (ξ : X)
    (hξ : ∀ O : X.Opens, (O : Set X).Nonempty → ξ ∈ O) {U : X.Opens} {a b : Γ(X, U)}
    (h : ξ ∈ U → gs (𝟙 X) ξ U a = gs (𝟙 X) ξ U b) : a = b := by
  by_cases hU : (U : Set X).Nonempty
  · have hm : ξ ∈ U := hξ _ hU
    have e := h hm
    rw [gs_eq _ ξ U hm, gs_eq _ ξ U hm] at e
    exact germ_injective_of_isIntegral X (U := U) ξ hm e
  · exact fn_ext fun x hx => (hU ⟨x, hx⟩).elim

theorem exists_push {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (V : Y.Opens) (u : Γ(Y, V)ˣ) :
    ∃ t : Γ(X, f ''ᵁ V)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ V → gm (r ≫ f) z _ t = gm r z V u := by
  have h : V ≤ f ⁻¹ᵁ (f ''ᵁ V) := (f.preimage_image_eq V).ge
  let t : Γ(X, f ''ᵁ V)ˣ := Units.map (f.appIso V).inv.hom.toMonoidHom u
  have e' : Semi.res h (pullU f _ t) = u := by
    apply Units.ext
    rw [val_res_pullU, ← Scheme.Hom.appIso_hom']
    exact Iso.inv_hom_id_apply _ _
  refine ⟨t, fun Z r z hz => ?_⟩
  rw [← e', gm_res r z h hz, gm_pull r f z _ (h hz)]

theorem exists_ratio {X G : Scheme.{0}} (p₁ p₂ : X ⟶ G) {E E' : G.Opens} (t : Γ(G, E)ˣ) (t' : Γ(G, E')ˣ)
    (V : X.Opens) (h₁ : V ≤ p₁ ⁻¹ᵁ E) (h₂ : V ≤ p₂ ⁻¹ᵁ E') :
    ∃ u : Γ(X, V)ˣ, (∀ (Y : Scheme.{0}) (r : Y ⟶ X) (y : Y), r y ∈ V →
      gm r y V u = gm (r ≫ p₁) y E t * (gm (r ≫ p₂) y E' t')⁻¹) ∧
      ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ X), Set.range x ⊆ V →
        ‖valF x V u.val‖ * ‖valF (x ≫ p₂) E' t'.val‖ = ‖valF (x ≫ p₁) E t.val‖ := by
  have k : ∀ (Y : Scheme.{0}) (r : Y ⟶ X) (y : Y), r y ∈ V →
      gm r y V (Semi.res h₁ (pullU p₁ E t) * (Semi.res h₂ (pullU p₂ E' t'))⁻¹) =
        gm (r ≫ p₁) y E t * (gm (r ≫ p₂) y E' t')⁻¹ := fun Y r y hy => by
    rw [map_mul, map_inv, gm_res r y h₁ hy, gm_res r y h₂ hy, gm_pull r p₁ y _ (h₁ hy), gm_pull r p₂ y _ (h₂ hy)]
  refine ⟨_, k, fun p _ x hx => ?_⟩
  let z : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  have hz := mem_of_range hx z
  rw [← norm_mul]
  congr 1
  apply (toStk z).injective
  rw [map_mul, toStk_valF x _ z hz, toStk_valF (x ≫ p₁) _ z (h₁ hz), toStk_valF (x ≫ p₂) _ z (h₂ hz), k _ x z hz,
    ← Units.val_mul, inv_mul_cancel_right]

theorem exists_local_section {G Z X : Scheme.{0}} (p₁ p₂ : X ⟶ G) [IsIntegral X] (π : X ⟶ Sp ℤ)
    [Flat π] [LocallyOfFiniteType π] (hX : Geo.Tor.IsNormalScheme X) (h : G ⟶ Z) (hp : IsPullback p₁ p₂ h h)
    (M : LB G) (E : M.ι → G.Opens) (hE : ∀ i, E i ≤ M.U i)
    (hne : ∀ i, (M.U i : Set G).Nonempty → (E i : Set G).Nonempty) (t : ∀ i, Γ(G, E i)ˣ)
    (ht : ∀ i k (Y : Scheme.{0}) (r : Y ⟶ G) (y : Y), r y ∈ E i → r y ∈ E k →
      gm r y _ (t i) = gm r y _ (M.g i k) * gm r y _ (t k))
    (Om : Set G) (hδ : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ Z), ∃ δ : ℝ, 0 < δ ∧
      ∀ (b : Sp (OO p) ⟶ G) (i : M.ι), (gPt p ≫ b) ≫ h = y → b (cPt p) ∈ M.U i → Set.range (gPt p ≫ b) ⊆ E i →
        ‖valF (gPt p ≫ b) _ (t i).val‖ ≤ δ ∧ (b (cPt p) ∈ Om → ‖valF (gPt p ≫ b) _ (t i).val‖ = δ))
    (W : G.Opens) (i₀ : M.ι) (hW : W ≤ M.U i₀) (hWO : (W : Set G) ⊆ Om) (hWne : (W : Set G).Nonempty)
    (N : Z.Opens) (b : N.toScheme ⟶ G) (hb : b ≫ h = N.ι) (hbW : ∀ z, b z ∈ W) :
    ∃ σ : LB.Sec (M.pull (h ⁻¹ᵁ N).ι), ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, h ((h ⁻¹ᵁ N).ι x) = z' := by
  obtain ⟨ξ, hξ⟩ := exists_generic X
  let Δ : G ⟶ X := hp.lift (𝟙 G) (𝟙 G) rfl
  have g₁ : ∀ O : G.Opens, (O : Set G).Nonempty → p₁ ξ ∈ O := fun O ⟨y, hy⟩ =>
    hξ (p₁ ⁻¹ᵁ O) ⟨Δ y, by
      change (Δ ≫ p₁) y ∈ O
      rw [hp.lift_fst]; exact hy⟩
  have g₂ : ∀ O : G.Opens, (O : Set G).Nonempty → p₂ ξ ∈ O := fun O ⟨y, hy⟩ =>
    hξ (p₂ ⁻¹ᵁ O) ⟨Δ y, by
      change (Δ ≫ p₂) y ∈ O
      rw [hp.lift_snd]; exact hy⟩
  have hW₁ := g₁ W hWne
  have hW₂ := g₂ W hWne
  have hE₂ := g₂ (E i₀) (hne _ ⟨_, hW hW₂⟩)
  have hE₁ : ∀ k, p₁ ξ ∈ M.U k → p₁ ξ ∈ E k := fun k hk => g₁ _ (hne _ ⟨_, hk⟩)
  have ll := GlobalTheory.regular_of_bounded_at_padicAlgCl_points.2 X π hX
  have nrm : ∀ k (V : X.Opens) (h₁ : V ≤ p₁ ⁻¹ᵁ E k) (h₂ : V ≤ p₂ ⁻¹ᵁ E i₀), ∃ u : Γ(X, V)ˣ,
      (ξ ∈ V → gm (𝟙 X) ξ V u = gm p₁ ξ _ (t k) * (gm p₂ ξ _ (t i₀))⁻¹) ∧
      ∀ (p : ℕ) [Fact p.Prime] (c : Sp (OO p) ⟶ X), p₁ (c (cPt p)) ∈ M.U k → p₂ (c (cPt p)) ∈ W →
        Set.range (gPt p ≫ c) ⊆ V → ‖valF (gPt p ≫ c) V u.val‖ ≤ 1 ∧
          (p₁ (c (cPt p)) ∈ W → ‖valF (gPt p ≫ c) V u.val‖ = 1) := by
    intro k V h₁ h₂
    obtain ⟨u, hu, hu'⟩ := exists_ratio p₁ p₂ (t k) (t i₀) V h₁ h₂
    refine ⟨u, fun hm => by simpa only [Category.id_comp] using hu _ (𝟙 X) ξ hm, fun p _ c c₁ c₂ hc => ?_⟩
    obtain ⟨δ, hδ₀, H⟩ := hδ p ((gPt p ≫ c ≫ p₁) ≫ h)
    have e := hu' p _ hc
    have a₁ := H (c ≫ p₁) k rfl c₁ (by rintro _ ⟨s, rfl⟩; exact h₁ (hc ⟨s, rfl⟩))
    have a₂ := (H (c ≫ p₂) i₀ (by simp only [Category.assoc, hp.w]) (hW c₂)
      (by rintro _ ⟨s, rfl⟩; exact h₂ (hc ⟨s, rfl⟩))).2 (hWO c₂)
    rw [Category.assoc, Category.assoc, a₂] at e
    refine ⟨?_, fun c₃ => ?_⟩
    · have := a₁.1
      rw [← e] at this
      exact le_of_mul_le_mul_right (by simpa using this) hδ₀
    · have := a₁.2 (hWO c₃)
      rw [← e] at this
      exact mul_right_cancel₀ hδ₀.ne' (by simpa using this)
  have key : ∀ k, ∃ f : Γ(X, p₁ ⁻¹ᵁ M.U k ⊓ p₂ ⁻¹ᵁ W), p₁ ξ ∈ M.U k →
      gs (𝟙 X) ξ _ f = (gm p₁ ξ _ (t k) * (gm p₂ ξ _ (t i₀))⁻¹).val := by
    intro k
    by_cases hk : p₁ ξ ∈ M.U k
    · have hm : ξ ∈ p₁ ⁻¹ᵁ E k ⊓ p₂ ⁻¹ᵁ E i₀ ⊓ p₂ ⁻¹ᵁ W := ⟨⟨hE₁ k hk, hE₂⟩, hW₂⟩
      obtain ⟨u, hu, hu'⟩ := nrm k (p₁ ⁻¹ᵁ E k ⊓ p₂ ⁻¹ᵁ E i₀ ⊓ p₂ ⁻¹ᵁ W) (inf_le_left.trans inf_le_left)
        (inf_le_left.trans inf_le_right)
      have le : p₁ ⁻¹ᵁ E k ⊓ p₂ ⁻¹ᵁ E i₀ ⊓ p₂ ⁻¹ᵁ W ≤ p₁ ⁻¹ᵁ M.U k ⊓ p₂ ⁻¹ᵁ W :=
        fun x hx => ⟨hE k hx.1.1, hx.2⟩
      obtain ⟨f, hf, -⟩ := (ll _ _ le u.val ⟨ξ, hm⟩).1 fun p _ c hc hr => (hu' p c hc.1 hc.2 hr).1
      refine ⟨f, fun _ => ?_⟩
      rw [← hu hm, ← gs_unit _ ξ _ hm, ← hf, gs_res _ ξ le hm]
    · exact ⟨0, fun hk' => (hk hk').elim⟩
  choose f hf using key
  have compat : ∀ k k' (Y : Scheme.{0}) (r : Y ⟶ X) (y : Y), p₁ (r y) ∈ M.U k → p₁ (r y) ∈ M.U k' → p₂ (r y) ∈ W →
      gs r y _ (f k) = (gm (r ≫ p₁) y _ (M.g k k')).val * gs r y _ (f k') := by
    intro k k'
    let O : X.Opens := p₁ ⁻¹ᵁ (M.U k ⊓ M.U k') ⊓ p₂ ⁻¹ᵁ W
    have l₁ : O ≤ p₁ ⁻¹ᵁ M.U k ⊓ p₂ ⁻¹ᵁ W := fun x hx => ⟨hx.1.1, hx.2⟩
    have l₂ : O ≤ p₁ ⁻¹ᵁ M.U k' ⊓ p₂ ⁻¹ᵁ W := fun x hx => ⟨hx.1.2, hx.2⟩
    have l₃ : O ≤ p₁ ⁻¹ᵁ (M.U k ⊓ M.U k') := inf_le_left
    have ev : ∀ (Y : Scheme.{0}) (r : Y ⟶ X) (y : Y), r y ∈ O →
        gs r y O (resG X l₁ (f k)) = gs r y _ (f k) ∧
        gs r y O ((Semi.res l₃ (pullU p₁ _ (M.g k k'))).val * resG X l₂ (f k')) =
          (gm (r ≫ p₁) y _ (M.g k k')).val * gs r y _ (f k') := fun Y r y hy =>
      ⟨gs_res r y l₁ hy _, by
        rw [gs_mul r y _ hy, gs_unit r y _ hy, gm_res r y l₃ hy, gm_pull r p₁ y _ (l₃ hy), gs_res r y l₂ hy]⟩
    have e : resG X l₁ (f k) = (Semi.res l₃ (pullU p₁ _ (M.g k k'))).val * resG X l₂ (f k') := by
      refine fn_eq_of_generic ξ hξ fun hm => ?_
      obtain ⟨e₁, e₂⟩ := ev _ (𝟙 X) ξ hm
      rw [e₁, e₂, hf k hm.1.1, hf k' hm.1.2, Category.id_comp, ht k k' _ p₁ ξ (hE₁ k hm.1.1) (hE₁ k' hm.1.2),
        ← Units.val_mul, _root_.mul_assoc]
    intro Y r y a₁ a₂ a₃
    obtain ⟨e₁, e₂⟩ := ev _ r y ⟨⟨a₁, a₂⟩, a₃⟩
    rw [← e₁, ← e₂, e]
  have unit : ∀ (Y : Scheme.{0}) (r : Y ⟶ X) (y : Y), p₁ (r y) ∈ W → p₂ (r y) ∈ W → IsUnit (gs r y _ (f i₀)) := by
    have hm : ξ ∈ p₁ ⁻¹ᵁ E i₀ ⊓ p₂ ⁻¹ᵁ E i₀ ⊓ (p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ W) := ⟨⟨hE₁ _ (hW hW₁), hE₂⟩, hW₁, hW₂⟩
    obtain ⟨u, hu, hu'⟩ := nrm i₀ (p₁ ⁻¹ᵁ E i₀ ⊓ p₂ ⁻¹ᵁ E i₀ ⊓ (p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ W)) (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right)
    obtain ⟨ψ, hψ, e⟩ := (ll _ _ inf_le_right u.val ⟨ξ, hm⟩).2 u.isUnit fun p _ c hc hr =>
      (hu' p c (hW hc.1) hc.2 hr).2 hc.1
    have le : p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ W ≤ p₁ ⁻¹ᵁ M.U i₀ ⊓ p₂ ⁻¹ᵁ W := fun x hx => ⟨hW hx.1, hx.2⟩
    have e' : resG X le (f i₀) = ψ := by
      refine fn_eq_of_generic ξ hξ fun hm' => ?_
      rw [gs_res _ ξ le hm', hf i₀ (hW hW₁), ← hu hm, ← gs_unit _ ξ _ hm, ← e, gs_res _ ξ inf_le_right hm]
    intro Y r y a₁ a₂
    have hy : r y ∈ p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ W := ⟨a₁, a₂⟩
    rw [← gs_res r y le hy, e', gs_eq r y _ hy]
    exact (hψ.map _).map _
  let q : (h ⁻¹ᵁ N).toScheme ⟶ X := hp.lift (h ⁻¹ᵁ N).ι (h ∣_ N ≫ b) (by rw [Category.assoc, hb, morphismRestrict_ι])
  have q₁ : q ≫ p₁ = (h ⁻¹ᵁ N).ι := hp.lift_fst _ _ _
  have q₂ : q ≫ p₂ = h ∣_ N ≫ b := hp.lift_snd _ _ _
  have r₁ : ∀ x, p₁ (q x) = (h ⁻¹ᵁ N).ι x := fun x => by rw [← q₁]; rfl
  have r₂ : ∀ x, p₂ (q x) = b ((h ∣_ N) x) := fun x => congrArg (fun s : (h ⁻¹ᵁ N).toScheme ⟶ G => s x) q₂
  have le : ∀ J, (M.pull (h ⁻¹ᵁ N).ι).U J ≤ q ⁻¹ᵁ (p₁ ⁻¹ᵁ M.U (J PUnit.unit) ⊓ p₂ ⁻¹ᵁ W) := fun J x hx =>
    ⟨show p₁ (q x) ∈ M.U _ from (r₁ x).symm ▸ mem_pull.1 hx, show p₂ (q x) ∈ W from (r₂ x).symm ▸ hbW _⟩
  have ev : ∀ J x, x ∈ (M.pull (h ⁻¹ᵁ N).ι).U J →
      gs (𝟙 _) x _ (resG _ (le J) ((q.app _).hom (f (J PUnit.unit)))) = gs q x _ (f (J PUnit.unit)) := fun J x hx => by
    rw [gs_res _ x (le J) hx, gs_pull _ q x _ (le J hx), Category.id_comp]
  refine ⟨⟨fun J => resG _ (le J) ((q.app _).hom (f (J PUnit.unit))), fun J J' => fn_ext fun x hx => ?_⟩,
    fun z' hz' => ?_⟩
  · rw [gs_res _ x inf_le_left hx, gs_mul _ x _ hx, gs_res _ x inf_le_right hx, ev J x hx.1, ev J' x hx.2,
      gs_unit _ x _ hx, gm_pull_g M _ _ x J J' hx.1 hx.2, Category.id_comp,
      compat _ _ _ q x (le J hx.1).1 (le J' hx.2).1 (le J hx.1).2, q₁]
  · have e₀ : h (b ⟨z', hz'⟩) = z' := congrArg (fun s : N.toScheme ⟶ Z => s ⟨z', hz'⟩) hb
    let x : (h ⁻¹ᵁ N).toScheme := ⟨b ⟨z', hz'⟩, show h (b ⟨z', hz'⟩) ∈ N from e₀.symm ▸ hz'⟩
    have hx : x ∈ (M.pull (h ⁻¹ᵁ N).ι).U (fun _ => i₀) := mem_pull.2 (hW (hbW _))
    refine ⟨x, TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i₀, ?_⟩, e₀⟩
    refine (isUnit_gs_iff_mem (𝟙 _) x _ hx _).1 ?_
    rw [ev _ x hx]
    exact unit _ q x ((r₁ x).symm ▸ hbW _) ((r₂ x).symm ▸ hbW _)

theorem exists_basicOpen_theta {C : Core} (T : C.Theta) :
    ∃ j, ((C.A.left.basicOpen (T.θ.f j) : C.A.left.Opens) : Set C.A.left).Nonempty := by
  have := C.lft
  have := C.isIntegral_G
  have := C.isOpenImmersion_a
  obtain ⟨-, -, -, hcl, -⟩ := GlobalTheory.jacobson_closedPoints_tools_int C.Z C.π
  obtain ⟨z, hz, -⟩ := hcl (genericPoint C.Z) PEmpty (fun k => k.elim) ⊤ trivial
  obtain ⟨x, hx, -⟩ := T.s_ne z hz
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨y₀⟩ := C.nonempty_A
  obtain ⟨y, hy⟩ := preimage_nonempty C.a y₀ ⟨x, hi⟩
  obtain ⟨j, hj⟩ := exists_chart T.L.isLB ((mulN C.A T.m).left y)
  have hyi : C.a y ∈ T.O₁.U i := C.G.toScheme.basicOpen_le _ hy
  have hu := (isUnit_gs_iff_mem C.a y _ hyi _).2 hy
  rw [T.w_sec y i j hyi hj] at hu
  exact ⟨j, _, (isUnit_gs_iff_mem _ y _ hj _).1 (isUnit_of_mul_isUnit_right hu)⟩

theorem exists_rational_section {C : Core} (T : C.Theta) (Om : Set C.G.toScheme) (ν) (hν : T.Norms Om ν)
    (M : LB C.G.toScheme) (w : LB.Iso (M.pull C.a) T.L.L) (D : M.ι → C.A.left.Opens) (hw : w.IsGen)
    (hD : ∀ i, (D i : Set C.A.left).Nonempty)
    (hn : ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ C.A.left) (i : M.ι) (j : T.L.L.ι),
      IntAt C.a (M.U i) x → Set.range x ⊆ T.L.L.U j → Set.range x ⊆ D i →
      ‖valF x _ (w.s (j, fun _ => i)).val‖ * ν p x j = 1) :
    ∃ (E : M.ι → C.G.toScheme.Opens) (t : ∀ i, Γ(C.G.toScheme, E i)ˣ), (∀ i, E i ≤ M.U i) ∧
      (∀ i, (M.U i : Set C.G.toScheme).Nonempty → (E i : Set C.G.toScheme).Nonempty) ∧
      (∀ i k (Y : Scheme.{0}) (r : Y ⟶ C.G.toScheme) (y : Y), r y ∈ E i → r y ∈ E k →
        gm r y _ (t i) = gm r y _ (M.g i k) * gm r y _ (t k)) ∧
      ∀ (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ C.Z), ∃ δ : ℝ, 0 < δ ∧
        ∀ (b : Sp (OO p) ⟶ C.G.toScheme) (i : M.ι), (gPt p ≫ b) ≫ C.GG.hom = y → b (cPt p) ∈ M.U i →
          Set.range (gPt p ≫ b) ⊆ E i →
          ‖valF (gPt p ≫ b) _ (t i).val‖ ≤ δ ∧ (b (cPt p) ∈ Om → ‖valF (gPt p ≫ b) _ (t i).val‖ = δ) := by
  have := C.isIntegral_G
  have := C.isOpenImmersion_a
  have := C.nonempty_A
  have hA := C.isPullback_a
  haveI : IsIntegral C.A.left := isIntegral_of_isOpenImmersion C.a
  obtain ⟨ξ, hξ⟩ := exists_generic C.A.left
  obtain ⟨j, hj⟩ := exists_basicOpen_theta T
  have lθ : C.A.left.basicOpen (T.θ.f j) ≤ T.L.L.U j := C.A.left.basicOpen_le _
  obtain ⟨θ₀, hθ₀⟩ : IsUnit (resG _ lθ (T.θ.f j)) := C.A.left.toRingedSpace.isUnit_res_basicOpen (T.θ.f j)
  let V : M.ι → C.A.left.Opens := fun i => C.A.left.basicOpen (T.θ.f j) ⊓ C.a ⁻¹ᵁ M.U i ⊓ D i
  have l₁ : ∀ i, V i ≤ C.A.left.basicOpen (T.θ.f j) := fun i => inf_le_left.trans inf_le_left
  have l₂ : ∀ i, V i ≤ (LB.div T.L.L (M.pull C.a)).U (j, fun _ => i) := fun i x hx =>
    ⟨lθ hx.1.1, mem_pull.2 hx.1.2⟩
  choose t ht using fun i => exists_push C.a (V i)
    (Semi.res (l₁ i) θ₀ * (Semi.res (l₂ i) (w.s (j, fun _ => i)))⁻¹)
  have ht' : ∀ i (Y : Scheme.{0}) (r : Y ⟶ C.A.left) (y : Y), r y ∈ V i →
      gm (r ≫ C.a) y _ (t i) = gm r y _ θ₀ * (gm r y _ (w.s (j, fun _ => i)))⁻¹ := fun i Y r y hy => by
    rw [ht i Y r y hy, map_mul, map_inv, gm_res r y _ hy, gm_res r y _ hy]
  have hE : ∀ i, C.a ''ᵁ V i ≤ M.U i := fun i => image_le C.a (inf_le_left.trans inf_le_right)
  have back : ∀ i (x : C.A.left), C.a x ∈ C.a ''ᵁ V i → x ∈ V i := fun i x hx =>
    (C.a.preimage_image_eq (V i)).le hx
  refine ⟨fun i => C.a ''ᵁ V i, t, hE, fun i hi => ⟨C.a ξ, ξ, ⟨⟨hξ _ hj, hξ _ (preimage_nonempty C.a ξ hi)⟩,
    hξ _ (hD i)⟩, rfl⟩, fun i k => ?_, fun p _ y => ?_⟩
  · have l : C.a ''ᵁ V i ⊓ C.a ''ᵁ V k ≤ M.U i ⊓ M.U k := inf_le_inf (hE i) (hE k)
    have e : Semi.res inf_le_left (t i) = Semi.res l (M.g i k) * Semi.res inf_le_right (t k) := by
      refine unit_eq_of_gm C.a ξ hξ fun hm => ?_
      rw [map_mul, gm_res _ ξ _ hm, gm_res _ ξ _ hm, gm_res _ ξ _ hm]
      have m₁ := back i ξ hm.1
      have m₂ := back k ξ hm.2
      have e₁ := ht' i _ (𝟙 _) ξ m₁
      have e₂ := ht' k _ (𝟙 _) ξ m₂
      have e₃ := gm_isGen hw (𝟙 _) ξ j j (fun _ => i) (fun _ => k) (l₂ i m₁).1 (l₂ i m₁).1 (l₂ i m₁).2 (l₂ k m₂).2
      have e₄ := gm_pull_g M C.a (𝟙 _) ξ (fun _ => i) (fun _ => k) (l₂ i m₁).2 (l₂ k m₂).2
      rw [gm_self T.L.isLB (𝟙 _) ξ (l₂ i m₁).1, e₄, _root_.one_mul] at e₃
      unfold gv at e₃
      rw [Category.id_comp] at e₁ e₂ e₃
      rw [e₁, e₂, e₃, mul_inv, inv_inv, mul_left_comm]
    intro Y r y a₁ a₂
    have hm : r y ∈ C.a ''ᵁ V i ⊓ C.a ''ᵁ V k := ⟨a₁, a₂⟩
    have := congrArg (gm r y _) e
    rwa [map_mul, gm_res _ y _ hm, gm_res _ y _ hm, gm_res _ y _ hm] at this
  · have lift : ∀ (b : Sp (OO p) ⟶ C.G.toScheme) (i : M.ι), Set.range (gPt p ≫ b) ⊆ (C.a ''ᵁ V i : C.G.toScheme.Opens) →
        ∃ x : Sp (PadicAlgCl p) ⟶ C.A.left, x ≫ C.a = gPt p ≫ b := fun b i hr =>
      ⟨IsOpenImmersion.lift C.a (gPt p ≫ b) (fun s hs => by
        obtain ⟨s', -, rfl⟩ := hr hs
        exact ⟨s', rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩
    by_cases hy : ∃ y' : Sp (PadicAlgCl p) ⟶ C.U.toScheme, y' ≫ C.U.ι = y
    · obtain ⟨y', rfl⟩ := hy
      obtain ⟨δ, hδ, H⟩ := hν.theta p y'
      refine ⟨δ, hδ, fun b i hb hc hr => ?_⟩
      obtain ⟨x, hx⟩ := lift b i hr
      let z : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
      have hz' : (x ≫ C.a) z ∈ C.a ''ᵁ V i := hx ▸ mem_of_range hr z
      have hz : x z ∈ V i := back i _ hz'
      have hxy : x ≫ C.A.hom = y' := by
        rw [← cancel_mono C.U.ι, Category.assoc, ← hA.w, reassoc_of% hx, ← hb, Category.assoc]
      obtain ⟨H₁, H₂⟩ := H x j hxy (range_sub z (l₂ i hz).1) ⟨b, hx.symm, trivial⟩
      have H₃ := hn p x i j ⟨b, hx.symm, hc⟩ (range_sub z (l₂ i hz).1) (range_sub z hz.2)
      have e₁ : valF (x ≫ C.a) _ (t i).val * valF x _ (w.s (j, fun _ => i)).val = valF x _ θ₀.val := by
        apply (toStk z).injective
        rw [map_mul, toStk_valF _ _ z hz', toStk_valF x _ z (l₂ i hz), toStk_valF x _ z (l₁ i hz), ht' i _ x z hz,
          ← Units.val_mul, inv_mul_cancel_right]
      have e₂ : valF x _ θ₀.val = valF x _ (T.θ.f j) := by
        rw [hθ₀, valF, valF, dif_pos ((top_le_iff_mem x _ z).2 (l₁ i hz)),
          dif_pos ((top_le_iff_mem x _ z).2 (lθ (l₁ i hz)))]
        congr 1
        change (C.A.left.presheaf.map (homOfLE lθ).op ≫ x.appLE _ _ _).hom _ = _
        rw [Scheme.Hom.map_appLE]
      have e₃ : ‖valF (gPt p ≫ b) _ (t i).val‖ = ‖valF x _ (T.θ.f j)‖ * ν p x j := by
        rw [← e₂, ← e₁, norm_mul, _root_.mul_assoc, H₃, _root_.mul_one, hx]
      rw [e₃]
      exact ⟨H₁, fun ho => H₂.2 ⟨b, hx.symm, ho⟩⟩
    · refine ⟨1, one_pos, fun b i hb _ hr => (hy ?_).elim⟩
      obtain ⟨x, hx⟩ := lift b i hr
      exact ⟨x ≫ C.A.hom, by rw [Category.assoc, ← hA.w, reassoc_of% hx, ← hb, Category.assoc]⟩

end ThetaLocal

open ThetaLocal NormGlue in

theorem exists_local_section_ne_zero_on_fibres : ∀ (C : Core) (L : C.Law) (T : C.Theta) (Om : Set C.G.toScheme) (ν), IsOpen Om → T.Norms Om ν → L.CompanionTheory Om → (∃ (M : LB C.G.toScheme) (w : LB.Iso (M.pull C.a) T.L.L) (D : M.ι → C.A.left.Opens), M.IsLB ∧ w.IsGen ∧ (∀ i, (D i : Set C.A.left).Nonempty) ∧ ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ C.A.left) (i : M.ι) (j : T.L.L.ι), IntAt C.a (M.U i) x → Set.range x ⊆ T.L.L.U j → Set.range x ⊆ D i → ‖valF x _ (w.s (j, fun _ => i)).val‖ * ν p x j = 1) → ∃ M : LB C.G.toScheme, M.IsLB ∧ LBIso (M.pull C.a) T.L.L ∧ ∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (M.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z' := by
  rintro C L T Om ν hOm hν hS ⟨M, w, D, hM, hw, hD, hn⟩
  refine ⟨M, hM, ⟨w, hw⟩, fun z => ?_⟩
  obtain ⟨E, t, hE, hne, ht, hδ⟩ := exists_rational_section T Om ν hν M w D hw hD hn
  have hA := C.isPullback_a
  have := L.smooth
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  obtain ⟨hI, hN, -⟩ := AddExt.isIntegral_and_normal C
    (pullback.map C.A.hom C.A.hom C.GG.hom C.GG.hom C.a C.a C.U.ι hA.w.symm hA.w.symm)
    ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hI' : IsIntegral (pullback C.GG.hom C.GG.hom) := hI
  have := C.lft
  have := C.flat
  obtain ⟨-, -, -, hcl, -⟩ := GlobalTheory.jacobson_closedPoints_tools_int C.G.toScheme (C.GG.hom ≫ C.π)
  obtain ⟨x₀, hx₀, hsp, -⟩ := hcl (C.e z) PEmpty (fun k => k.elim) ⊤ trivial
  have hz : z ⤳ C.GG.hom x₀ := by
    have e : C.GG.hom (C.e z) = z := congrArg (fun s : C.Z ⟶ C.Z => s z) C.e_sec
    exact e ▸ hsp.map C.GG.hom.continuous
  obtain ⟨N, b, c, K, _, s, x, b', c', hx, hb, -, H⟩ := hS x₀ hx₀
  let k : Sp K := IsLocalRing.closedPoint K
  have h₁ : x.left k = x₀ := by
    have : x.left k ∈ Set.range x.left := ⟨k, rfl⟩
    rwa [hx] at this
  have h₂ : N.ι (s k) = C.GG.hom x₀ := by
    rw [← h₁]
    exact (congrArg (fun q : Sp K ⟶ C.Z => q k) (Over.w x)).symm
  have h₃ : b.left (s k) ∈ Om := by
    have := H b' (by simp) ⟨k, rfl⟩
    rw [hb] at this
    exact this
  obtain ⟨i₀, hi₀⟩ := exists_chart hM (b.left (s k))
  let W : C.G.toScheme.Opens := ⟨Om, hOm⟩ ⊓ M.U i₀
  let b₀ : N.toScheme ⟶ C.G.toScheme := b.left
  have hb₀ : b₀ ≫ C.GG.hom = N.ι := Over.w b
  let N' : C.Z.Opens := N.ι ''ᵁ (b₀ ⁻¹ᵁ W)
  have le : N' ≤ N := N.ι_image_le _
  obtain ⟨σ, hσ⟩ := exists_local_section (pullback.fst C.GG.hom C.GG.hom) (pullback.snd C.GG.hom C.GG.hom)
    (pullback.fst C.GG.hom C.GG.hom ≫ C.GG.hom ≫ C.π) hN C.GG.hom (IsPullback.of_hasPullback _ _) M E hE hne t ht
    Om hδ W i₀ inf_le_right (fun _ h => h.1) ⟨_, h₃, hi₀⟩ N' (C.Z.homOfLE le ≫ b₀)
    (by rw [Category.assoc, hb₀, Scheme.homOfLE_ι]) (by
      intro v
      have e : N.ι (C.Z.homOfLE le v) = N'.ι v :=
        congrArg (fun q : N'.toScheme ⟶ C.Z => q v) (Scheme.homOfLE_ι _ le)
      exact (N.ι.preimage_image_eq (b₀ ⁻¹ᵁ W)).le (show N.ι (C.Z.homOfLE le v) ∈ N' from e ▸ v.2))
  exact ⟨N', σ, hz.mem_open N'.isOpen ⟨s k, ⟨h₃, hi₀⟩, h₂⟩, hσ⟩

end GlobalTheory
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_local_section_ne_zero_on_fibres' : ∀ (C : Core) (L : C.Law) (T : C.Theta) (Om : Set C.G.toScheme) (ν), IsOpen Om → T.Norms Om ν → L.CompanionTheory Om → (∃ (M : LB C.G.toScheme) (w : LB.Iso (M.pull C.a) T.L.L) (D : M.ι → C.A.left.Opens), M.IsLB ∧ w.IsGen ∧ (∀ i, (D i : Set C.A.left).Nonempty) ∧ ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ C.A.left) (i : M.ι) (j : T.L.L.ι), IntAt C.a (M.U i) x → Set.range x ⊆ T.L.L.U j → Set.range x ⊆ D i → ‖valF x _ (w.s (j, fun _ => i)).val‖ * ν p x j = 1) → ∃ M : LB C.G.toScheme, M.IsLB ∧ LBIso (M.pull C.a) T.L.L ∧ ∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (M.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z' := by
  atlas_forward_decl GlobalTheory.exists_local_section_ne_zero_on_fibres
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem exists_extension_with_section : Semi.extend_existsSt.{0} → Out.MulNSt → (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : K) ≠ 0 → Surjective (mulN B n).left) → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), letI := L.grp; letI := L.comm; IsSemiAbelian C.GG → C.HasTests → C.TorsSec n → T.Few n → ∃ M : LB C.G.toScheme, M.IsLB ∧ LBIso (M.pull C.a) T.L.L ∧ ∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (M.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z' := by
  intro hE hM hS C L T n hG hT hTors hFew
  have hB : T.BTest L := GlobalTheory.T.baseChangeTest_of_surjective_mul_abelianVariety hS C L T
  have hO : IsOpen (T.Om L) := (GlobalTheory.ZJ.etale_mulN_and_isOpen_om_of_isSemiAbelian C L T hG hM).2
  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_norms_of_tests hE C L T hT hB
  have h6 : L.CompanionTheory (T.Om L) := GlobalTheory.T.companionTheory_om_of_tests_torsionSections hE C L T n hT hB hTors hFew
  have hγ := GlobalTheory.ZJ.Core.exists_gen_normOne C L T (T.Om L) ν hO hν h6
  obtain ⟨-, hlft, -, hint, hflat, -, hop, -⟩ := core_basic C
  have := C.lft
  have hsm : Smooth C.GG.hom := by
    have := L.smooth
    exact SmoothOfRelativeDimension.smooth C.g _
  have hN : Geo.Tor.IsNormalScheme C.G.toScheme := fun x =>
    GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth C.GG.hom C.normal x
  have hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π) := inferInstance
  exact GlobalTheory.T.exists_local_section_ne_zero_on_fibres' C L T (T.Om L) ν hO hν h6
    (@GlobalTheory.exists_lineBundle_of_normOne_generators C.G.toScheme C.A.left hint (C.GG.hom ≫ C.π) hflat hlft' hN C.a hop T.L.L T.L.isLB ν hν.isNrm hγ)

end GlobalTheory.ZJ
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_extension_thetaSection_semiAbelian : Semi.extend_existsSt.{0} → Out.MulNSt → (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : K) ≠ 0 → Surjective (mulN B n).left) → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), letI := L.grp; letI := L.comm; IsSemiAbelian C.GG → C.HasTests → C.TorsSec n → T.Few n → ∃ M : LB C.G.toScheme, M.IsLB ∧ LBIso (M.pull C.a) T.L.L ∧ ∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (M.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z' := by
  atlas_forward_decl GlobalTheory.ZJ.exists_extension_with_section
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.Assembly

theorem exists_sec_of_lbIso_pull {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB)
    (hL' : L'.IsLB) (H : LBIso L' (L.pull F)) (s : LB.Sec L) :
    ∃ s' : LB.Sec L', ∀ y : X', F y ∈ Out.nonzeroLocus s → y ∈ Out.nonzeroLocus s' := by
  obtain ⟨W, hW⟩ := H
  obtain ⟨s', hs'⟩ := sec_pull_down ((isGen_iff W).1 hW) hL hL' s
  refine ⟨s', fun y hy => ?_⟩
  obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hy
  obtain ⟨k, hk⟩ := exists_chart hL' y
  have e := hs' _ (𝟙 _) y j k hj hk
  rw [Category.id_comp, gs_stalkMap F y _ hj] at e
  refine (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩
  exact isUnit_of_mul_isUnit_right ((congrArg IsUnit e).mp (u.map (F.stalkMap y).hom))

theorem mulN_eq_pow' {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = (𝟙 G) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem mulN_comm_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    (mulN G' n).left ≫ φ = φ ≫ (mulN G n).left := by
  have e := congrArg (fun q => q.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e₂ : pushHom h G' (𝟙 G') ≫ mulN G n = pushHom h G' (𝟙 G') ^ n := by
    rw [mulN_eq_pow', MonObj.comp_pow, Category.comp_id]
  rw [← e₂, ← mulN_eq_pow'] at e
  refine Eq.trans e ?_
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem exists_sec_fibres {H S : Scheme.{0}} (p : H ⟶ S) {L M : LB H} (hL : L.IsLB) (hM : M.IsLB) (z : S)
    (h₁ : ∃ N : S.Opens, z ∈ N ∧ LBIso (L.pull (p ⁻¹ᵁ N).ι) (M.pull (p ⁻¹ᵁ N).ι))
    (h₂ : ∃ (N : S.Opens) (σ : LB.Sec (M.pull (p ⁻¹ᵁ N).ι)), z ∈ N ∧
      ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, p ((p ⁻¹ᵁ N).ι x) = z') :
    ∃ (N : S.Opens) (σ : LB.Sec (L.pull (p ⁻¹ᵁ N).ι)), z ∈ N ∧
      ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, p ((p ⁻¹ᵁ N).ι x) = z' := by
  obtain ⟨N₁, hz₁, H₁⟩ := h₁
  obtain ⟨N₂, σ, hz₂, H₂⟩ := h₂
  have l₁ : p ⁻¹ᵁ (N₁ ⊓ N₂) ≤ p ⁻¹ᵁ N₁ := fun _ hx => hx.1
  have l₂ : p ⁻¹ᵁ (N₁ ⊓ N₂) ≤ p ⁻¹ᵁ N₂ := fun _ hx => hx.2
  have I : LBIso (L.pull (p ⁻¹ᵁ (N₁ ⊓ N₂)).ι) ((M.pull (p ⁻¹ᵁ N₂).ι).pull (H.homOfLE l₂)) :=
    H₁.chartPull (h := H.homOfLE l₁)
      (chartPullSame L _ _ _ _ fun _ => (H.homOfLE_ι l₁).symm)
      (chartPullLinComb M _ _ _ _ _ fun _ => (H.homOfLE_ι l₂).trans (H.homOfLE_ι l₁).symm)
  obtain ⟨σ', hσ'⟩ := exists_sec_of_lbIso_pull (pull_isLB hM _) (pull_isLB hL _) I σ
  refine ⟨N₁ ⊓ N₂, σ', ⟨hz₁, hz₂⟩, fun z' hz' => ?_⟩
  obtain ⟨x, hx, e⟩ := H₂ z' hz'.2
  have hm : x.1 ∈ p ⁻¹ᵁ (N₁ ⊓ N₂) := by
    change p x.1 ∈ N₁ ⊓ N₂
    exact (show p x.1 = z' from e) ▸ hz'
  refine ⟨⟨x.1, hm⟩, hσ' _ ?_, e⟩
  have : H.homOfLE l₂ ⟨x.1, hm⟩ = x := Subtype.ext (Scheme.homOfLE_apply l₂ _)
  rwa [this]

theorem exists_law_splitAll_cubical : Out.Laws → ∀ (C : Core) (T : C.Theta) (n : ℕ), C.HasTests → C.Indep → C.HasCharts → C.TorsSec n → T.Few n → ∃ L : C.Law, letI := L.grp; letI := L.comm; SplitAll C.GG ∧ IsSemiAbelian C.GG ∧ ∃ (PP : RigLB C.GG) (cub : CubicalStr C.GG PP) (m : CubeMap C.A C.GG), m.F = C.a ∧ m.e = C.U.ι ∧ m.IsPullCubical T.cub cub ∧ (T.L.IsSymmetric → PP.IsSymmetric) ∧ (∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (PP.L.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z') ∧ ∀ z : C.Z, ∃ N : C.Z.Opens, z ∈ N ∧ LBIso (T.O₁.pull (C.GG.hom ⁻¹ᵁ N).ι) ((PP.L.pull (mulN C.GG T.m).left).pull (C.GG.hom ⁻¹ᵁ N).ι) := by
  intro hL C T n hT hI hC hS hF
  obtain ⟨L⟩ := Core.nonempty_law_of_hasTests_of_indep C hT hI
  refine ⟨L, ?_⟩
  letI := L.grp
  letI := L.comm
  obtain ⟨h₁, h₂⟩ := GlobalTheory.ZJ.FibreSplit.splitAll_and_isSemiAbelian C L hT hC
  obtain ⟨M, hM, hMa, hσ⟩ := GlobalTheory.T.exists_lineBundle_extension_thetaSection_semiAbelian hL.extend hL.mulN
    GlobalTheory.abelian_torsion_finite_and_mulN_surjective.2 C L T n h₂ hT hS hF
  obtain ⟨-, -, -, -, -, -, -, hcart, -, hN, -⟩ := GlobalTheory.ZJ.core_basic C
  have : Nonempty C.U.toScheme := C.ne.to_subtype
  have := h₂.smooth
  have := h₂.geomConnected
  have hgi : GeometricallyIntegral C.GG.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ C.GG
  obtain ⟨PP, cub, m, hF, he, hp, hsym⟩ :=
    GlobalTheory.NormalCubeExt.exists_cubical_extension C.Z C.normal C.U.toScheme C.U.ι C.GG C.A C.a L.pull T.L T.cub M hM hMa
  have iso := GlobalTheory.T.lineBundleIso_extend_of_normal_base C.Z C.normal C.U.toScheme C.G.toScheme C.A.left C.U.ι C.GG.hom C.e C.a C.A.hom
    h₂.smooth hgi C.e_sec hcart
  have hw : LBIso T.L.L (PP.L.pull C.a) := by
    obtain ⟨w, hw, -⟩ := hp
    exact hF ▸ ⟨w, hw⟩
  refine ⟨h₁, h₂, PP, cub, m, hF, he, hp, hsym, fun z => ?_, fun z => ?_⟩
  · refine exists_sec_fibres C.GG.hom PP.isLB hM z ((iso PP.L M PP.isLB hM ?_).2 z) (hσ z)
    exact (LBIso.trans (pull_isLB hM _) T.L.isLB (pull_isLB PP.isLB _) hMa hw).symm
  · refine (iso T.O₁ (PP.L.pull (mulN C.GG T.m).left) T.isLB (pull_isLB PP.isLB _) ?_).2 z
    have i₁ : LBIso (T.L.L.pull (mulN C.A T.m).left) ((PP.L.pull (mulN C.GG T.m).left).pull C.a) :=
      hw.chartPull (h := (mulN C.A T.m).left) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullLinComb PP.L _ _ _ _ _ fun _ => (mulN_comm_of_isGrpPullback L.pull T.m).symm)
    exact LBIso.trans (pull_isLB T.isLB _) (pull_isLB T.L.isLB _) (pull_isLB (pull_isLB PP.isLB _) _)
      (LBIso.symm ⟨T.w, T.w_gen⟩) i₁

end GlobalTheory.ZJ.Assembly
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelian_split_cubical_extension_closure : Out.Laws → ∀ (C : Core) (T : C.Theta) (n : ℕ), C.HasTests → C.Indep → C.HasCharts → C.TorsSec n → T.Few n → ∃ L : C.Law, letI := L.grp; letI := L.comm; SplitAll C.GG ∧ IsSemiAbelian C.GG ∧ ∃ (PP : RigLB C.GG) (cub : CubicalStr C.GG PP) (m : CubeMap C.A C.GG), m.F = C.a ∧ m.e = C.U.ι ∧ m.IsPullCubical T.cub cub ∧ (T.L.IsSymmetric → PP.IsSymmetric) ∧ (∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (PP.L.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z') ∧ ∀ z : C.Z, ∃ N : C.Z.Opens, z ∈ N ∧ LBIso (T.O₁.pull (C.GG.hom ⁻¹ᵁ N).ι) ((PP.L.pull (mulN C.GG T.m).left).pull (C.GG.hom ⁻¹ᵁ N).ι) := by
  atlas_forward_decl GlobalTheory.ZJ.Assembly.exists_law_splitAll_cubical
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ClosureGroup

theorem exists_rescale {X' S' X S Y T : Scheme.{0}} (π : X' ⟶ S') (e' : S' ⟶ X') (he : e' ≫ π = 𝟙 S')
    (F : X' ⟶ X) (f : S' ⟶ S) (e : S ⟶ X) (hF : e' ≫ F = f ≫ e)
    (F₂ : X' ⟶ Y) (f₂ : S' ⟶ T) (e₂ : T ⟶ Y) (hF₂ : e' ≫ F₂ = f₂ ≫ e₂)
    {L : LB X} {M : LB Y} (hL : L.IsLB) (hM : M.IsLB) (a : LB.Gen (L.pull e)) (ha : a.IsGen)
    (b : LB.Gen (M.pull e₂)) (hb : b.IsGen) (H : LBIso (M.pull F₂) (L.pull F)) :
    ∃ w : LB.Iso (M.pull F₂) (L.pull F), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ S') (z : Z) (p : L.ι) (q : M.ι),
      F (e' (r z)) ∈ L.U p → F₂ (e' (r z)) ∈ M.U q →
      gm (r ≫ f) z ((L.pull e).U fun _ => p) (a.s fun _ => p) =
        gw w (r ≫ e') z p (fun _ => q) * gm (r ≫ f₂) z ((M.pull e₂).U fun _ => q) (b.s fun _ => q) := by
  obtain ⟨w, hw⟩ := H
  have pg := (isGen_iff w).1 hw
  have m₁ : ∀ (s : S') (p : L.ι), F (e' s) ∈ L.U p → f s ∈ (L.pull e).U fun _ => p := fun s p h =>
    mem_pull.2 ((congrArg (fun k => k s ∈ L.U p) hF).mp h)
  have m₂ : ∀ (s : S') (q : M.ι), F₂ (e' s) ∈ M.U q → f₂ s ∈ (M.pull e₂).U fun _ => q := fun s q h =>
    mem_pull.2 ((congrArg (fun k => k s ∈ M.U q) hF₂).mp h)
  let W : L.ι × M.ι → S'.Opens := fun j =>
    e' ⁻¹ᵁ ((L.pull F).U (fun _ => j.1) ⊓ (M.pull F₂).U (fun _ => j.2))
  have l₁ : ∀ j, W j ≤ f ⁻¹ᵁ (L.pull e).U fun _ => j.1 := fun j s hs => m₁ s _ (mem_pull.1 hs.1)
  have l₂ : ∀ j, W j ≤ f₂ ⁻¹ᵁ (M.pull e₂).U fun _ => j.2 := fun j s hs => m₂ s _ (mem_pull.1 hs.2)
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(S', W j)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ S') (z : Z) j, r z ∈ W j →
      gm r z (W j) (u j) = gm (r ≫ f) z ((L.pull e).U fun _ => j.1) (a.s fun _ => j.1) *
        (gw w (r ≫ e') z j.1 (fun _ => j.2) * gm (r ≫ f₂) z ((M.pull e₂).U fun _ => j.2) (b.s fun _ => j.2))⁻¹ :=
    ⟨fun j => res (l₁ j) (pullU f _ (a.s fun _ => j.1)) *
      ((show Γ(S', W j)ˣ from pullU e' _ (w.s (fun _ => j.1, fun _ => j.2))) * res (l₂ j) (pullU f₂ _ (b.s fun _ => j.2)))⁻¹,
      fun Z r z j hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_res r z _ hz _).trans (gm_pull r f z _ (l₁ j hz) _))
        ((map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          (gm_pull r e' z _ hz _) ((gm_res r z _ hz _).trans (gm_pull r f₂ z _ (l₂ j hz) _)))))))⟩
  obtain ⟨c, hc⟩ := glue_unit ⊤ W (fun _ => le_top) (fun s _ => by
      obtain ⟨p, hp⟩ := exists_chart hL (F (e' s))
      obtain ⟨q, hq⟩ := exists_chart hM (F₂ (e' s))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(p, q), mem_pull.2 hp, mem_pull.2 hq⟩) u (fun i j s hs => by
    have e₁ := gen_trans ha (𝟙 S' ≫ f) s (l₁ i hs.1) (l₁ j hs.2)
    have e₂' := gen_trans hb (𝟙 S' ≫ f₂) s (l₂ i hs.1) (l₂ j hs.2)
    have e₃ := pg _ (𝟙 S' ≫ e') s i.1 j.1 (fun _ => i.2) (fun _ => j.2) (mem_pull.1 hs.1.1) (mem_pull.1 hs.2.1)
      hs.1.2 hs.2.2
    rw [gm_pull_g M F₂ (𝟙 S' ≫ e') s _ _ hs.1.2 hs.2.2] at e₃
    simp only [trF, Fintype.prod_unique, zpow_one, Category.id_comp, ← hF, ← hF₂] at e₁ e₂' e₃
    rw [hu _ _ s i hs.1, hu _ _ s j hs.2]
    simp only [Category.id_comp]
    have alg : ∀ {V : Type} [CommGroup V] (A B x y z x' y' z' : V), x' = A * x → z' = B * z → y' = A * B⁻¹ * y →
        x' * (y' * z')⁻¹ = x * (y * z)⁻¹ := by
      rintro V _ A B x y z _ _ _ rfl rfl rfl
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    exact alg _ _ _ _ _ _ _ _ e₁ e₂' e₃)
  have hv : ∀ (Z : Scheme.{0}) (g : Z ⟶ X') (z : Z) (V : X'.Opens), g z ∈ V →
      gm g z V (res (le_top : V ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c)) = gm (g ≫ π) z ⊤ c := fun Z g z V h =>
    (gm_res g z _ h _).trans (gm_pull g π z ⊤ trivial c)
  let w' : LB.Iso (M.pull F₂) (L.pull F) := ⟨fun j => res (le_top : _ ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c) * w.s j⟩
  have hw' : ∀ (Z : Scheme.{0}) (g : Z ⟶ X') (z : Z) (p : L.ι) (q), F (g z) ∈ L.U p → g z ∈ (M.pull F₂).U q →
      gw w' g z p q = gm (g ≫ π) z ⊤ c * gw w g z p q := fun Z g z p q hp hq =>
    (map_mul _ _ _).trans (congrArg (· * _) (hv Z g z _ ⟨mem_pull.2 hp, hq⟩))
  refine ⟨w', (isGen_iff w').2 fun Z g z j j' k k' hj hj' hk hk' => ?_, fun Z r z p q hp hq => ?_⟩
  · rw [hw' Z g z j k hj hk, hw' Z g z j' k' hj' hk', pg Z g z j j' k k' hj hj' hk hk', mul_left_comm]
  · have hz : r z ∈ W (p, q) := ⟨mem_pull.2 hp, mem_pull.2 hq⟩
    have e₁ := (gm_res r z le_top hz c).symm.trans ((congrArg (gm r z _) (hc (p, q))).trans (hu Z r z (p, q) hz))
    rw [hw' Z (r ≫ e') z p _ hp (mem_pull.2 hq), Category.assoc, he, Category.comp_id, e₁, _root_.mul_assoc,
      inv_mul_cancel_right]

theorem isSymmetric_of_pull (hG : GlobalFnsSt) {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A]
    [GrpObj A'] [IsCommMonObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (hs : Sym A L) (L' : RigLB A') (H : LBIso L'.L (L.pull φ)) : L'.IsSymmetric := by
  obtain ⟨u, hu⟩ := exists_gen_neg_of_sym hG hA hL hs
  obtain ⟨w, hw⟩ := H
  obtain ⟨t, ht⟩ := gen_chartPull (chartPullSame L (K := Fin 2)
    (fun k => (![(GrpObj.inv : A' ⟶ A').left, 𝟙 A'.left] : Fin 2 → _) k ≫ φ) _ ![1, -1] φ fun k => by
      fin_cases k
      · exact PolBaseChange.inv_comm h
      · exact (Category.id_comp _).trans (Category.comp_id _).symm) u hu
  exact GlobalTheory.PrimNorm.isSymmetric_of_hasGen L' (exists_down ((isGen_iff w).1 hw) hL L'.isLB t ht)

theorem isQProjOver_ι {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) (U : X.Opens)
    [QuasiCompact U.ι] : IsQProjOver (U.ι ≫ f) := by
  obtain ⟨N, i, hi, e⟩ := h
  exact ⟨N, U.ι ≫ i, inferInstance, inferInstance, by rw [Category.assoc, e]⟩

theorem valF_eq_mul_of_gm {K : Type} [Field K] {X₁ X₂ X₃ : Scheme.{0}} {x₁ : Sp K ⟶ X₁} {x₂ : Sp K ⟶ X₂}
    {x₃ : Sp K ⟶ X₃} {U₁ : X₁.Opens} {U₂ : X₂.Opens} {U₃ : X₃.Opens} (z : Sp K) (h₁ : x₁ z ∈ U₁) (h₂ : x₂ z ∈ U₂)
    (h₃ : x₃ z ∈ U₃) {u₁ : Γ(X₁, U₁)ˣ} {u₂ : Γ(X₂, U₂)ˣ} {u₃ : Γ(X₃, U₃)ˣ}
    (e : gm x₁ z U₁ u₁ = gm x₂ z U₂ u₂ * gm x₃ z U₃ u₃) :
    valF x₁ U₁ u₁.val = valF x₂ U₂ u₂.val * valF x₃ U₃ u₃.val :=
  (toStk z).injective (by
    rw [map_mul, toStk_valF x₁ U₁ z h₁, toStk_valF x₂ U₂ z h₂, toStk_valF x₃ U₃ z h₃, e, Units.val_mul])

theorem exists_pre : Laws → Laws2 → ThmUSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ex.core.HasTests → ex.core.Indep → ex.core.HasCharts → ex.core.TorsSec (S.r * S.N) → (∃ T : ex.core.Theta, LBIso T.L.L (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀))) → ∃ Z : ZHPre ρ M U₀, (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) ∧ Z.LocTheta ∧ Nonempty ex.core.Law := by
  intro hL hL2 hU o Ω _ _ _ _ S ρ M U₀ EE Q ex hbig htest hind hch htors ⟨T, hT⟩
  have hcomm : IsCommMonObj ρ.P.A := ρ.P.isAb.comm
  have gp : IsGrpPullback ex.core.A ρ.P.A Q.u₀ (pullback.fst ρ.P.A.hom Q.u₀) := isGrpPullback_pullback ρ.P.A Q.u₀
  obtain ⟨-, hamp, hK⟩ := GlobalTheory.pol_pull _ _ _ _ _ _ _ _ ρ.P.isLB T.L.isLB ρ.P.isAb gp hT
  have hsym : T.L.IsSymmetric := isSymmetric_of_pull hL.globalFns gp ρ.P.isAb ρ.P.isLB ρ.P.sym T.L hT
  have hS := GlobalTheory.SymBaseChange.hypS_baseChange _ _ _ _ _ _ _ _ ρ.P.isLB T.L.isLB gp hT ρ.hypS
  have hN : 4 ≤ S.N := by
    have h2 : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]
    nlinarith
  have hunit : IsUnit ((S.r * S.N : ℕ) : Γ(ex.core.Z, ⊤)) := by
    have h := S.unit.map (M.s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
    rw [map_natCast] at h
    exact h
  have hfew : T.Few (S.r * S.N) := GlobalTheory.ZJ.theta_few hU hL hL2 ex.core T (hamp ρ.P.ample) (hK ρ.P.ktriv) hsym hS S.N _
    hN hunit (hbig.2.2.trans_le (Nat.le_self_pow two_ne_zero _))
  obtain ⟨law, hmain⟩ := GlobalTheory.T.exists_semiAbelian_split_cubical_extension_closure hL ex.core T _ htest hind hch htors hfew
  let _ := law.grp
  let _ := law.comm
  obtain ⟨hsplit, hsemi, PP, cub, m, hF, he, hpull, hsym', hloc, -⟩ := hmain
  have hiso : LBIso T.L.L (PP.L.pull ex.core.a) := by
    obtain ⟨w, hw, -⟩ := hpull
    rw [← hF]
    exact ⟨w, hw⟩
  have e₁ := PolBaseChange.eSec_comm gp
  have e₂ := PolBaseChange.eSec_comm law.pull
  have hs : eSec ex.core.A ≫ ex.core.A.hom = 𝟙 _ := Over.w η[ex.core.A]
  have hsP : eSec ρ.P.A ≫ ρ.P.A.hom = 𝟙 _ := Over.w η[ρ.P.A]
  have hsG : eSec ex.core.GG ≫ ex.core.GG.hom = 𝟙 _ := Over.w η[ex.core.GG]
  obtain ⟨w, hw, hv⟩ := exists_rescale ex.core.A.hom (eSec ex.core.A) hs _ _ _ e₁ _ _ _ e₂ ρ.P.isLB PP.isLB ρ.rig
    ρ.rig_gen PP.rig PP.rigGen (LBIso.trans (pull_isLB PP.isLB _) T.L.isLB (pull_isLB ρ.P.isLB _) hiso.symm hT)
  have hqc : QuasiCompact (Q.G.ι ≫ Q.P.hom) := (GlobalTheory.ZJ.core_basic ex.core).2.2.1
  have hpr := Q.proper
  have hqc' : QuasiCompact Q.G.ι := QuasiCompact.of_comp _ Q.P.hom
  refine ⟨{ u₀ := Q.u₀
            u₀_gen := Q.u₀_pt
            G := ex.core.GG
            grp := law.grp
            comm := law.comm
            semi := hsemi
            dim := law.smooth
            qproj := by
              have h := isQProjOver_ι Q.proj Q.G
              rw [← Category.assoc] at h
              exact h
            φ := ex.a
            cart := law.pull
            L := PP
            cub := cub
            sym := hsym' hsym
            w := w
            w_gen := hw
            w_rig := ?_
            split := hsplit }, ⟨Iso.refl _, Category.id_comp _, rfl, heq_of_eq (Category.comp_id _)⟩, hloc, ⟨law⟩⟩
  intro K _ g x y jP jL hx hy hP hL'
  let r : Sp K ⟶ U₀.toScheme := g ≫ pullback.snd ρ.P.A.hom Q.u₀
  have ry : r ≫ Q.u₀ = y := by
    have h := congrArg (· ≫ ρ.P.A.hom) hy
    simp only [Category.assoc] at h
    rw [pullback.condition] at h
    exact (Category.assoc _ _ _).trans (h.trans ((congrArg (y ≫ ·) hsP).trans (Category.comp_id _)))
  have rx : r ≫ U₀.ι = x := by
    have h := congrArg (· ≫ ex.core.GG.hom) hx
    exact (Category.assoc _ _ _).trans ((congrArg (g ≫ ·) law.pull.1.w.symm).trans ((Category.assoc _ _ _).symm.trans
      (h.trans ((Category.assoc _ _ _).trans ((congrArg (x ≫ ·) hsG).trans (Category.comp_id _))))))
  have rg : r ≫ eSec ex.core.A = g := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ eSec ρ.P.A) ry).trans hy.symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hs).trans (Category.comp_id _))
  let z : Sp K := IsLocalRing.closedPoint K
  have mP : pullback.fst ρ.P.A.hom Q.u₀ (g z) ∈ ρ.P.L.U jP := hP ⟨z, rfl⟩
  have mL : ex.a (g z) ∈ PP.L.U jL := hL' ⟨z, rfl⟩
  have key := hv _ r z jP jL ((congrArg (fun k => pullback.fst ρ.P.A.hom Q.u₀ (k z) ∈ ρ.P.L.U jP) rg).mpr mP)
    ((congrArg (fun k => ex.a (k z) ∈ PP.L.U jL) rg).mpr mL)
  erw [ry, rx, rg] at key
  exact valF_eq_mul_of_gm z (mem_pull.2 ((congrArg (fun k => k z ∈ ρ.P.L.U jP) hy).mp mP))
    (show g z ∈ (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)).U (fun _ => jP) ⊓ (PP.L.pull ex.a).U (fun _ => jL) from
      ⟨mem_pull.2 mP, mem_pull.2 mL⟩) (mem_pull.2 ((congrArg (fun k => k z ∈ PP.L.U jL) hx).mp mL)) key

end GlobalTheory.ClosureGroup
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelian_groupScheme_cubical_bundle_closure : Laws → Laws2 → ThmUSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ex.core.HasTests → ex.core.Indep → ex.core.HasCharts → ex.core.TorsSec (S.r * S.N) → (∃ T : ex.core.Theta, LBIso T.L.L (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀))) → ∃ Z : ZHPre ρ M U₀, (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) ∧ Z.LocTheta ∧ Nonempty ex.core.Law := by
  atlas_forward_decl GlobalTheory.ClosureGroup.exists_pre
end
