import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OntoXAndLamLowOfPublishedUE
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PublishedInputsImplyGalois
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExportFromReciprocityTheoremsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExportFromReciprocityTheorems
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportStOfPrintsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PageSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoStOfPageSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankAtPlacesRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MaxSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompareOffOwnAtRuns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TupleReadBaseTupleEqFamily
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareWSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunWeightArch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThreeRLtGOfParams
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeafShareIOfShareW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqOfSemilinear
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseLevelIsWhitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankInfRangeAddInfKer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadWStOfRegular
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExponentBoundOfUnitaryThetaStandardTheorems
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoXOfTwistSharesExp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LlOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamLowOfPublished
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FinitenessInputsRealDataThree
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn
theorem exportSt_of_reading_alt :
    GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
      GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach →
      GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.ExportedStatement :=
  _root_.GlobalTheory.T.exportSt_of_discrete_series_cover
end GlobalTheory.BigOn
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exportSt_of_reciprocity_and_casselman_wallach : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.ExportedStatement := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.exportSt_of_reading_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn.TwistBoundAtPlace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end Point
theorem twistSt_of_alt (hE : _root_.GlobalTheory.BigOn.ExportedStatement) (hG : _root_.GlobalTheory.BigOn.GeometricStatement')
    (hK : _root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) : _root_.GlobalTheory.BigOn.TwistStatement' := by
  obtain ⟨a, ha, H⟩ := (hE.and hG).and hK
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK'⟩ := H e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨⟨x1, E1⟩, ⟨c1, G1⟩⟩, ⟨c2, K1⟩⟩ := hK' Fm CH hc hL
  obtain ⟨x0, T0⟩ := hc.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨max c1 c2, fun c hcC hb => ?_⟩
  obtain ⟨x2, G2⟩ := G1 c ((le_max_left _ _).trans hcC) hb
  obtain ⟨x3, K2⟩ := K1 c ((le_max_right _ _).trans hcC) hb
  refine ⟨max (max x0 x1) (max x2 x3), fun x hx hle i p hp hM r O hR => ?_⟩
  have h0 : x0 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hle)
  have h1 : x1 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hle)
  have h2 : x2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hle)
  have h3 : x3 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hle)
  obtain ⟨-, N0, S, hTG⟩ := T0 x h0 hx i
  exact hasTwistBound_at p hR (E1 x hx h1 i p hp hM) (G2 x hx h2 i p hp hM r O hR).1 (K2 x hx h3 i p hp hM r O hR) hTG
end GlobalTheory.BigOn.TwistBoundAtPlace
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open GlobalTheory.RunJoin
namespace GlobalTheory.ShareOn
section Model
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end Model
section Run
end Run
section Point
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem p0_extreme_or_archOn_of_runModel : _root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x hx ι p r h => ∀ (i : Fin (Fm.D x ι).R.m) (C : Type) [Finite C]
    [MulAction p.P.Gp C] (M : TwoLevels (Fm.D x ι).host.E (Fm.D x ι).R.r p.P.Gp C) (ka : Wt M.Ψ (Fm.D x ι).R.r),
    RunModel p r h i M ka → (M.p0 = 0 ∨ M.p0 = (Fm.D x ι).R.r) ∨
      (0 < M.p0 ∧ M.p0 < (Fm.D x ι).R.r ∧ ArchOn M ka (Fm.parT x hx ι).TO) := by
  obtain ⟨x₀, hrun⟩ := GlobalTheory.FinalJoin.runHolds_of_parOK
  obtain ⟨CK, hCK⟩ := GlobalTheory.FinalJoin.RecordRun.exists_pageRun_record_sub_four
  obtain ⟨x₂, hpg⟩ := GlobalTheory.FinalJoin.pageOK_of_pageRun_beyond (fun _ _ => 0)
  refine Formalism.MainNotions.Closed.imp (GlobalTheory.T.runNumericalConditions_hold_along_family (max ((10 : ℝ) ^ 60) (max (x₀ 20 CK) (x₂ 20 CK)))) ?_
  intro eps Fm CH _ hx0
  obtain ⟨x0, hx0⟩ := hx0
  refine ⟨x0, fun x hx hle ι p _ hmore r hr hown i C _ _ M ka hRM => ?_⟩
  obtain ⟨⟨S, hCnW, hg, hC, hCZ, hxl⟩, -⟩ := hx0 x hx hle ι
  obtain ⟨-, hcore, -⟩ := hmore
  obtain ⟨v, e, hXc, hkaC, -⟩ := hRM
  have hl := hr.laws v
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hinj := hcore.inj
  have hpar : ∀ j, InR (Fm.D x ι) j → ParOK (r.used v).full.toTop (Fm.ex x hx ι).errX (ownAt (Fm.D x ι) v) j :=
    GlobalTheory.FinalJoin2.liftIndexParameterConditions_of_coreAndShortLaws _ p.T _ _ _ hl.j hl.p hl.sh rfl hcore.canon (hcore.fieldAt v) hcore.halfEX
      (fun j hj n => ⟨hl.lvA j hj n, hown v j n hj⟩)
  have hO := (GlobalTheory.FinalJoin2.fieldSmall_iff_opo (Fm.D x ι) _ hl.p (Fm.L x ι)).1 hcore.small
  have hP := hCK (Fm.D x ι) (Fm.L x ι) _ (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def S hCnW hg
    ((le_max_left _ _).trans hxl) hC hCZ _ _ _ (recPJ hl.p ((i : ℕ) + 1) hj) hj hO
  have hHC := (hrun (Fm.D x ι) _ hl.p hinj _ _ hpar ((i : ℕ) + 1) hj (Fm.L x ι) _ _ _ _ _ _ _ _ _ _ _ hP
    (((le_max_left _ _).trans (le_max_right _ _)).trans hxl)).2.1
  have hOK := (hpg (Fm.D x ι) _ _ ((i : ℕ) + 1) (recPJ hl.p ((i : ℕ) + 1) hj) (Fm.L x ι) _ _ _ _ _ _ _ _ _ _ _ hj hP
    (((le_max_right _ _).trans (le_max_right _ _)).trans hxl)).1
  have hwd := fun k => GlobalTheory.Shares.WtDic.weights_dictionary (Fm.D x ι) (r.used v).full.toTop hl.p ((i : ℕ) + 1) hj k
  haveI : Nonempty C := ⟨e.symm ((r.used v).full.toTop.dict ((i : ℕ) + 1) (r.used v).full.toTop.σ₀ 1).1⟩
  obtain ⟨c0⟩ := ‹Nonempty C›
  have hp0M : M.p0 = ((Fm.D x ι).R.sigW ((i : ℕ) + 1)).2 :=
    (M.comp_basePoint c0).symm.trans ((congrArg Data.p0 (hXc c0)).trans (hwd (e c0)).2.2.2.2.2.1)
  have hq : ((Fm.D x ι).R.sigW ((i : ℕ) + 1)).2 = (Fm.D x ι).R.m - ((i : ℕ) + 1) := rfl
  have hr : (Fm.D x ι).R.r = (Fm.D x ι).R.k + (Fm.D x ι).R.m - 1 := rfl
  have hk := (Fm.D x ι).R.m_add_three_le_k
  by_cases hjm : (i : ℕ) + 1 < (Fm.D x ι).R.m
  swap
  · left; left; rw [hp0M, hq]; omega
  right
  refine ⟨by rw [hp0M, hq]; omega, by rw [hp0M, hq, hr]; omega, ?_⟩
  have hκ : p.κ i = kaR (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def ((i : ℕ) + 1) :=
    GlobalTheory.BigOn.eq_kaR _ _ i (p.κ i) (fun τ => ((fw2 p).kap i τ).1) (fun τ => ((fw2 p).kap i τ).2.1)
      ((fw2 p).kap i (GlobalTheory.RunDepth.plOf _ (false, Classical.arbitrary _))).2.2
  have hΨ : M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c0)).Ψ :=
    (M.comp_Ψ c0).symm.trans (congrArg Data.Ψ (hXc c0))
  have hcard : M.Ψ.card = (Fm.D x ι).R.f := by rw [hΨ]; exact (hwd (e c0)).2.2.2.2.2.2.1
  have hr1 : 1 ≤ (Fm.D x ι).R.r := by rw [hr]; omega
  have hdim : WeightFamilies.dimY (Fm.D x ι) ((i : ℕ) + 1) = M.dimY := by
    unfold TwoLevels.dimY
    rw [hcard]
    have h2 := GlobalTheory.ArchInputs.two_mul_dimY _ hj
    have h3 : ((2 * WeightFamilies.dimY (Fm.D x ι) ((i : ℕ) + 1) : ℕ) : ℝ) =
        (((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1)) : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hr1]
      linarith
    have h4 : 2 * WeightFamilies.dimY (Fm.D x ι) ((i : ℕ) + 1) = (Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1)) :=
      by exact_mod_cast h3
    obtain ⟨t, ht⟩ := Nat.even_mul_pred_self (Fm.D x ι).R.r
    rw [ht] at h4 ⊢
    rw [show (t + t) / 2 = t by omega]
    rw [mul_add] at h4
    linarith
  refine archOn_of_comps M ka (fun k => ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k) e hXc
    (fun k => laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k)
    (fun k => laR (r.used v).full.toTop ((i : ℕ) + 1) (lR (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def ((i : ℕ) + 1)) k)
    (fun k => laR (r.used v).full.toTop ((i : ℕ) + 1) (fR (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def ((i : ℕ) + 1)) k)
    (Fm.parT x hx ι).TO _ hdim hkaC (fun k => ?_) (fun k k' τ h h' a => ?_) (fun k k' τ h h' a => ?_)
    (fun k => run_weight_arch _ _ hl.p _ hj _ _ _ _ _ _ _ _ _ _ _ _ _ hOK.hyp hjm k)
    (fun k => archOne_of_run _ _ hl.p hinj _ _ _ hj _ _ _ _ _ _ _ _ _ _ _ _ _ (hpar _ hj) hOK hHC hjm k)
  · show laR _ _ (p.κ i) k = _
    rw [hκ, ← (GlobalTheory.SharesDefinite.weight_and_degree hOK.hyp).1]
    exact (hwd k).2.2.1 _ _ _
  · simp only [GlobalTheory.Shares.laR, Formalism.L2.Pj.laU, (hwd k).2.2.2.2.2.1, (hwd k').2.2.2.2.2.1]
  · simp only [GlobalTheory.Shares.laR, Formalism.L2.Pj.laU, (hwd k).2.2.2.2.2.1, (hwd k').2.2.2.2.2.1]
end Point
end GlobalTheory.ShareOn
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory.BigOn
theorem typePrimes_gt_three_r_alt :
    _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ k : Fin 2, 3 * (Fm.D x i).R.r < (Fm.D x i).host.g k := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  exact _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i _ _ _ k => three_r_lt_g_of_params _ _ (Fm.params x hx i) k
end GlobalTheory.BigOn
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem modelSt_alt : _root_.GlobalTheory.ShareOn.ModelStatement := by
  refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and _root_.GlobalTheory.ShareOn.p0_extreme_or_archOn_of_runModel _root_.GlobalTheory.BigOn.typePrimes_gt_three_r_alt) ?_
  intro eps Fm CH _ hx0
  obtain ⟨x0, hx0⟩ := _root_.GlobalTheory.BigTop.EventuallyAtPoints.and hx0.1 hx0.2
  refine ⟨x0, fun x hx hle ι p hrows hmore r hr hown i => ?_⟩
  obtain ⟨harch, hg⟩ := hx0 x hx hle ι p hrows
  obtain ⟨C, hfin, hact, M, ka, hRM⟩ := exists_runModel p hmore r hr hown i
  have hb0 : 0 < badN (Fm.D x ι) := by
    obtain ⟨v, -⟩ := hRM
    exact (GlobalTheory.TrivLevel.badN_pos_iff _).2 (hmore.2.1.fieldAt v).bad
  obtain ⟨hcard, ρ, σ, f, h1, h2, h3, h4⟩ :=
    Reading.reading_of_runModel p r hr i M ka hb0 (Fm.parT x hx ι).nV_ge hRM
  exact ⟨C, hfin, hact, M, ka, ρ, σ, f, h1, h2, h3, h4, levelCondition_restrict_of_halfUnipotent p r hr i M ka (hg hmore) hRM, hcard,
    harch hmore r hr hown i C M ka hRM⟩
end GlobalTheory.ShareOn
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
namespace GlobalTheory.ShareOn.Comparison₂
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Tied
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
local instance  (r : RunData J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst
variable {fw : FWTie J R κ v₀} {hc : LawsCore J.toCore} {run : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData J}
  {h : ∀ v, LawsP (run v).full.toTop} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {wL wF : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {nT : ℕ}
  {ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)}
  {ph : Fin D.R.m → ℂ} {c : OnConst}
variable {P : Type} [Group P] [Finite P]
end Tied
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
end GlobalTheory.ShareOn.Comparison₂
namespace GlobalTheory.ShareOn
theorem shareSt_of_shareWSt_alt : _root_.GlobalTheory.ShareOn.SharedWeightStatement → _root_.GlobalTheory.BigOn.ShareStatement := by
  intro h
  unfold _root_.GlobalTheory.ShareOn.SharedWeightStatement _root_.GlobalTheory.BigOn.ForallTwoRuns _root_.GlobalTheory.BigOn.AtPtsAlt at h
  unfold _root_.GlobalTheory.BigOn.ShareStatement _root_.GlobalTheory.BigOn.ForallRecordObjects
  refine Closed.imp h fun Fm CH _ H => ⟨0, fun c _ _ => ?_⟩
  obtain ⟨x0, hx0⟩ := H
  exact ⟨x0, fun x hx hle i p hp hm r O hR =>
    Comparison₂.leafShareI_of_shareW p hR (hx0 x hx hle i p hp hm r hR.1.ok hR.2)⟩
end GlobalTheory.ShareOn
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open Module
namespace GlobalTheory.ShareOn.Alg
end GlobalTheory.ShareOn.Alg
namespace GlobalTheory.ShareOn.Alg
end GlobalTheory.ShareOn.Alg
namespace GlobalTheory.ShareOn
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop
open GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end GlobalTheory.ShareOn
namespace GlobalTheory.ShareOn
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop
open GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end GlobalTheory.ShareOn
namespace GlobalTheory.ShareOn
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies Formalism.MainNotions.ArithmeticCylinders
theorem shareWSt_of_modelSt_alt : _root_.GlobalTheory.ShareOn.ModelStatement → _root_.GlobalTheory.ShareOn.SharedWeightStatement := by
  intro hM
  unfold _root_.GlobalTheory.ShareOn.ModelStatement _root_.GlobalTheory.BigOn.ForallTwoRuns _root_.GlobalTheory.BigOn.AtPtsAlt at hM
  unfold _root_.GlobalTheory.ShareOn.SharedWeightStatement _root_.GlobalTheory.BigOn.ForallTwoRuns _root_.GlobalTheory.BigOn.AtPtsAlt
  refine (hM.and GlobalTheory.T.shareSize_bounds_along_family).imp ?_
  intro eps Fm CH _ h
  obtain ⟨⟨x1, h1⟩, ⟨x2, h2⟩⟩ := h
  refine ⟨max x1 x2, fun x hx hle ι p hp hmore r hr hown i => ?_⟩
  have hm := h1 x hx ((le_max_left _ _).trans hle) ι p hp hmore r hr hown i
  have hn := h2 x hx ((le_max_right _ _).trans hle) ι
  exact shareW_of_modelAt p i _ _ (by positivity) hm (by obtain ⟨_, _, -, -, h⟩ := _root_.GlobalTheory.T.exists_whittaker_lam_psi_half_unip _ _ _ _ _ _ _ _ _ _ p hp; exact h)
    (fun p0 h0 => (hn p0 h0).1) (hn 0 (Nat.zero_le _)).2
end GlobalTheory.ShareOn
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
namespace GlobalTheory.BadOnRec
end GlobalTheory.BadOnRec
namespace GlobalTheory.BadOnRec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
local instance  {D : D7} {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] (r : RunData J) :
    Algebra r.full.J.Q.c.F D.what₂.LL := inst
section General
open scoped TensorProduct
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) F.P0 F.ψ0⁻¹) → D.what₂.LL)}
end General
end GlobalTheory.BadOnRec
namespace GlobalTheory.BadOnRec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] runAlgBad
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}
theorem bad_rec_alt (hR : p.PointConditions') (hm : More p) {Pm : ParameterChoice' D L} {Tp : ParamsT D L Pm} {r : TwoRuns p.T p.P.Gp}
    {c : OnConst} {O : Obj p c} (hrec : RecAt p Tp r O) {del : ℝ} (j : Fin D.R.m) (hbad : BadW p j del) :
    (1 - del) * O.d0 j ≤ ((S2 p).D : ℝ) := by
  obtain ⟨hC, hOk, -, -, hRk, -⟩ := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hR hm.1
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.1.tied
  have hU : (F2 p).P0 ≤ (mirIncl (R2 p)).range := fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff hC.grp.levels g).1 hg
    exact ⟨u, e⟩
  obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
  have hmem := mem_eig_iff (ht v₁ j).1 (ht v₁ j).2 hC.grp hU
  have hf := finrank_eq_of_bij _ (GlobalTheory.OnTies.toForms_bijective (hrec.1.ok.laws v₁).p (fw2 p) j (z j)) _ _ hmem
  have hd0 : O.d0 j = (finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j) : ℝ) := by
    unfold OnObj.d0
    exact congrArg (fun n : ℕ => (n : ℝ)) hf
  have hV : ∀ x ∈ GlobalTheory.CovTop.spType (R2 p) (F2 p) j, goodOp (R2 p) j x ∈ GlobalTheory.CovTop.spType (R2 p) (F2 p) j :=
    fun x hx g => by
      rw [← GlobalTheory.BigOn.goodOp_rho_comm hOk.irr j (g : p.P.Gp) x, hx g, map_smul]
  have hsplit := finrank_inf_range_add_inf_ker (goodOp (R2 p) j)
    (fun x => LinearMap.congr_fun (goodOp_idem hOk.irr j) x) _ hV
  have hD : (S2 p).D = finrank D.what₂.LL ((R2 p).WL (F2 p) false j) := (hRk.2 j).symm
  have hbad' : (finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j ⊓ LinearMap.ker (goodOp (R2 p) j) :
      Submodule D.what₂.LL _) : ℝ) ≤ del * finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j) := hbad
  have hs : (finrank D.what₂.LL ((R2 p).WL (F2 p) false j) : ℝ) +
      (finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j ⊓ LinearMap.ker (goodOp (R2 p) j) : Submodule D.what₂.LL _) : ℝ) =
      finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j) := by
    exact_mod_cast hsplit
  rw [hd0, hD]
  nlinarith
end Point
end GlobalTheory.BadOnRec
namespace GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem badSt_of_badW_alt : _root_.GlobalTheory.ShareOn.BadWeightStatement → _root_.GlobalTheory.BigOn.BadPlacesStatement := by
  intro hB
  refine (hB.and GlobalTheory.T.badShareSize_bounds_along_family).imp fun Fm CH _ H => ?_
  obtain ⟨⟨x1, H1⟩, ⟨x2, H2⟩⟩ := H
  refine ⟨0, fun c _ _ => ⟨max x1 x2, fun x hx hle i p hR hm r O hrec => ?_⟩⟩
  have hb := H1 x hx ((le_max_left _ _).trans hle) i p hR hm r hrec.1.ok hrec.2
  have hq := (H2 x hx ((le_max_right _ _).trans hle) i).2.2.1
  intro j
  exact ⟨_, (Real.exp_pos _).le, hq, _root_.GlobalTheory.BadOnRec.bad_rec_alt hR hm hrec j (hb j)⟩
end GlobalTheory.BigOn
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BadWOn
open Module GlobalTheory.BadCount GlobalTheory.TwistedRepresentationEmbedding GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
set_option maxHeartbeats 1000000 in
theorem badW_of_del_bound_of_T_bound (p : PtAt ex Csz) (i : Fin D.R.m) (T : ℕ) (del : ℝ) (hGr : GlobalTheory.GLq.Green) (hRows : p.PointConditions')
    (hRec : RecTies p) (hmod : ModelAt p i T) (hr : 100 ≤ D.R.r) (hA : TieAdmG D)
    (hg : ∀ k : Fin 2, 2 ^ 12 ≤ D.host.g k ∧ 4 * (3 * (D.R.f : ℝ) / (D.host.g k : ℝ) + 23 * (D.R.f : ℝ) *
      Real.log (D.host.g k : ℝ) / Real.sqrt (D.host.g k : ℝ) + 2 * (D.R.f : ℝ) * (D.R.m : ℝ) *
      (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log (D.R.r : ℝ)) / ((D.host.g k : ℝ) - 1)) +
      (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f + Real.exp (-(D.R.f : ℝ) / (5 * Real.log (D.R.r : ℝ)))) ≤ del)
    (hsT : 2 * D.R.r + 50 * D.R.r ^ 2 * (D.R.f * (D.R.r * D.R.r / 4)) + 2 ≤ T) : BadW p i del := by
  classical
  obtain ⟨C, hCf, hact, M, ka, ρ, σ, f, hpull, hequiv, hli, hspan, hlev, hcard, hcase⟩ := hmod
  obtain ⟨lam, ψ, hW, hlam, hhalf⟩ := _root_.GlobalTheory.T.exists_whittaker_lam_psi_half_unip D L hT Gi Gl Kc Y cX ex Csz p hRows
  obtain ⟨-, hHex⟩ := GlobalTheory.T.exists_whittakerDatum_and_halfLevels D ψ hW.1
  choose Hh hHh using hHex
  let e : p.P.Gp ≃* G0g D.nd := p.R.eG.trans p.cG
  let π : p.P.Gp →* G0g D.nd := e.toMonoidHom
  let ιs : G0g D.nd →* p.P.Gp := e.symm.toMonoidHom
  let P : Subgroup (G0g D.nd) := p.P.P0.map π
  let P' : Subgroup p.P.Gp := P.comap π
  have hle : P' ≤ p.P.P0 := fun g hg => (Subgroup.mem_map_iff_mem e.injective).1 hg
  have hge : p.P.P0 ≤ P' := fun g hg => (Subgroup.mem_map_iff_mem e.injective).2 hg
  have hbot : LevelHyp (GlobalTheory.ShareOn.sub M ⊥) := hlev ⊥ ⟨0, fun g hg v => by
    rw [Subgroup.mem_bot] at hg
    subst hg
    intro a b
    simp only [map_one]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact Matrix.one_apply_ne (ne_of_gt h)
    · subst h; exact Matrix.one_apply_eq a⟩
  have hP'lev : LevelHyp (GlobalTheory.ShareOn.sub M P') := by
    obtain ⟨k, hk⟩ := hhalf
    exact hlev P' ⟨k, fun g hg v => hk g (hle hg) v⟩
  have hHlev : ∀ k, LevelHyp (GlobalTheory.ShareOn.sub M ((Hh k).comap π)) := fun k => hlev _ ⟨k + 1, fun g hg v =>
    ((hHh k (π g)).1 hg) ⟨k + 1, v⟩ (by simp)⟩
  have hsOf : GlobalTheory.ShareOn.sOf M ≤ T := by
    have key : ∀ a b : ℕ, a * (b - a) * 4 ≤ b * b := by
      intro a b
      rcases le_total a b with h | h
      · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le h
        rw [Nat.add_sub_cancel_left]
        nlinarith [sq_nonneg ((a : ℤ) - q)]
      · rw [Nat.sub_eq_zero_of_le h]; simp
    have hq : M.p0 * (D.R.r - M.p0) ≤ D.R.r * D.R.r / 4 := (Nat.le_div_iff_mul_le (by norm_num)).2 (key _ _)
    have hX : M.dimX ≤ D.R.f * (D.R.r * D.R.r / 4) := by
      unfold TwoLevels.dimX; rw [hcard]; exact Nat.mul_le_mul_left _ hq
    unfold GlobalTheory.ShareOn.sOf
    have := Nat.mul_le_mul_left (50 * D.R.r ^ 2) hX
    omega
  have hc : (M.p0 = 0 ∨ M.p0 = D.R.r) ∨ (0 < M.p0 ∧ M.p0 < D.R.r ∧ GlobalTheory.ShareOn.ArchOn M ka T ∧
      GlobalTheory.ShareOn.sOf M ≤ T ∧ LevelHyp (GlobalTheory.ShareOn.sub M ⊥)) := by
    rcases hcase with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3, hsOf, hbot⟩
  let A := p.R.toRealDat.FW i
  let N := p.R.toRealDat.nW i
  let ρK : Representation D.what₂.LL p.P.Gp (Fin N → D.what₂.LL) := GlobalTheory.TwistedRepresentationEmbedding.twist A.ρ A.chi⁻¹
  let χM : p.P.Gp →* ℂˣ := (Units.map σ.toMonoidHom).comp A.chi⁻¹
  let ρM : Representation ℂ p.P.Gp (M.cusp ka) := GlobalTheory.TwistedRepresentationEmbedding.twist ρ χM
  let ρE : Representation ℂ p.P.Gp (Fin N → ℂ) := GlobalTheory.TwistedRepresentationEmbedding.repE D.what₂.embLL ρK
  have hequivM : ∀ g v, ρM g (f v) = f (ρK g v) := by
    intro g v
    rw [GlobalTheory.TwistedRepresentationEmbedding.twist_apply, GlobalTheory.TwistedRepresentationEmbedding.twist_apply, hequiv, map_smulₛₗ]
    rfl
  have hequivE : ∀ g v, ρE g (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N v) = GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (ρK g v) := fun g v => GlobalTheory.TwistedRepresentationEmbedding.repE_embV _ _ _ _
  let ψ0' : P' →* D.what₂.LLˣ := p.P.ψ0⁻¹.comp (Subgroup.inclusion hle)
  let lamM : P' →* ℂˣ := (Units.map σ.toMonoidHom).comp ψ0'
  let lamb : P' →* ℂˣ := lam.comp (π.subgroupComap P)
  have hemb : ∀ k, ∃ n : ℕ, EmbReg ρE ((Hh k).comap π) n ∧
      (n : ℝ) * Nat.card ((Hh k).comap π) ≤ 2 * Nat.card P' * finrank ℂ (eig ρM P' lamM) := by
    intro k
    obtain ⟨n, hn, hb⟩ := model_bound M ka ρM T (GlobalTheory.TwistedRepresentationEmbedding.isPullRep_twist hpull χM) hc _ P' (hHlev k) hP'lev lamM
    exact ⟨n, GlobalTheory.T.embedsInRegularRepresentationCopies_complexEmbedding_indep D.what₂.LL _ _ p.P.Gp N ρK σ D.what₂.embLL ρM ρE f (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N) hli hspan
      (GlobalTheory.TwistedRepresentationEmbedding.embV_li _ _) (GlobalTheory.TwistedRepresentationEmbedding.embV_span _ _) hequivM hequivE _ n hn, hb⟩
  choose n hnE hnb using hemb
  have alg : ∀ (u w : D.what₂.LLˣ) (x y : Fin N → D.what₂.LL), y = ((u * w : D.what₂.LLˣ) : D.what₂.LL) • x ↔
      ((u⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • y - ((w : D.what₂.LLˣ) : D.what₂.LL) • x = 0 := by
    intro u w x y
    rw [sub_eq_zero]
    constructor
    · rintro rfl
      rw [smul_smul, ← Units.val_mul, inv_mul_cancel_left]
    · intro h
      rw [Units.val_mul, mul_smul, ← h, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  let aK : P' → (Fin N → D.what₂.LL) →ₗ[D.what₂.LL] (Fin N → D.what₂.LL) := fun γ =>
    ρK γ - ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) • LinearMap.id
  have haK : ∀ γ F, aK γ F = (((A.chi γ)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • A.ρ γ F -
      ((p.P.ψ0⁻¹ ⟨γ, hle γ.2⟩ : D.what₂.LLˣ) : D.what₂.LL) • F := fun γ F => rfl
  have hsp : spType p.R.toRealDat p.F.lv2 i = ⨅ γ : P', LinearMap.ker (aK γ) := by
    ext F
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    change F ∈ A.typeP p.P.P0 p.P.ψ0⁻¹ ↔ _
    rw [Formalism.IndefR.Arith.FormsL.mem_typeP]
    constructor
    · intro h γ
      rw [haK]
      exact (alg _ _ _ _).1 (h ⟨γ, hle γ.2⟩)
    · intro h q
      have := h ⟨q, hge q.2⟩
      rw [haK] at this
      exact (alg _ _ _ _).2 this
  have dM : finrank ℂ (eig ρM P' lamM) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i) := by
    rw [hsp]
    refine GlobalTheory.T.finrank_iInf_ker_semilinear_standardBasis D.what₂.LL (M.cusp ka) P' σ N f hli hspan aK (fun γ => ρM γ - ((lamM γ : ℂˣ) : ℂ) • LinearMap.id) ?_
    intro γ v
    show _ = f (ρK γ v - ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) • v)
    rw [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hequivM]
    rfl
  have hlamb : ∀ γ : P', ((lamb γ : ℂˣ) : ℂ) = D.what₂.embLL ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) :=
    fun γ => hlam ⟨γ, hle γ.2⟩ γ.2
  have haE : ∀ (γ : P') v, (ρE γ - ((lamb γ : ℂˣ) : ℂ) • LinearMap.id : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ))
      (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N v) = GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (aK γ v) := by
    intro γ v
    show _ = GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (ρK γ v - ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) • v)
    rw [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hequivE, hlamb]
  have dE : finrank ℂ (eig ρE P' lamb) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i) := by
    rw [hsp]
    exact GlobalTheory.T.finrank_iInf_ker_semilinear_standardBasis D.what₂.LL (Fin N → ℂ) P' D.what₂.embLL N (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N) (GlobalTheory.TwistedRepresentationEmbedding.embV_li _ _) (GlobalTheory.TwistedRepresentationEmbedding.embV_span _ _) aK
      (fun γ => ρE γ - ((lamb γ : ℂˣ) : ℂ) • LinearMap.id) haE
  haveI : Fintype (G0g D.nd) := Fintype.ofEquiv p.P.Gp e.toEquiv
  have hsumE : Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0 =
      ∑ g : p.P.Gp, D.ntypes.e0.coeff (e g) • ρE g := by
    rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum_fintype D.ntypes.e0.coeff (fun a b => b • (ρE.comp ιs) a) (fun a => zero_smul ℂ _)]
    exact (Fintype.sum_equiv e.toEquiv (fun g => D.ntypes.e0.coeff (e g) • ρE g)
      (fun h => D.ntypes.e0.coeff h • (ρE.comp ιs) h) (fun g => by simp [ιs])).symm
  obtain ⟨-, -, -, hid, -, -⟩ := p.grpRecPin
  have hE0 : ∀ v, Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0 (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N v) =
      GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (eGood p.R.toRealDat i v) := by
    intro v
    have hG : eGood p.R.toRealDat i v = ∑ g : p.P.Gp, (idemOf p.P.A3.A.X).coeff g • ρK g v := by
      show ((∑ g, ((idemOf p.P.A3.A.X).coeff g * ((A.chi g)⁻¹ : D.what₂.LLˣ)) • A.ρ g :
        (Fin N → D.what₂.LL) →ₗ[D.what₂.LL] (Fin N → D.what₂.LL)) v) = _
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [LinearMap.smul_apply, mul_smul]
      rfl
    rw [hsumE, LinearMap.sum_apply, hG, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, hequivE, map_smulₛₗ, hid]
  let aO : Option P' → (Fin N → D.what₂.LL) →ₗ[D.what₂.LL] (Fin N → D.what₂.LL) := fun o =>
    o.elim (eGood p.R.toRealDat i) aK
  let aO' : Option P' → (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) := fun o =>
    o.elim (Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0) (fun γ => ρE γ - ((lamb γ : ℂˣ) : ℂ) • LinearMap.id)
  have dBad : finrank ℂ (eig ρE P' lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0) :
      Submodule ℂ (Fin N → ℂ)) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i ⊓
      LinearMap.ker (eGood p.R.toRealDat i) : Submodule D.what₂.LL (Fin N → D.what₂.LL)) := by
    have h1 : (eig ρE P' lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0) :
        Submodule ℂ (Fin N → ℂ)) = ⨅ o, LinearMap.ker (aO' o) := by
      rw [iInf_option, inf_comm]; rfl
    have h2 : (spType p.R.toRealDat p.F.lv2 i ⊓ LinearMap.ker (eGood p.R.toRealDat i) :
        Submodule D.what₂.LL (Fin N → D.what₂.LL)) = ⨅ o, LinearMap.ker (aO o) := by
      rw [iInf_option, inf_comm, hsp]; rfl
    rw [h1, h2]
    refine GlobalTheory.T.finrank_iInf_ker_semilinear_standardBasis D.what₂.LL (Fin N → ℂ) (Option P') D.what₂.embLL N (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N) (GlobalTheory.TwistedRepresentationEmbedding.embV_li _ _) (GlobalTheory.TwistedRepresentationEmbedding.embV_span _ _)
      aO aO' ?_
    rintro (_ | γ) v
    · exact hE0 v
    · exact haE γ v
  have hsplit : IsSplit π ιs := ⟨fun g => e.apply_symm_apply g, fun g γ h => by
    have hγ : γ = 1 := e.injective (h.trans e.map_one.symm)
    subst hγ; simp⟩
  let ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ := fun k =>
    haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
    ZMod.stdAddChar
  have hψ₀ : ∀ k, ψ₀ k ≠ 1 := by
    intro k h
    haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
    haveI : Fact (1 < D.host.g k) := ⟨(D.host.g_prime k).one_lt⟩
    have := ZMod.isPrimitive_stdAddChar (D.host.g k) (one_ne_zero)
    rw [AddChar.mulShift_one] at this
    exact this h
  have hbd : ∀ k, (n k : ℝ) * Nat.card ((Hh k).comap π) ≤
      2 * Nat.card (P.comap π) * finrank ℂ (eig ρE (P.comap π) lamb) := by
    intro k; rw [dE, ← dM]; exact hnb k
  obtain ⟨S, hSbad, hineq⟩ := GlobalTheory.T.bad_part_dim_le_sum_local_shares_whittaker D p.P.Gp (Fin N → ℂ) π ιs hsplit ρE P lam ψ hW lamb (fun γ => rfl) Hh hHh n 2
    hnE hbd ψ₀ hψ₀
  have hadm := GlobalTheory.T.admLq_of_green_of_eSerTie hGr D hRec.eSer
  have hloc : ∀ k, 4 * locShare D (fun k _ => eUk D k (ψ₀ k)) k (S k) ≤ del := fun k =>
    le_trans (by linarith [GlobalTheory.T.weightedIdempotent_localShare_bad_tuples_le D ψ₀ hψ₀ hadm hA hr (fun k => (hg k).1) k (S k) (hSbad k)]) (hg k).2
  rw [dBad, dE] at hineq
  unfold GlobalTheory.ShareOn.BadW
  have h0 := hloc 0
  have h1 := hloc 1
  have hd : (0 : ℝ) ≤ finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i) := Nat.cast_nonneg _
  refine hineq.trans ?_
  nlinarith
end Point
theorem badWSt_of_greenCuspidal_of_modelSt (hG : GlobalTheory.Published.GreenCuspidal) (hM : _root_.GlobalTheory.ShareOn.ModelStatement) : _root_.GlobalTheory.ShareOn.BadWeightStatement := by
  have hGr := hG.green
  refine Closed.imp ((hM.and GlobalTheory.T.badShareSize_bounds_along_family).and GlobalTheory.T.hodgeLineMultiple_le_familyThreshold) ?_
  rintro eps Fm CH - ⟨⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩, ⟨x3, hx3⟩⟩
  refine ⟨max x1 (max x2 x3), fun x hx hle ι p hp hMore r hr hown i => ?_⟩
  have h1 : x1 ≤ x := (le_max_left _ _).trans hle
  have h2 : x2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have h3 : x3 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  obtain ⟨hr100, hA, -, hg⟩ := hx2 x hx h2 ι
  exact _root_.GlobalTheory.BadWOn.badW_of_del_bound_of_T_bound p i _ _ hGr hp hMore.2.2 (hx1 x hx h1 ι p hp hMore r hr hown i) hr100 hA hg (hx3 x hx h3 ι)
end GlobalTheory.BadWOn
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open GlobalTheory.BigOn
namespace GlobalTheory.BigOn
theorem ontoX_of_hypotheses_alt_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.ChebotarevDegreeOne → _root_.UpperTheory.GalS.CuspUAlt → _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.CuspRapidDecay → _root_.UpperTheory.Zero.LLC.RecTExists → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → _root_.GlobalTheory.BigOn.SurjectiveOntoX := by
  intro hGreen hCoh hHecke hCheb hGal hBC hBS hAbove hDecay hLL hCover hCW
  have hArtin : GlobalTheory.Published.GlobalArtinReciprocity :=
    GlobalTheory.Published.HeckeLAdicCharacter.globalArtin hHecke
  have hRay : GlobalTheory.Published.RayClassFieldSt :=
    GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt hArtin
  have hSer : GlobalTheory.SerStd.SeriesRatS := (GlobalTheory.seriesRatS_and_serInt_of_globalArtin hArtin).1
  have hExport : _root_.GlobalTheory.BigOn.ExportedStatement := by
    apply _root_.GlobalTheory.T.exportSt_of_reciprocity_and_casselman_wallach <;> with_reducible assumption
  have hPage : _root_.GlobalTheory.BigOn.PageStatement := _root_.GlobalTheory.BigOn.pageSt_alt
  have hGeo : _root_.GlobalTheory.BigOn.GeometricStatement' := _root_.GlobalTheory.BigOn.geoSt_of_pageSt_alt hPage
  have hRank := _root_.GlobalTheory.BigOn.rankLocSt_of_max_geo_runs _root_.GlobalTheory.BigOn.maxSt_alt hGeo _root_.GlobalTheory.BigOn.compareOffOwn_atRuns_alt
  have hTwist : _root_.GlobalTheory.BigOn.TwistStatement' := _root_.GlobalTheory.BigOn.TwistBoundAtPlace.twistSt_of_alt hExport hGeo hRank
  have hModel := _root_.GlobalTheory.ShareOn.modelSt_alt
  have hShare : _root_.GlobalTheory.BigOn.ShareStatement := _root_.GlobalTheory.ShareOn.shareSt_of_shareWSt_alt (_root_.GlobalTheory.ShareOn.shareWSt_of_modelSt_alt hModel)
  have hBad : _root_.GlobalTheory.BigOn.BadPlacesStatement := _root_.GlobalTheory.BigOn.badSt_of_badW_alt (_root_.GlobalTheory.BadWOn.badWSt_of_greenCuspidal_of_modelSt hGreen hModel)
  have hExp : _root_.GlobalTheory.BigOn.ExponentStatement := _root_.GlobalTheory.T.expSt_of_base_change_and_crystalline_lattices hCoh hHecke hCheb hGal hBC hBS hAbove hLL
  exact _root_.GlobalTheory.BigOn.ontoX_of_twist_shares_exp_alt hExport hTwist hShare hBad hExp
end GlobalTheory.BigOn
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
namespace GlobalTheory.BigTop
theorem lamLow_of_hypotheses_alt_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent →
    _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.FormalDegreeCompactDual → _root_.GlobalTheory.BigTop.LambdaLowerBound₂ := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine (Formalism.MainNotions.DIV.closed_Csz_ge FamHyp 8).imp ?_
  intro eps Fm CH _ h8
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.thetaLift_weightSizes_eventually_along_family eps Fm
  refine ⟨x0, fun x hx hle i p hp C => ?_⟩
  have hS : ∀ j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := hx0 x hx hle i
  refine _root_.GlobalTheory.T.finiteness_inputs_real_data_three_alt h1 h2 h3 h4 h5 h6 h7 (T := p.T) (R := p.R) (F := p.F) p.κ p.v₀ p.O 1 (Fm.L x i).sc.b C CH
    hp.ok hp.sep p.charW hp.exAt hp.prim p.phsOne p.stdChar p.fw p.bar hp.ioExt p.pins (fun j => (hp.oneMap j).1) p.phase hS
    ?_ ?_ ⟨_, ⟨Fm.params x hx i⟩⟩ p.stdV
  · intro j
    have := GlobalTheory.T.hookLogSum_sub_sizeTerm_le_lowerBound (Fm.D x i) (Fm.L x i) p.Del p.h0 Fm.Csz j h8 (hS j)
    exact this
  · intro j
    show _ - C * 0 ≤ _
    rw [mul_zero, sub_zero]
    exact le_rfl
end GlobalTheory.BigTop
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
namespace GlobalTheory.Fc.S0
theorem ontoX_and_lamLow_of_unitaryGroupHypotheses' :
    _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses → _root_.GlobalTheory.BigOn.SurjectiveOntoX ∧ _root_.GlobalTheory.BigTop.LambdaLowerBound₂ := by
  intro P
  exact ⟨_root_.GlobalTheory.BigOn.ontoX_of_hypotheses_alt_alt P.greenCuspidal P.clozelCohomological
      P.heckeLAdicCharacter P.chebotarevDegreeOne
      P.galoisRepOfPolarizedCuspidal P.baseChangeDefiniteUnitary
      P.bhattScholzeCrystallineLattices P.heckeLAdicCharacterAbove P.cuspRapidDecay
      (_root_.UpperTheory.One.M.New.llOf_alt P.litN.loc.llc P.litN.loc.conv
      P.litN.loc.dzi P.litN.loc.brauer P.litN.loc.chev P.globalArtinReciprocity P.litN.loc.exh
      P.litN.loc.multi P.litN.loc.cos P.litN.loc.zel P.litN.loc.geo P.litN.loc.bz)
      P.discreteSeriesCover P.casselmanWallach,
    _root_.GlobalTheory.BigTop.lamLow_of_hypotheses_alt_alt P.cuspRapidDecay P.weilSiegelFormulaUnitary
      P.siegelWeilUnitaryConvergent P.doublingMethod P.unramifiedDoublingGL
      P.bernsteinZelevinskyFiniteness P.formalDegreeCompactDual⟩
end GlobalTheory.Fc.S0
end
end
end
