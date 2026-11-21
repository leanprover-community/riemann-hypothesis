import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFibFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtCommon
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtLift
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PIsolate
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PIsolateSpec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PImageOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PGenBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PIndDesc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSHSec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFinSec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PImageFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PLocFinGeo
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PRingSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PLocFinAff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCoverOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.WtBCOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PInvTrans
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PGalTrans
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SplittingFieldConstruction
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSplitCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSumComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNormSpec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtClopen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtPush
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCountEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCountWt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtLocal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtGlue
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultBC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtAgree
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtOpen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtVanish
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtUnique
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtDegConst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNmlInt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNmlNoeth
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultSec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultEt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultOpen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtOfFlat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtDeg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PStalkSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultSumPt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PArtSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultPt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtFlat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFunSec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrRed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.TrHlOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtInj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamSemi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PRedZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSecFun
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSumExLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PRpBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrIdQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrDegQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrCompQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSumEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrBCQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrChar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrEqQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCycComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PImgBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrCompQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.ImgcSpec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamBC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrSplitQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamPush
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrGraphQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrPush
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.TrBCOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrRel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPhiEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.FLOf

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.ptEx_of :
    PtEx := by
  intro X s
  let Ω : Type := AlgebraicClosure (X.residueField s)
  let y : gp Ω ⟶ Spec (X.residueField s) :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField s) Ω))
  refine ⟨Ω, inferInstance, inferInstance, y ≫ X.fromSpecResidueField s, ?_⟩
  rw [pt_comp]
  exact Scheme.fromSpecResidueField_apply s (pt y)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtPt_of :
    WtExt → PtCommon → WtPt := by
  intro hE hC Z S p _ w hw Ω Ω' _ _ _ _ z z' h
  obtain ⟨L, _, _, a, a', ha⟩ := hC Z Ω Ω' z z' h
  rw [← hE p w hw Ω L z a, ← hE p w hw Ω' L z' a', ha]
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.locFinSec_of :
    CoverOne → LocFinGeo → LocFinSec := by
  intro hC hG R _ F G f V U r _ b hb
  obtain ⟨W, π, a, hE, hS, ha⟩ := hC R f V b hb
  haveI := hE
  haveI := hS
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ (hG π r) ?_
  rintro U' g ⟨s, hs⟩ V' k r' hk
  refine ⟨Sec.res (pullback.lift k r' hk ≫ s) a, ?_⟩
  rw [map_res, ha, res_res]
  congr 1
  rw [Category.assoc, hs, pullback.lift_fst]
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.splitField_of :
    SplitField :=
  _root_.UpperTheory.Reformulated.B.SplittingFieldConstruction.splitField_of
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtCrit_of :
    PtEx → WtCrit := by
  intro hPt Z S p w h A φ hφ
  choose N c hN hu hc using h A φ hφ
  refine ⟨c, ?_, fun Ω _ _ x => (hc (pt x) Ω x (hu (pt x))).symm⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro u
  refine ⟨N u, hN u, hu u, fun u' hu' => ?_⟩
  obtain ⟨Ω, _, _, x, rfl⟩ := hPt A.U u'
  rw [← hc (pt x) Ω x (hu (pt x)), hc u Ω x hu']
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.normAff_of :
    Chart → NormSpec → NormAff := by
  intro hC hN Z S p _ U hU hD hI
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hC p Γ(S, U) hU.fromSpec
  obtain ⟨w, hw⟩ := hN Γ(S, U) B
  exact ⟨⟨_, _, hU.fromSpec, v, _, hpb⟩, w, inferInstance, hU.range_fromSpec, hw⟩
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtNormal_of :
    NormAff → NwtGlue → WtNormal := by
  intro hAff hGlue Z S p _ hS
  have h : ∃ w, IsNwt p w := by
    refine hGlue p (fun s => ?_)
    obtain ⟨U, hU, hs, hd, hi⟩ := hS s
    obtain ⟨A, w, ho, hr, hw⟩ := hAff p U hU hd hi
    exact ⟨A, w, ho, by rw [hr]; exact hs, hw⟩
  unfold nwt
  rw [dif_pos h]
  exact h.choose_spec
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nmlLoc_of :
    NmlInt → NmlNoeth → NmlLoc := by
  intro hI hN S hS h
  rcases h with h | h
  · haveI := h
    exact hI S hS
  · haveI := h
    exact hN S hS
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtFlat_of :
    WtBC → WtFlat → WtUnique → MultBC → NwtFlat := by
  intro hBC hFlat hUniq hMBC Z' S' Z S v p' p g _ _ _ pb hN hD
  haveI : IsFinite p' := MorphismProperty.of_isPullback pb ‹_›
  refine hUniq p' _ _ (hBC v p' p g _ pb hN.1) (hFlat p') _ hD ?_
  intro Ω _ _ z hz
  rw [hMBC v p' p g pb]
  refine hN.2 Ω (z ≫ v) ?_
  have e : (z ≫ v) ≫ p = (z ≫ p') ≫ g := by
    rw [Category.assoc, pb.w, Category.assoc]
  rw [e, pt_comp]
  exact hz
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.multBasic_of :
    MultBC → MultOpen → MultEt → MultBasic := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.multSum_of :
    MultSumPt → MultBC → MultSum := by
  intro hPt hBC Z S p _ _ Ω _ _ x
  have hpb : IsPullback (pullback.fst p x) (pullback.snd p x) p x := IsPullback.of_hasPullback p x
  have hfin := Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb (IsLocalRing.closedPoint Ω)
  have h1 := hPt Ω (pullback.snd p x)
  rw [hBC _ _ _ _ hpb] at h1
  rw [show pt x = x (IsLocalRing.closedPoint Ω) from rfl, ← hfin, ← h1]
  simp only [Wt.push, Wt.comap]
  have hb := fib_bijOn hpb (Ω := Ω) (𝟙 _)
  rw [Category.id_comp] at hb
  exact (finsum_mem_eq_of_bijOn _ hb (fun _ _ => rfl)).symm
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.sumNat_of :
    SumNat := by
  intro R _ F Z S p w A B t a b hB Ω _ _ x
  rw [res_res, hB Ω (x ≫ t.g)]
  symm
  refine finsum_mem_eq_of_bijOn (fun z => z ≫ t.k) (fib_bijOn t.isPullback x) ?_
  intro z _
  simp only [res_res, Category.assoc, t.hv]
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.opEq_of :
    FL → RpBasic → RpOp → OpEq := by
  intro hFL hB hOp Q Z S p _ F G t τ τ' hτ hτ' n
  ext x
  obtain ⟨a, ha⟩ := (hB (ZMod Q) (res (ZMod Q) F) Z n).1 x
  have hd := (hB (ZMod Q) (res (ZMod Q) F) Z n).2.1 x a ha
  have h1 := hOp _ _ τ n x a ha
  have h2 := hOp _ _ τ' n x a ha
  obtain ⟨y, hy⟩ := (hFL Q p F G t).2 τ τ' hτ hτ' (Sq.self p) (n - 1) n (n + 1)
    (sub_add_cancel n 1) rfl a hd
  exact ((hB (ZMod Q) (res (ZMod Q) G) S n).2.2.1 _ _ _ _ h1 h2).1.mpr ⟨y, hy⟩
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem pullHQ_comp' (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n i : ℤ) :
    pullHQ l (sch.map (f ≫ g)) n i = pullHQ l (sch.map f) n i ∘ₗ pullHQ l (sch.map g) n i := by
  simp only [pullHQ, Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]

theorem UpperTheory.Gal.TranscendenceTraces.corrBCQ_of :
    TrBCQ → CorrBCQ := by
  intro hT l _ n i S' Y' S Y c' c g g' v hpb hf hw hl
  haveI := c.fin
  haveI := c'.fin
  simp only [Corr.opQ]
  rw [← LinearMap.comp_assoc, hT l n i v c'.p c.p g c.w hpb c.wt hl, ← hw,
    LinearMap.comp_assoc, LinearMap.comp_assoc, ← pullHQ_comp', ← pullHQ_comp', hf]
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trDeg_of :
    TrPush → TrLin → TrDeg := by
  intro hP hL q _ n i Z S p _ w d hw hq hpush x
  have h1 := hP q n i p (𝟙 S) w (by simpa using hw) hq x
  simp only [Category.comp_id] at h1
  rw [h1, hpush]
  exact (hL q n i).2.2 S d hq x
end

section
namespace UpperTheory.Gal.TranscendenceTraces

theorem ptEx_holds : PtEx := @ptEx_of

theorem chart_holds : Chart := @chart_of

theorem fibFin_holds : FibFin := @fibFin_of @chart_holds

theorem ptCommon_holds : PtCommon := @ptCommon_of

theorem ptOne_holds : PtOne := @ptOne_of @chart_holds

theorem wtExt_holds : WtExt := @wtExt_of @ptOne_holds @chart_holds

theorem wtPt_holds : WtPt := @wtPt_of @wtExt_holds @ptCommon_holds

theorem ptLift_holds : PtLift := @ptLift_of

theorem isolateSpec_holds : IsolateSpec := @isolateSpec_of

theorem isolate_holds : Isolate := @isolate_of @chart_holds @isolateSpec_holds

theorem imageOne_holds : ImageOne := @imageOne_of

theorem genBasic_holds : GenBasic := @genBasic_of

theorem indDesc_holds : IndDesc := @indDesc_of

theorem sHSec_holds : SHSec := @sHSec_of

theorem finSec_holds : FinSec := @finSec_of @sHSec_holds

theorem imageFin_holds : ImageFin := @imageFin_of @imageOne_holds

theorem ringSplit_holds : RingSplit := @ringSplit_of @finSec_holds @indDesc_holds

theorem locFinAff_holds : LocFinAff := @locFinAff_of @chart_holds @ringSplit_holds

theorem locFinGeo_holds : LocFinGeo := @locFinGeo_of @locFinAff_holds

theorem coverOne_holds : CoverOne := @coverOne_of

theorem locFinSec_holds : LocFinSec := @locFinSec_of @coverOne_holds @locFinGeo_holds

theorem wtBC_holds : WtBC := @wtBC_of

theorem invTrans_holds : InvTrans := @invTrans_of

theorem galTrans_holds : GalTrans := @galTrans_of @invTrans_holds

theorem splitField_holds : SplitField := @splitField_of

theorem sumComp_holds : SumComp := @sumComp_of @fibFin_holds

theorem wtComp_holds : WtComp := @wtComp_of @sumComp_holds @fibFin_holds

theorem splitCover_holds : SplitCover := @splitCover_of @splitField_holds @galTrans_holds

theorem wtLin_holds : WtLin := @wtLin_of @fibFin_holds

theorem countEx_holds : CountEx := @countEx_of

theorem countWt_holds : CountWt := @countWt_of @ptEx_holds @ptLift_holds @fibFin_holds

theorem wtCrit_holds : WtCrit := @wtCrit_of @ptEx_holds

theorem wtClopen_holds : WtClopen := @wtClopen_of @wtCrit_holds @fibFin_holds

theorem artSum_holds : ArtSum := @artSum_of

theorem stalkSum_holds : StalkSum := @stalkSum_of @chart_holds @artSum_holds

theorem multSec_holds : MultSec := @multSec_of

theorem multSumPt_holds : MultSumPt := multSumPt_of stalkSum_holds multSec_holds ptLift_holds ptOne_holds fibFin_holds

theorem multBC_holds : MultBC := @multBC_of

theorem multSum_holds : MultSum := @multSum_of @multSumPt_holds @multBC_holds

theorem multOpen_holds : MultOpen := @multOpen_of

theorem wtFlat_holds : WtFlat := wtFlat_of wtClopen_holds multSum_holds multBC_holds multOpen_holds

theorem multPt_holds : MultPt := @multPt_of @wtFlat_holds @wtPt_holds @multBC_holds

theorem normSpec_holds : NormSpec := normSpec_of splitCover_holds countEx_holds countWt_holds multPt_holds ptEx_holds ptLift_holds genBasic_holds

theorem wtPush_holds : WtPush := @wtPush_of @sumComp_holds @fibFin_holds

theorem wtLocal_holds : WtLocal := @wtLocal_of @wtCrit_holds

theorem normAff_holds : NormAff := @normAff_of @chart_holds @normSpec_holds

theorem nwtOpen_holds : NwtOpen := @nwtOpen_of @wtBC_holds @multBC_holds @genBasic_holds

theorem wtVanish_holds : WtVanish := wtVanish_of isolate_holds wtPt_holds ptEx_holds ptLift_holds fibFin_holds

theorem wtUnique_holds : WtUnique := @wtUnique_of @wtVanish_holds @wtLin_holds

theorem nwtAgree_holds : NwtAgree := nwtAgree_of nwtOpen_holds wtUnique_holds genBasic_holds multBC_holds

theorem nwtGlue_holds : NwtGlue := nwtGlue_of nwtAgree_holds wtLocal_holds multBC_holds genBasic_holds

theorem wtNormal_holds : WtNormal := @wtNormal_of @normAff_holds @nwtGlue_holds

theorem wtDegConst_holds : WtDegConst := @wtDegConst_of @ptEx_holds

theorem nmlInt_holds : NmlInt := @nmlInt_of

theorem nmlNoeth_holds : NmlNoeth := @nmlNoeth_of

theorem nmlLoc_holds : NmlLoc := @nmlLoc_of @nmlInt_holds @nmlNoeth_holds

theorem nwtFlat_holds : NwtFlat := nwtFlat_of wtBC_holds wtFlat_holds wtUnique_holds multBC_holds

theorem multEt_holds : MultEt := @multEt_of

theorem multBasic_holds : MultBasic := @multBasic_of @multBC_holds @multOpen_holds @multEt_holds

theorem nwtOfFlat_holds : NwtOfFlat := @nwtOfFlat_of @wtFlat_holds @wtUnique_holds @genBasic_holds

theorem nwtDeg_holds : NwtDeg := nwtDeg_of wtNormal_holds wtDegConst_holds multSum_holds multBC_holds genBasic_holds

theorem funSec_holds : FunSec := @funSec_of

theorem phiEx_holds : PhiEx := @phiEx_of @locFinSec_holds

theorem fL_holds : FL := @fL_of @phiEx_holds

theorem rpBasic_holds : RpBasic := @rpBasic_of

theorem imgBasic_holds : ImgBasic := @imgBasic_of

theorem rpOp_holds : RpOp := @rpOp_of @imgBasic_holds

theorem opEq_holds : OpEq := @opEq_of @fL_holds @rpBasic_holds @rpOp_holds

theorem secFun_holds : SecFun := @secFun_of @ptEx_holds

theorem sumExLoc_holds : SumExLoc := @sumExLoc_of @secFun_holds @funSec_holds @fibFin_holds

theorem sumNat_holds : SumNat := @sumNat_of

theorem ptInj_holds : PtInj := @ptInj_of @ptEx_holds

theorem sumEx_holds : SumEx := @sumEx_of @sumExLoc_holds @sumNat_holds @ptInj_holds

theorem trSum_holds : TrSum := trSum_of sumEx_holds sumNat_holds ptInj_holds fibFin_holds

theorem trChar_holds : TrChar := @trChar_of @fL_holds @opEq_holds @trSum_holds @ptInj_holds

theorem famSemi_holds : FamSemi := @famSemi_of

theorem redZero_holds : RedZero := @redZero_of

theorem trRed_holds (h : GlobalTheory.EtC.A8) : TrRed := trRed_of h trChar_holds trSum_holds opEq_holds famSemi_holds redZero_holds rpBasic_holds rpOp_holds ptInj_holds fibFin_holds

theorem trHl_holds (h : GlobalTheory.EtC.A8) : TrHl := @trHl_of (@trRed_holds h)

theorem famLin_holds : FamLin := @famLin_of @fibFin_holds

theorem trLin_holds : TrLin := trLin_of trChar_holds famLin_holds wtLin_holds rpBasic_holds rpOp_holds

theorem trIdQ_holds (h : GlobalTheory.EtC.A8) : TrIdQ := @trIdQ_of (@trHl_holds h) @trLin_holds @wtLin_holds

theorem famPush_holds : FamPush := @famPush_of @sumComp_holds @fibFin_holds

theorem trPush_holds : TrPush := trPush_of trChar_holds famPush_holds wtPush_holds rpBasic_holds rpOp_holds

theorem trDeg_holds : TrDeg := @trDeg_of @trPush_holds @trLin_holds

theorem trDegQ_holds (h : GlobalTheory.EtC.A8) : TrDegQ := @trDegQ_of (@trHl_holds h) @trDeg_holds

theorem famComp_holds : FamComp := @famComp_of @sumComp_holds @fibFin_holds

theorem trComp_holds : TrComp := trComp_of trChar_holds famComp_holds wtComp_holds rpBasic_holds rpOp_holds

theorem trCompQ_holds (h : GlobalTheory.EtC.A8) : TrCompQ := trCompQ_of (trHl_holds h) trComp_holds wtComp_holds

theorem famBC_holds : FamBC := @famBC_of

theorem trBC_holds : TrBC := trBC_of trChar_holds famBC_holds wtBC_holds rpBasic_holds rpOp_holds

theorem trBCQ_holds (h : GlobalTheory.EtC.A8) : TrBCQ := trBCQ_of (trHl_holds h) trBC_holds wtBC_holds

theorem trRel_holds : TrRel := @trRel_of @trLin_holds @wtLin_holds @wtVanish_holds

theorem corrEq_holds : CorrEq := corrEq_of imageFin_holds trRel_holds trPush_holds wtPush_holds

theorem corrEqQ_holds (h : GlobalTheory.EtC.A8) : CorrEqQ := @corrEqQ_of (@trHl_holds h) @corrEq_holds

theorem cycComp_holds : CycComp := @cycComp_of @fibFin_holds

theorem corrBCQ_holds (h : GlobalTheory.EtC.A8) : CorrBCQ := @corrBCQ_of (@trBCQ_holds h)

theorem corrCompQ_holds (h : GlobalTheory.EtC.A8) : CorrCompQ := corrCompQ_of cycComp_holds wtBC_holds wtComp_holds (trBCQ_holds h) (trCompQ_holds h)

theorem trSplitQ_holds (h : GlobalTheory.EtC.A8) : TrSplitQ := trSplitQ_of (trBCQ_holds h) (corrEqQ_holds h) (trIdQ_holds h) wtLin_holds wtFlat_holds multBasic_holds

theorem corrGraphQ_holds (h : GlobalTheory.EtC.A8) : CorrGraphQ := @corrGraphQ_of (@trIdQ_holds h) @wtLin_holds

theorem weights_holds : Weights := ⟨wtBC_holds, wtComp_holds, wtLin_holds, wtPush_holds, wtPt_holds, wtUnique_holds, wtDegConst_holds,
    multBasic_holds, multSum_holds, wtFlat_holds, wtNormal_holds, nmlLoc_holds, nwtFlat_holds, nwtOfFlat_holds,
    nwtDeg_holds⟩

theorem torsion_holds : Torsion :=
  ⟨@trSum_holds, @trBC_holds, @trComp_holds, @trLin_holds, @trPush_holds, @trDeg_holds, @corrEq_holds⟩

theorem adic_holds (h : GlobalTheory.EtC.A8) : Adic := ⟨trRed_holds h, trHl_holds h, trBCQ_holds h, trCompQ_holds h, trDegQ_holds h, corrEqQ_holds h, corrBCQ_holds h,
    corrCompQ_holds h, corrGraphQ_holds h, trSplitQ_holds h⟩

end UpperTheory.Gal.TranscendenceTraces
end
