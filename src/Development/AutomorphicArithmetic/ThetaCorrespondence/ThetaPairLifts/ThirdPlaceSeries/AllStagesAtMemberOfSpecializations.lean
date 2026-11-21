import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllReductionStatementsHold
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultiplicityOfPrimitive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SRatOfIsotInternal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotOverRows
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityCoverHypotheses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalParameterStableAtUnramifiedPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SLarge
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FinitenessOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SXdAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepsPin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionToLocalLanglandsAStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RayPrimeHostIntegral
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowDepthOfPrimitive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclOfGrpStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowerLeftValuationEqZeroAllStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigTrue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigOfRatAd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GalPolLiftsOfSplit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.OpenUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnrRecOfHasSat
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionSeriesB0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterGridData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalExOfCgTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowCuspMultiplicityInputStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SecondStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideDataOverSetLevelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideDataOverSetLevels
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestageCopyStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SecondBoundOfPrimitive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionSeriesB2
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricHeckeLawsOfMultiplicityLowerBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Lb2OfThetaTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesCoverOfPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesCoverOfPrimitive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelComparisonChoicesExistAtAllPlaces

section
set_option synthInstance.maxHeartbeats 200000

section
section
namespace GlobalTheory.HeightCounting.Up.IsotAtStates
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 2000000 in
theorem isotInternal_of_multEq : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt →
    OverRows fun _ _ _ _ w Z _ _ z p0 Y => RationalReadingWithoutCongruence z.R z.F p0 Y → GlobalTheory.CuspMult.MultEq z.R.toRealDat →
      Formalism.BasicNotions.Rows.IsotInternal (w.st Z).toD7.what₂ := by
  intro hW hDS hN
  refine EvG.imp (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev) fun K _ _ _ _ hHost => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, ?_⟩
  intro B f T hO _ _ _ _ w _ Z Wt hX z p0 Y hHo _ _ hGrp _ hRd hME
  have hH : Formalism.IndefR.Links.HostHyp (w.st Z).toD7 := (hHost (w.st Z) hO).1
  have hGS : Formalism.L2.DIV.GoodStable z.Xg := by
    have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hN.greenC
      (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (w.st Z).toD7) hGrp).2.1
    refine GlobalTheory.Mem.R3.GoodDual.goodStable_of_coeff (w.st Z).B.embLL z.Xg z.good.irr fun g => ?_
    apply (w.st Z).B.embLL.injective
    rw [z.good.2, z.good.2, map_inv, GlobalTheory.Mem.R3.GoodDual.goodIdempotent_coeff_inv_eq_coeff hI]
  have hIR : Formalism.BasicNotions.Rows.IsotRank (w.st Z).toD7.what₂ :=
    GlobalTheory.Mem.R3.isotRank_of_multEq hW hDS hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG _ Y z.pins hHo hH hGS
      (GlobalTheory.CuspDec.cuspDecomp hN.hc hN.decay _) hME
  exact (GlobalTheory.NRows.L0.parts_positive_scalars_without_congruence_lengths hW hDS hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y hRd z.pins hHo hH).1 hIR
set_option maxHeartbeats 2000000 in
theorem isotInternal_at_states : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt →
    AllSt fun _ _ _ _ _ _ x => Formalism.BasicNotions.Rows.IsotInternal (Dof x).what₂ := by
  intro hW hDS hH hN
  have h1 := GlobalTheory.HeightCounting.Up.RowModel.overRows_allSt (_root_.GlobalTheory.HeightCounting.Up.IsotAtStates.isotInternal_of_multEq hW hDS hN)
  have h0 : StepW Start Pinned := StepW.of_all fun _ _ _ _ _ _ _ s => s.1
  refine (StepW.and h1 (h0.trans hH.multL)).trans (StepW.of_all fun K B f T w _ _ hh P x => ?_)
  obtain ⟨hA, hB⟩ := hh
  exact hA P x x.r.Z (hB x.o.Z P.hX P.Wt x.m.z x.fits.grp x.fits.grpAt x.m.exAt x.m.inGeo)
end GlobalTheory.HeightCounting.Up.IsotAtStates
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.UpPin
theorem steps_pin_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, (_root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep → _root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevelExists hL) ∧ (_root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep → _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevelExists hL) ∧
    (_root_.GlobalTheory.HeightCounting.Up.ModuliPointsExistList' hL cDep → _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevelExists hL) ∧ (StepW Start HasBare → _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevelExists hL → SMt → _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL → _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL → _root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep → _root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep →
      _root_.GlobalTheory.HeightCounting.Up.ModuliPointsExistList' hL cDep → _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL → _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep → ∀ (S : SExt) (Γ : GeoP), StepW Start (Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) S Γ).s)) := by
  intro hL cDep
  refine ⟨fun h => h.trans (StepW.of_all ?_), fun h => h.trans (StepW.of_all ?_), fun h => h.trans (StepW.of_all ?_), ?_⟩
  · intro K B f T w _ _ H P x l
    obtain ⟨x', hx', -⟩ := H P x l
    exact ⟨x', hx'⟩
  · intro K B f T w _ _ H P x l
    obtain ⟨x', hx', -⟩ := H P x l
    exact ⟨x', hx'⟩
  · intro K B f T w _ _ H P x l
    obtain ⟨x', hx', -⟩ := H P x l
    exact ⟨x', hx'⟩
  · intro hB hA hMt hRat hCu hB0 hB1 hB2 hC hFin S Γ
    have h := hB.and (hA.and (hMt.and (hRat.and (hCu.and (hB0.and (hB1.and (hB2.and (hC.and hFin))))))))
    refine h.trans (StepW.of_all ?_)
    intro K B f T w _ _ H
    obtain ⟨⟨P, x, hLoc, -⟩, a, mt, rat, cu, b0, b1, b2, c, fin⟩ := H
    obtain ⟨x1, ⟨la⟩, -⟩ := a P x hLoc
    obtain ⟨imt⟩ := mt P x1
    obtain ⟨irat⟩ := rat P x1 la
    have li : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x1 := { toLA := la, mt := imt, rat := irat, cusp := cu P x1 la }
    obtain ⟨x2, ⟨l0⟩, p2⟩ := b0 P x1 li
    obtain ⟨x3, ⟨l1⟩, p3⟩ := b1 P x2 l0
    obtain ⟨x4, ⟨l2⟩, p4⟩ := b2 P x3 l1
    obtain ⟨sc⟩ := c P x4 l2
    obtain ⟨Z, v, -, -⟩ := fin P x4 { toStrictHenselianAcyclic := l2, c := sc } S Γ (p4 (p3 p2))
    exact ⟨Z, ⟨v⟩⟩
end GlobalTheory.HeightCounting.UpPin
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
noncomputable section
namespace GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
theorem sa_of_prN_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → PhtCmp → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevelExists hL := by
  intro hP hC hL
  have hE := _root_.GlobalTheory.T.isRayPrime_g_and_integral_range hP
  have hR := _root_.GlobalTheory.T.depth_of_repOf_of_inputs hP
  have hA := _root_.GlobalTheory.T.types_true_of_ray_class_alt hL hP.what₂.fin hP.what₂.berger hP.greenC hP.what₂.art hP.ray hP.what₂.cheb
  unfold _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevelExists AllSt
  refine StepW.trans (StepW.and hE hR) (StepW.of_all ?_)
  intro K B f T w _ _ hq P x hLoc
  obtain ⟨hEl, hRw⟩ := hq
  obtain ⟨hElem, -, -, h, jE, hfr, hray⟩ := hEl P x
  have e1 : (cfOf x).P = f.P := by
    show w.I.C.P = f.P
    rw [w.C_eq]
  have e2 : (cfOf x).W = f.W := by
    show w.I.C.W = f.W
    rw [w.C_eq]
  have hTy : TypesTrue (Dof x).ntypes (cfOf x).P (cfOf x).W := by
    rw [e1, e2]
    exact x.fits.grp
  obtain ⟨L, hZ, hη, A, hcg, hau, hrow, hTT, hPlG, hplGw, hcA, hcM, hζ, hloc, hO1, hO2, hO3, hO4, hlab⟩ :=
    hA (Dof x) hLoc (cfOf x) jE (repOf x.r.Y) hElem.int hTy (hRw P x) hray
  have hG : GrpTrue (nOfLay x L hZ hη) f := by
    show TypesTrue L.ntypes f.P f.W
    rw [← e1, ← e2]
    exact hTT
  obtain ⟨hGA, hCen⟩ := GlobalTheory.T.heckeGaloisStage_fits_of_same_centre_actions x (nOfLay x L hZ hη) hG hPlG hplGw hcA hcM
  obtain ⟨x', hx', hrep⟩ := GlobalTheory.T.exists_transported_state_heckeGaloisStage x (nOfLay x L hZ hη) hG hGA hCen
  obtain ⟨Pq, hPq1, hPq2⟩ := exists_pq_sel B w.I w.ok
  have hEl' := hEl P x'
  have hRw' := hRw P x'
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at hx'
  subst hx'
  obtain ⟨fr, hfrj⟩ := omFrame_exists_with_jE (setK (Dof x) L hZ hη) jE
  obtain ⟨Wd, hWd⟩ := PhtExt.exists_phtOn_all hC (setK (Dof x) L hZ hη) fr A.wdT A.wd
  let A' : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding (setK (Dof x) L hZ hη) (cfK L hZ hη (cfOf x)) jE := { A with wd := Wd }
  have e := eq_of_heq hrep
  obtain ⟨cg⟩ := hcg
  refine ⟨⟨⟨x.o.η, x.o.hη, x.o.V, x.o.S, nOfLay x L hZ hη, x.o.G⟩, fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩, ⟨⟨⟨⟨h.fr, h.jLL, h.embLL⟩, jE, hfr, A', cg, hau, ?_, fr, hfrj, hWd, hRw', hEl'.1, hEl'.2.1, hlab, hζ, hEl'.2.2.1⟩,
    Pq, hPq1, hPq2⟩⟩, ⟨rfl, HEq.rfl, hloc.symm, hO1.symm, hO2.symm, hO3.symm, hO4.symm, heq_of_eq hPlG.symm⟩⟩
  rw [e]
  exact hrow
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stageASameGalois_of_inputs_phtCmp : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → PhtCmp → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevelExists hL := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.sa_of_prN_alt_alt | exact _root_.GlobalTheory.HeightCounting.Up.sa_of_prN_alt_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.sa_of_prN_alt_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SCuspRows
set_option maxHeartbeats 1000000 in
theorem exists_eigTrue_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (l : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x) (n : InRat x.r.Y x.m.z.cG) :
    ∃ Sb, GlobalTheory.TwInputs.EigTrue (Dof x) (cfOf x) l.a.A.row Sb n.In.eig := by
  obtain ⟨Sb, h1, h2, -⟩ := GlobalTheory.TwInputs.Eig.exists_low (ι := Empty) n.In.Sb (fun i => i.elim) (fun i => i.elim) fun i => i.elim
  have h := _root_.GlobalTheory.TwInputs.Eig.eigTrue_of_read hL x.r.Y x.m.z.lev.is l.a.A.wdT l.a.A.row l.a.row n.rat.eig h1 h2
  have hC : x.m.z.R.C = cfOf x := x.m.z.lev.C
  exact ⟨Sb, (congrArg (fun c : CharFrame (Dof x) => GlobalTheory.TwInputs.EigTrue (Dof x) c l.a.A.row Sb n.In.eig) hC).mp h⟩
end GlobalTheory.SCuspRows
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Polar
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
end Polar
section True
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.WeilDeligne NumberField IsDedekindDomain Polynomial
end GlobalTheory.HeightCounting
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GalAllPlaces
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.WeilDeligne Polynomial
theorem exists_rep_uniform_alt_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : _root_.UpperTheory.GalS.CuspUAlt) {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (ha : 1 ≤ a) (π : D.naut.CG a) (hc : D.naut.csd π)
    (hr : D.naut.ralg π) :
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar l),
      Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
      ∀ w : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → D.naut.unr (D.naut.locG π w) →
        ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B w →
          IsFrob (F := D.host.E) B (normV w) σ →
          ((ρ σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
            galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) := by
  have := host_isCMField D.host
  have hr' : (C.e a π).1.IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [C.inf] at this
  obtain ⟨r, h1, h2, h3⟩ := _root_.UpperTheory.GalS.exists_aw_alt hL hF hG D.nd.Om ι ha (C.e a π).1 ((C.csd a π).1 hc) hr'
  refine ⟨r, h1, fun w hl hu B σ hB hσ => ?_⟩
  have hu' := (D.naut.unr_tw _ ((1 - (a : ℝ)) / 2)).2 hu
  have e : T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) = wdOf (D.nd.plOm.2 w) hl ι r := by
    have hu2 := (T.unr w _).1 hu'
    rw [T.tw, C.loc] at hu2 ⊢
    exact ((h3 w hl _ _).eq_unr hu2).symm
  rw [galPol, T.frobEig w _ hu', e]
  exact frobEig_wdOf hl ι h1 (e ▸ (T.unr w _).1 hu') hB hσ
end GlobalTheory.GalAllPlaces
end
section
namespace GlobalTheory.CsdTwistGal
end GlobalTheory.CsdTwistGal
namespace GlobalTheory.TempSatGal
end GlobalTheory.TempSatGal
end
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.GalAllPlaces
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.WeilDeligne Polynomial
end GlobalTheory.GalAllPlaces
end
noncomputable section
namespace GlobalTheory.GalAllPlaces
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
theorem galPol_lpTw_mem_lifts_eventually : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.GalS.CuspUAlt → GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → ∀ (K : Type) [Field K] (e : K →+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → (∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts e) → ∀ᶠ w in Filter.cofinite, galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts e := by
  intro hL hF hG hCh D T C K _ e π hc hr hsplit
  have ha : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    simp only [Formalism.BasicNotions.Ranks.r]
    omega
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  set P : HeightOneSpectrum (𝓞 D.host.E) → ℂ[X] :=
    fun w => galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) with hP
  have hU : ∀ᶠ w in Filter.cofinite, ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w) :=
    (eventually_natCast_notMem D.host.E 2).and (D.naut.locG_unr_ae π)
  obtain ⟨ρ, hρc, hρ⟩ := _root_.GlobalTheory.GalAllPlaces.exists_rep_uniform_alt_alt hL hF hG C 2 ι ha π hc hr
  letI : Algebra K ℂ := e.toAlgebra
  have key : ∀ γ : ℂ ≃ₐ[K] ℂ, ∀ w, (((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w)) →
      (P w).map (γ : ℂ →+* ℂ) = P w := by
    intro γ
    obtain ⟨ρ', hρ'c, hρ'⟩ := _root_.GlobalTheory.GalAllPlaces.exists_rep_uniform_alt_alt hL hF hG C 2 (ι.trans γ.toRingEquiv) ha π hc hr
    have hfix : ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → (P w).map (γ : ℂ →+* ℂ) = P w :=
      hsplit.mono fun w hw hs => by
        obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).1 (hw hs)
        simp only [hP]
        rw [← hq, Polynomial.map_map]
        congr 1
        ext x
        exact γ.commutes x
    have hall := hU.and hfix
    rw [Filter.eventually_cofinite] at hall
    set S := hall.toFinset with hS
    have hmap : ∀ g, (((ρ' g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)).charpoly.map
        (ι.trans γ.toRingEquiv).toRingHom) = ((((ρ' g : GL (Fin D.R.r) (Qbar 2)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)).charpoly.map ι.toRingHom).map (γ : ℂ →+* ℂ)) := by
      intro g
      rw [Polynomial.map_map]
      rfl
    have heq := GlobalTheory.charpoly_eq_of_eqOn_dense
      (fun g => ((ρ g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)))
      (fun g => ((ρ' g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2))) hρc hρ'c _
      (GlobalTheory.ChebSplitDense.chebSplit_nd hCh D S) (by
        rintro g ⟨w, hwS, hsp, B, hB, hFr⟩
        have hw : (((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w)) ∧
            (IsSplitPl D.host w → (P w).map (γ : ℂ →+* ℂ) = P w) := by
          by_contra h
          exact hwS (by rw [hS, Set.Finite.mem_toFinset]; exact h)
        apply Polynomial.map_injective ι.toRingHom ι.injective
        rw [hρ w hw.1.1 hw.1.2 B g hB hFr]
        apply Polynomial.map_injective (γ : ℂ →+* ℂ) γ.injective
        rw [← hmap, hρ' w hw.1.1 hw.1.2 B g hB hFr, hw.2 hsp])
    intro w hw
    obtain ⟨σ, hσ⟩ := exists_isFrob (D.nd.plOm.2 w)
    have h1 := hρ w hw.1 hw.2 _ σ (D.nd.plOm.2 w) hσ
    have h2 := hρ' w hw.1 hw.2 _ σ (D.nd.plOm.2 w) hσ
    rw [hmap, ← heq σ, h1] at h2
    exact h2
  filter_upwards [hU] with w hw
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  exact GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv ((P w).coeff n) fun γ => by
    have := congrArg (fun p : ℂ[X] => p.coeff n) (key γ w hw)
    simpa [Polynomial.coeff_map] using this
end GlobalTheory.GalAllPlaces
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SCuspRows
theorem sCusp_of_parSt_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.ParameterStatement hL → _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL → _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL := by
  intro hP hL hPar hRat
  refine allSt_mono' (allSt_and' (allSt_and' hPar hRat) (_root_.GlobalTheory.HeightCounting.Up.lowerLeftValuation_eq_zero_all_stages_alt hP)) ?_
  rintro K B f T w P x ⟨⟨hp, he⟩, hv⟩ l j hj1 hj2 σ hσ hg
  obtain ⟨π, hc, hr, hs, -, -, -⟩ := hp l j hj1 hj2 σ hσ hg
  obtain ⟨n⟩ := he l
  obtain ⟨Sb, hn⟩ := _root_.GlobalTheory.SCuspRows.exists_eigTrue_alt l n
  refine ⟨π, hc, hr, hs, ?_⟩
  have h2 := GlobalTheory.CuspFrobSplit.galPol_lifts_ae (Dof x) (cfOf x) l.a.A.row Sb n.In.eig hv hn j hj1 hj2 σ hσ hg π hc hs
  have h4 := _root_.GlobalTheory.GalAllPlaces.galPol_lpTw_mem_lifts_eventually hL hP.what₂.fin hP.what₂.gal hP.what₂.cheb (Dof x) l.a.A.wdT l.a.cg _ (embLL0 (Dof x)) π hc hr h2
  exact (GlobalTheory.TwistLift.galPol_lifts_tw_etaTinv (Dof x) (cfOf x) l.a.A.chr hv π h4).mono fun w hw => (Polynomial.mem_lifts _).1 hw
end GlobalTheory.SCuspRows
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up.GridLg
theorem exists_large_grid_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x =>
    ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) ∧
      (GlobalTheory.BigTop.Fun.lamOf G).Ok ∧ (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x ∧ (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x) := by
  intro _ cDep
  have hd : AllSt fun K _ _ _ _ _ x => ∃ w0, GlobalTheory.LamTie.PlacesOk (Dof x).host (AbsolutelyIrreducibleSpan.q0 (Dof x)) w0 :=
    (Step.of_evLgG GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices).trans (Step.of_all fun K B f T _ hk _ H w _ P x => (H hk T w x.o.Z).2.2.2.2.2.2)
  refine (StepW.and (GlobalTheory.T.exists_grid_unit_gap_field_contains_values cDep) hd).trans (StepW.of_all fun K B f T w _ _ H P x => ?_)
  obtain ⟨G, hG⟩ := H.1 P x
  obtain ⟨w0, h0⟩ := H.2 P x
  exact ⟨G, hG, lamOf_ok _ _ _ _ G w0 h0, x.m.z.lev.C.trans rfl, rfl⟩
end GlobalTheory.HeightCounting.Up.GridLg
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lam_grid_fieldHas_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) ∧ (GlobalTheory.BigTop.Fun.lamOf G).Ok ∧ (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x ∧ (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.GridLg.exists_large_grid_alt | exact _root_.GlobalTheory.HeightCounting.Up.GridLg.exists_large_grid_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.GridLg.exists_large_grid_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_cusp_multiplicity_input_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw) (In : RatIn D S) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (Q : D.what₂.places.Pl → Finset (PlE D.host)), MtInput D M tup Q → (∀ v, NG.OverPl (Pq v) v) → GalEx D → RowCusp D A.row → GlobalTheory.RowTie.ChebSplit D.nd → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → ∃ c0 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T), (∀ (l : ℕ) [Fact l.Prime] j, (c0 l j).1 ≤ (b0 l j).1) → In.Sb ⊆ Sx → (∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx) → (∀ p ∈ low, placesOver D.host.E p ⊆ ↑Sx) → ∃ (F : TwF T) (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw A.bare F (TwL.empty T))) (h0 : _), (∀ i j b, (ex.Bsup i j b).FG ∧ Submodule.span (FractionRing ((T.ntw A.bare F (TwL.empty T)).O i)) (ex.Bsup i j b : Set (ex.Fm i j b)) = ⊤) ∧ ∀ th, Nonempty (SideB (⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).row A.row) low Pq ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).rat S) In.hL In.eig In.θ) := by
  atlas_forward_decl _root_.GlobalTheory.HeightCounting.FormsStep.second_step_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr in
theorem restage_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x)), Nonempty (SideB N.toD7 (N.cf (cfOf x)) (N.row l.a.A.row) (lowAll (Dof x)) l.Pq (N.rat l.rat.S) l.rat.In.hL l.rat.In.eig l.rat.In.θ) → (∀ i, l.rat.In.Sb ⊆ N.tw.S0 i) → (∀ i, OverSet (Dof x) (N.tw.S0 i) (insert (N.tw.l i) (lowAll (Dof x)))) → ∀ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) → (GlobalTheory.BigTop.Fun.lamOf G).Ok → (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x → (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x) → GlobalTheory.LamTie.IsLamTieFull N.tw (GlobalTheory.BigTop.Fun.lamOf G) → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x') ∧ ListSt cDep x' := by
  intro hL cDep K B f T w P x l N hSB hSb hS0 G hF hOk hC hq0 hTie
  obtain ⟨x', l', ho, hLc, hrow, hPq, hS, hSb', hhL, heig, hθ⟩ := _root_.GlobalTheory.T.twisted_state_transport_heq' hL x l N
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at ho
  subst ho
  obtain ⟨sb⟩ := hSB
  have eL : m'.z.R.toRealDat.toLevCh = (by with_unfolding_all exact ((levCh (a := x.o.Z) (oTw x N).Z x.m.z.R.toRealDat.toLevCh) :)) := eq_of_heq hLc
  have hPin : ListPin N.toD7 ((by with_unfolding_all exact ((levCh (a := x.o.Z) (oTw x N).Z x.m.z.R.toRealDat.toLevCh) :)) :
      Formalism.IndefR.Links.LevCh N.toD7 _) cDep K.s.b :=
    ⟨(by with_unfolding_all exact ((GlobalTheory.Mem.GridMove.gdC (a := x.o.Z) (oTw x N).Z G) :)), ⟨(by with_unfolding_all exact (hF.values :)), (by with_unfolding_all exact (hF.roots :))⟩, (by with_unfolding_all exact (hTie :))⟩
  have hLam : ∃ Z : GlobalTheory.LamTie.LamDat N.toD7, Z.Ok ∧ Z.Teich ∧ Z.C = N.cf (cfOf x) ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 N.toD7 ∧
      GlobalTheory.LamTie.IsLamTieFull N.toD7.ntw Z :=
    ⟨(by with_unfolding_all exact ((GlobalTheory.BigTop.Fun.lamOf (GlobalTheory.Mem.GridMove.gdC (a := x.o.Z) (oTw x N).Z G)) :)), ⟨(by with_unfolding_all exact (hOk.places :)), (by with_unfolding_all exact (hOk.aux :)), (by with_unfolding_all exact (hOk.big :))⟩,
      (by with_unfolding_all exact ((GlobalTheory.BigTop.Fun.lamOf_teich (GlobalTheory.Mem.GridMove.gdC (a := x.o.Z) (oTw x N).Z G)) :)),
      (by with_unfolding_all exact ((congrArg (TwNew.cf N) hC) :)), (by with_unfolding_all exact (hq0 :)), (by with_unfolding_all exact (hTie :))⟩
  refine ⟨⟨oTw x N, fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩, ⟨{ toLI := l', b := ?_ }⟩, ?_⟩
  · refine ⟨sideB_congr rfl (eq_of_heq hrow).symm rfl (eq_of_heq hPq).symm (eq_of_heq hS).symm hhL.symm
      (eq_of_heq heig).symm (eq_of_heq hθ).symm sb, fun i => (eq_of_heq hSb') ▸ hSb i, fun i => hS0 i, hLam⟩
  · show ListPin _ m'.z.R.toRealDat.toLevCh cDep K.s.b
    rw [eL]
    exact hPin
end GlobalTheory.HeightCounting.Up
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_data_over_set_levels_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x)), Nonempty (SideB N.toD7 (N.cf (cfOf x)) (N.row l.a.A.row) (lowAll (Dof x)) l.Pq (N.rat l.rat.S) l.rat.In.hL l.rat.In.eig l.rat.In.θ) → (∀ i, l.rat.In.Sb ⊆ N.tw.S0 i) → (∀ i, OverSet (Dof x) (N.tw.S0 i) (insert (N.tw.l i) (lowAll (Dof x)))) → ∀ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) → (GlobalTheory.BigTop.Fun.lamOf G).Ok → (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x → (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x) → GlobalTheory.LamTie.IsLamTieFull N.tw (GlobalTheory.BigTop.Fun.lamOf G) → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x') ∧ ListSt cDep x' := by
  atlas_forward_decl _root_.GlobalTheory.HeightCounting.Up.restage_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
noncomputable section
namespace GlobalTheory.HeightCounting.Up.PointwiseSettings
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
open Formalism.L2.TwC in
theorem pointwise_alt_alt (hPr : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hSer : SerN) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) {K : Ctx} {B : Base}
    {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x)
    (G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩)
    (hF : GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x))) (hOk : (GlobalTheory.BigTop.Fun.lamOf G).Ok)
    (hC : (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x) (hq : (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x)) :
    ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x') ∧ ListSt cDep x' := by
  have hgal : GalEx (Dof x) :=
    _root_.GlobalTheory.HeightCounting.galEx_of_cgTrue_alt hL hPr.what₂.fin hPr.what₂.gal (Dof x) l.a.A.wdT ⟨l.a.cg⟩
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hPr.what₂.cheb (Dof x)
  obtain ⟨c0f, hf⟩ := _root_.GlobalTheory.T.row_cusp_multiplicity_input_alt hPr.what₂.art (Dof x) (cfOf x) l.a.jE l.a.A l.rat.S l.rat.In (lowAll (Dof x)) l.Pq
    l.mt.M _ (QOf P) l.mt.mt l.Pq_over hgal l.cusp hcheb l.a.elem.star l.a.elem.int l.a.elem.split
  have hJ := fun (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 ↥(Dof x).LL0))
      (hv : ((p : ℕ) : 𝓞 ↥(Dof x).LL0) ∈ v.asIdeal) => Formalism.BasicNotions.Examples₂.LB.exists_embAt (l := p) v hv
  obtain ⟨c0r, hr⟩ := GlobalTheory.T.exists_twistRings_characters_classGroups hPr.what₂.art (Dof x) (cfOf x) (fun p _ v hv => (hJ p v hv).choose)
    (fun p _ v hv y => (hJ p v hv).choose_spec y) l.a.val l.a.elem.star l.a.elem.int
  let b0 : Big (Dof x) := fun p _ j =>
    ⟨(c0f p j).1 ⊔ (c0r p j).1, by haveI := (c0f p j).2; haveI := (c0r p j).2; infer_instance⟩
  obtain ⟨Sx, hSx1, hSx2, hSx3⟩ := exists_Sx (Dof x)
  obtain ⟨T', Sp, -⟩ := hr b0 b0 Sx (fun p _ j => le_sup_right)
  have hSbSx : l.rat.In.Sb ⊆ Sx := l.rat.rat.Sb_le.subset hSx1
  obtain ⟨F, ex, h0, hfg, hsb⟩ := hf b0 b0 Sx T' Sp (fun p _ j => le_sup_left) hSbSx hSx3 hSx1
  have hSxS0 : ∀ i, ∀ Q ∈ Sx, Q ∈ T'.S0 i := fun i Q hQ => by
    have h := Sp.ringSpec_excludedPlaces_eq i
    have : Q ∈ (T'.S0 i : Set (HeightOneSpectrum (𝓞 (Dof x).host.E))) := by
      rw [h]; exact Or.inr (Finset.mem_coe.2 hQ)
    exact Finset.mem_coe.1 this
  have hratio : ∀ i, ∀ y ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)),
      ∀ z ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)), ‖y‖ ≤ ‖z‖ →
        y / z ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)) := fun i => by
    have h := GlobalTheory.CycClosure.exists_cyclotomic_integers (T'.l i) (Sp.K0 i) (Sp.Lw i) 0
    have h0 : Kt (T'.l i) (Sp.K0 i) (Sp.Lw i) ⊔ muK (T'.l i) 0 = Kt (T'.l i) (Sp.K0 i) (Sp.Lw i) := by
      rw [h.snd.2.2.2.2.1, sup_bot_eq]
    rw [h0] at h
    exact h.snd.2.2.2.1
  choose iC hiC using fun i => GlobalTheory.Mem.Df.exists_iC_of_clC (T'.l i) (T'.O i) _ (Sp.eO i) (hratio i)
  obtain ⟨L, hLam⟩ := GlobalTheory.T.exists_toricCharacters_in_twistCoefficientRings hPr.what₂.cheb hPr.what₂.art hSer.ratio (Dof x) l.a.A.bare (cfOf x) l.a.A.row
    (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig l.rat.In.θ b0 b0 Sx T' Sp (GlobalTheory.BigTop.Fun.lamOf G) hC hOk
    (GlobalTheory.BigTop.Fun.lamOf_teich G) l.a.val (fun a => hF.values (a.1 + 1) (by omega) a.2)
    (fun i Q hQ => by
      obtain ⟨p, hp, hQp⟩ := GlobalTheory.T.conductor_primes_in_low_set (Dof x) _ hOk hq Q hQ
      exact hSxS0 i Q (Finset.mem_coe.1 (hSx1 p hp hQp)))
  obtain ⟨htie, hside⟩ := hLam F
  obtain ⟨th0⟩ := GlobalTheory.HeightCounting.exists_nth_of_fg_full (Dof x) (T'.ntw l.a.A.bare F (TwL.empty T')) ex
    (fun i => ⟨iC i, hiC i⟩) hfg
  obtain ⟨th1⟩ := GlobalTheory.HeightCounting.exists_nth_of_fg_full (Dof x) (T'.ntw l.a.A.bare F L) { ex with }
    (fun i => ⟨iC i, hiC i⟩) hfg
  have hB := hside ex h0 th0 (hsb th0) th1
  refine _root_.GlobalTheory.T.side_data_over_set_levels_alt hL cDep x l ⟨T'.ntw l.a.A.bare F L, { ex with }, h0, th1, Sp.br, Sp.br_ind⟩ hB
    (fun i => hSbSx.trans fun Q hQ => hSxS0 i Q hQ) (fun i Q hQ => ?_) G hF hOk hC hq htie
  have h := Sp.ringSpec_excludedPlaces_eq i
  have hQ' : Q ∈ (T'.S0 i : Set (HeightOneSpectrum (𝓞 (Dof x).host.E))) := Finset.mem_coe.2 hQ
  rw [h] at hQ'
  simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_coe] at hQ'
  rcases hQ' with (((h1 | ⟨k, h1⟩) | h1) | h1) | h1
  · exact ⟨_, Finset.mem_insert_self _ _, h1⟩
  · refine ⟨(Dof x).host.g k, Finset.mem_insert_of_mem ?_, h1⟩
    fin_cases k <;> simp [lowAll]
  · exact ⟨_, Finset.mem_insert_of_mem (by simp [lowAll]), h1⟩
  · exact ⟨_, Finset.mem_insert_of_mem (by simp [lowAll]), h1⟩
  · obtain ⟨p, hp, hQp⟩ := hSx2 Q h1
    exact ⟨p, Finset.mem_insert_of_mem hp, hQp⟩
theorem settings_forms_exist_list_of_published_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep := by
  intro hPr hSer hL cDep
  exact (_root_.GlobalTheory.T.exists_lam_grid_fieldHas_at_member hPr cDep).trans (StepW.of_all fun K B f T w _ _ h P x l => by
    obtain ⟨G, hF, hOk, hC, hq⟩ := h P x
    exact _root_.GlobalTheory.HeightCounting.Up.PointwiseSettings.pointwise_alt_alt hPr hSer hL cDep x l G hF hOk hC hq)
end GlobalTheory.HeightCounting.Up.PointwiseSettings
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.settingsFormsExistList_of_inputs_serN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.PointwiseSettings.settings_forms_exist_list_of_published_inputs | exact _root_.GlobalTheory.HeightCounting.Up.PointwiseSettings.settings_forms_exist_list_of_published_inputs | (intros; apply _root_.GlobalTheory.HeightCounting.Up.PointwiseSettings.settings_forms_exist_list_of_published_inputs <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr in
theorem points_step_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.ModuliPointsExistList' hL cDep := by
  intro hPr hSer hL cDep
  refine StepW.trans (_root_.GlobalTheory.T.geoLaws_iC_at_levelB1_of_serN hPr hSer hL) (StepW.of_all fun K B f T w _ _ hq P x l => ?_)
  have hlaw := hq P x l
  obtain ⟨x', hl', ho, hLc⟩ := _root_.GlobalTheory.T.exists_levelB2_twist_of_thetaTie hL x l (GlobalTheory.GeoTie.geoNTh hlaw) (GlobalTheory.GeoTie.geoTie hlaw)
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at ho
  subst ho
  refine ⟨⟨oTw x (thTw (Dof x) (GlobalTheory.GeoTie.geoNTh hlaw)), fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩, hl',
    fun hLs => ?_⟩
  obtain ⟨G, hF, hTie⟩ := hLs
  have eL : m'.z.R.toRealDat.toLevCh =
      (by with_unfolding_all exact ((levCh (a := x.o.Z) (oTw x (thTw (Dof x) (GlobalTheory.GeoTie.geoNTh hlaw))).Z x.m.z.R.toRealDat.toLevCh) :)) := eq_of_heq hLc
  show ListPin _ m'.z.R.toRealDat.toLevCh cDep K.s.b
  rw [eL]
  exact ⟨(by with_unfolding_all exact ((GlobalTheory.Mem.GridMove.gdC (a := x.o.Z) (oTw x (thTw (Dof x) (GlobalTheory.GeoTie.geoNTh hlaw))).Z G) :)),
    ⟨(by with_unfolding_all exact (hF.values :)), (by with_unfolding_all exact (hF.roots :))⟩, kc% hTie⟩
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduliPointsExistList_of_inputs_serN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.ModuliPointsExistList' hL cDep := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.points_step_alt_alt | exact _root_.GlobalTheory.HeightCounting.Up.points_step_alt_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.points_step_alt_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ChoiceEx
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
theorem sc_of_sck_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (h : _root_.GlobalTheory.HeightCounting.Up.ThirdStageExists hL) : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL :=
  StepW.trans h (StepW.of_all fun _ _ _ _ _ _ _ H P x l => by
    obtain ⟨s, h1, h2⟩ := exists_settings_conj (D := Dof x) l.a.elem.star l.b.Bs.cover
    obtain ⟨c, -⟩ := H P x l s h1 h2
    exact ⟨c⟩)
end GlobalTheory.HeightCounting.Up.ChoiceEx
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ChoiceEx
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
theorem stage_c_nonempty_of_published_inputs : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL :=
  fun hCo hCW hHM a b hL => _root_.GlobalTheory.HeightCounting.Up.ChoiceEx.sc_of_sck_alt (_root_.GlobalTheory.T.stageCExists_of_casselmanWallach hCo hCW hHM a b hL)
end GlobalTheory.HeightCounting.Up.ChoiceEx
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stage_c_nonempty_of_prints_third_layer : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.ChoiceEx.stage_c_nonempty_of_published_inputs | exact _root_.GlobalTheory.HeightCounting.Up.ChoiceEx.stage_c_nonempty_of_published_inputs | (intros; apply _root_.GlobalTheory.HeightCounting.Up.ChoiceEx.stage_c_nonempty_of_published_inputs <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem all_stages_of_specializations_alt : GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.DiscreteSeriesUpqUnique → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN →
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.ArchimedeanComparison' hL → _root_.GlobalTheory.HeightCounting.Up.PointStatement hL →
    _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevelExists hL ∧ SMt ∧ _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL ∧ _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL ∧ _root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevelExists hL ∧ _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevelExists hL ∧ _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevelExists hL ∧ _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL ∧ _root_.GlobalTheory.HeightCounting.Up.FinitenessStatement hL ∧
      ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep ∧ _root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep ∧ _root_.GlobalTheory.HeightCounting.Up.ModuliPointsExistList' hL cDep ∧ _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep := by
  intro hCW hHM hW hD hU hH hP hS hL hA hPt
  have hMt : SMt := _root_.GlobalTheory.T.sMt_of_published_inputs' hP
  have hRat : _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL := _root_.GlobalTheory.HeightCounting.RatSide.sRat_of_isotInternal_inputs hU hP hS (_root_.GlobalTheory.HeightCounting.Up.IsotAtStates.isotInternal_at_states hW hD hH hP) hL
  have hPar : _root_.GlobalTheory.HeightCounting.Up.ParameterStatement hL := _root_.GlobalTheory.T.parSt_of_third_layer_sMt hP hMt hL
  have hEta : _root_.GlobalTheory.HeightCounting.Up.EtaStatement' hL := _root_.GlobalTheory.StEta.sEta_alt_alt_alt hP hL hPt
  have hFin := _root_.GlobalTheory.T.sFin_and_sFinl_of_archCmp_sEta_thetaData hW hD hP hL hA hEta (_root_.GlobalTheory.HeightCounting.Up.sXd_all_alt hL)
  have hG := _root_.GlobalTheory.HeightCounting.UpPin.steps_pin_alt hL 0
  refine ⟨_root_.GlobalTheory.T.stageASameGalois_of_inputs_phtCmp hP hA.pht hL, hMt, hRat, _root_.GlobalTheory.SCuspRows.sCusp_of_parSt_alt_alt hP hL hPar hRat, hG.1 (_root_.GlobalTheory.T.settingsFormsExistList_of_inputs_serN hP hS hL 0),
    hG.2.1 (_root_.GlobalTheory.T.seriesExistList_of_inputs_serN hP hS hL 0), hG.2.2.1 (_root_.GlobalTheory.T.moduliPointsExistList_of_inputs_serN hP hS hL 0), _root_.GlobalTheory.T.stage_c_nonempty_of_prints_third_layer hH.cover hCW hHM hP hS hL, hFin.1, fun c => ?_⟩
  exact ⟨_root_.GlobalTheory.T.settingsFormsExistList_of_inputs_serN hP hS hL c, _root_.GlobalTheory.T.seriesExistList_of_inputs_serN hP hS hL c, _root_.GlobalTheory.T.moduliPointsExistList_of_inputs_serN hP hS hL c, hFin.2 c⟩
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.all_stages_at_member_of_specializations_alt : GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.DiscreteSeriesUpqUnique → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.ArchimedeanComparison' hL → _root_.GlobalTheory.HeightCounting.Up.PointStatement hL → _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevelExists hL ∧ SMt ∧ _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL ∧ _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL ∧ _root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevelExists hL ∧ _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevelExists hL ∧ _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevelExists hL ∧ _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL ∧ _root_.GlobalTheory.HeightCounting.Up.FinitenessStatement hL ∧ ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep ∧ _root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep ∧ _root_.GlobalTheory.HeightCounting.Up.ModuliPointsExistList' hL cDep ∧ _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.all_stages_of_specializations_alt | exact _root_.GlobalTheory.HeightCounting.Up.all_stages_of_specializations_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.all_stages_of_specializations_alt <;> assumption)
end
end
end
