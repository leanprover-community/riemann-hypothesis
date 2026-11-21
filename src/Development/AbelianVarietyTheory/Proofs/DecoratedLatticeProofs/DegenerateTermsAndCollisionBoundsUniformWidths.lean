import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DiscreteSeriesDegreeBound
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FinrankLeRankOnAdd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.AutomorphicFormsFiniteUnitaryIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNml
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataChoiceLeaves
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowAmplitudeBoundsUniformSingletonWidth
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AmpUnifPOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopRowSB
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBTheta
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IsLowUnitHBaseVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RMeasExAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeUnipotentIntegralNormalisedHaarStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalBesselJFactorAllWordsOfGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBessel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefWeightedLocUncond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InstFactDecLow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserCovolumeRelevantTermLeHeightPow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsPosTypeP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallOnUnivUnconditional
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InputsOfSubsetWidths
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollSOn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeSizeZ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivIntegral
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CntClLeEncardMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanCountPrimitiveSublatticesOverGenus
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveCorankOneSublatticesBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsRawMassAndGenusMass
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TermSumBoundOfPairsAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanDiagonalOfConditions
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import BuildAid.ForwardExisting
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanCosetSumLe
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsIdentityOfEqualFlags
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovolumeSpans

section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Core.Deg.exists_termLoop_of_standingHypotheses : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (u : D.what₂.Word) (C' Cl Cg cb Cu cT CT : ℝ), 29 ≤ C' → 72 ≤ Cl → Ties D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → ConcTie X Y → ∃ (W : WittDat X) (H : TieHyp W hI) (Am : AmpDat X) (hV : PvalForm W hI Am) (Z : LoopTie D large₂ (termTieOf W hI H Am hV) u u 1), TieAt hF hI large₂ u (termTieOf W hI H Am hV) Z ∧ ∀ t, Z.volR t = Formalism.L2.SG.LoopTerm.volRC hI t := by
  intro D large₂ X Y hF hI u C' Cl Cg cb Cu cT CT hC' hCl hT hS hCT
  haveI : Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow := ⟨GlobalTheory.DecTransport.decLow_main⟩
  haveI : Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc := ⟨GlobalTheory.Sloc.CoefWeighted.coefWeightedLoc_uncond⟩
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D := Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hS (by linarith) hC'
  have hWD : Formalism.L2.SG.WuDecay.WuDecay X := hCT.2.2.2.2.1
  haveI : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  have hB : Formalism.L2.SG.LocWSOf.WuBessel C := Formalism.L2.SG.Pf.wuBesselOfLoc_all C hG GlobalTheory.uniqGap_and_besselOfW.2
    (Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) (fun τ => Formalism.L2.SG.Pf.dsTr C τ) (fun τ => Formalism.L2.SG.Pf.haarTr C τ)
    (fun w τ => Formalism.L2.SG.Pf.colsTypeTr C w τ)
  have hW : ∀ τ, GoodW D τ u u 1 (Formalism.L2.SG.LocWSOf.locW C u u τ) := fun τ =>
    Formalism.L2.SG.LocWSOf.goodW_of C u u τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u τ)
      (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.haarTr C τ)
  have hSS : ∀ τ, GoodS D (lamD D τ) (Formalism.L2.SG.LocWSOf.locS hB u u τ) := fun τ =>
    Formalism.L2.SG.LocWSOf.goodS_of hB u u τ (Formalism.L2.SG.Pf.goodSRest_all hG hT.dsig_tie hB u u τ)
  have hwin : normWin D large₂ 1 1 := Formalism.L2.SG.Pf.LoopBTheta.normWin_one large₂ zero_le_one
  have hCF : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula := GlobalTheory.T.covolume_unipotentIntegral_normalisedHaar
  have hup : Formalism.L2.SG.Pf.LoopBCovN.eN D * Real.log (2 * D.host.v) ≤
      1 * (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b := by
    have h2v : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
    have hrd : Real.log D.host.rdE ≤ large₂.sc.L / Cl := hS.2.2.2.2.2.2.2.2.2.2.1
    have hv0 : 0 ≤ Real.log (2 * D.host.v) := Real.log_nonneg (Formalism.L2.SG.Pf.LoopBCovN.rdE_ge_one D)
    have he := Formalism.L2.SG.Pf.LoopBCovN.eN_le D
    have he0 : 0 ≤ Formalism.L2.SG.Pf.LoopBCovN.eN D := by unfold Formalism.L2.SG.Pf.LoopBCovN.eN; positivity
    rw [Formalism.MainNotions.S.log_scb large₂, h2v]
    rw [h2v] at hv0
    have hCl0 : (0 : ℝ) < Cl := by linarith
    have hL0 : 0 ≤ large₂.sc.L := by
      by_contra hneg
      push_neg at hneg
      have : large₂.sc.L / Cl < 0 := div_neg_of_neg_of_pos hneg hCl0
      linarith
    have h72 : large₂.sc.L / Cl ≤ large₂.sc.L / 72 := div_le_div_of_nonneg_left hL0 (by norm_num) hCl
    have hm0 : 0 ≤ (D.R.m : ℝ) ^ 2 := sq_nonneg _
    calc Formalism.L2.SG.Pf.LoopBCovN.eN D * Real.log D.host.rdE ≤ ((D.R.m : ℝ) ^ 2 / 2) * (large₂.sc.L / 72) :=
          mul_le_mul he (hrd.trans h72) hv0 (by positivity)
      _ ≤ 1 * (D.R.m : ℝ) ^ 2 * large₂.sc.L := by nlinarith
  have hFE := Formalism.L2.SG.LoopsFinal.frameEqvInj_of (Formalism.L2.SG.LoopsTies.wOf X) hI (Formalism.L2.SG.LoopsTies.hOf X Y hF hI)
    (Formalism.L2.SG.LoopsTies.aOfW X Y hF hI hWD) (Formalism.L2.SG.LoopsTies.hvOfW X Y hF hI hWD)
    (Formalism.L2.SG.Pf.LoopBFrame.frameChangeC_holds _ _ _ hF hI _) u u
  have hti := Formalism.L2.SG.LoopsTies.tiesAt X Y hF hI hWD u u
  refine ⟨Formalism.L2.SG.LoopsTies.wOf X, Formalism.L2.SG.LoopsTies.hOf X Y hF hI, Formalism.L2.SG.LoopsTies.aOfW X Y hF hI hWD,
    Formalism.L2.SG.LoopsTies.hvOfW X Y hF hI hWD,
    Formalism.L2.SG.LoopTieOf.loopTieOfParts
      (Formalism.L2.SG.LoopTieOf.loopRowsOf (Formalism.L2.SG.LoopsTies.wOf X) hI (Formalism.L2.SG.LoopsTies.hOf X Y hF hI)
        (Formalism.L2.SG.LoopsTies.aOfW X Y hF hI hWD) (Formalism.L2.SG.LoopsTies.hvOfW X Y hF hI hWD)
        (Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D) u u hFE)
      (Formalism.L2.SG.LoopTerm.locB large₂ 1 C hB u u hwin hW hSS)
      (Formalism.L2.SG.LoopTerm.loopTermOfN (Formalism.L2.SG.LoopsTies.wOf X) hI (Formalism.L2.SG.LoopsTies.hOf X Y hF hI)
        (Formalism.L2.SG.LoopsTies.aOfW X Y hF hI hWD) (Formalism.L2.SG.LoopsTies.hvOfW X Y hF hI hWD) large₂ 1 C hB u u hwin hW hSS
        (GlobalTheory.RMeasAll.rMeasEx_all D X Y hF hI C u u hW)
        (Formalism.L2.SG.Pf.LoopBPin.pinAll_holds u u) (Formalism.L2.SG.Pf.LoopBPin.covolPos_holds u u)
        (GlobalTheory.T.localBesselJFactor_all_words_of_gap D X Y hF hI C hB u u hG)
        (Formalism.L2.SG.Pf.LoopBCovN.covN_pos hCF one_pos C u u)
        (Formalism.L2.SG.Pf.LoopBCovN.covWinN_of hCF C large₂ zero_le_one hup u u) hwin), ?_, fun t => rfl⟩
  exact ⟨Formalism.L2.SG.LoopsFinal.jtPin_of _ hI _ _ _ (Formalism.L2.SG.Pf.FibreCounting.AmpFibreConst_holds Y),
    Formalism.L2.SG.Pf.WittFlags.WRowPin_holds hF hI _ _ _ _,
    Formalism.L2.SG.Pf.FibreCounting.FibreCount_holds Y,
    Formalism.MainNotions.BridgeLemma₂.rows_TermPtsTie_of _ (Formalism.MainNotions.BridgeLemma₂.rows_rdE_pos D) hti.1,
    hti.2.1, hti.2.2, fun t t' hL hE => hFE t t' hL hE⟩

namespace GlobalTheory.Core.Deg

theorem tieOn_singleton_uncond : ∀ c : ℝ, TieOn {c} := by
  intro c Cg cb Cu cT CT
  obtain ⟨C, hCv⟩ := GlobalTheory.T.stabiliserCovolume_relevantTerm_le_heightPow Cg cb Cu cT CT c 1
  refine ⟨C, 72, ?_⟩
  intro C0 hC0 C' Cl hC' hCl D large₂ X Y hF hI u hT hH hCT
  have hC0' : C0 = c := hC0
  subst hC0'
  obtain ⟨W, H, Am, hV, Z, hTie, hvol⟩ :=
    exists_termLoop_of_standingHypotheses D large₂ X Y hF hI u C' Cl Cg cb Cu cT CT (by linarith) hCl hT hH.1 hCT
  refine ⟨_, Z, hTie, ?_⟩
  intro hHyp t hG hr
  rw [hvol t]
  exact hCv D X Y hF hI W H Am hV large₂ u u C' Cl (by linarith) hHyp t hG hr

end GlobalTheory.Core.Deg
end

section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Deg

theorem corankTwoCountBounds_of_rowCountBoundsUniform : ∀ S : Set ℝ, CntOn S → CountBoundOn S := by
  intro S h Cg cb Cu cT CT
  obtain ⟨c3, cH, cS, c4, thr, hthr⟩ := h Cg cb Cu cT CT
  exact ⟨c3, cH, thr, fun C0 hC0 C' Cl h1 h2 D large₂ u =>
    ⟨(hthr C0 hC0 C' Cl h1 h2 D large₂ u).1, (hthr C0 hC0 C' Cl h1 h2 D large₂ u).2.1⟩⟩

end GlobalTheory.Core.Deg
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

theorem cntOn_singleton : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ c : ℝ, CntOn {c} := by
  intro hM c Cg cb Cu cT CT
  obtain ⟨C1a, hC1⟩ := GlobalTheory.Mass.PrimMeanRow.main 1 one_pos
  obtain ⟨c3, hC3⟩ := GlobalTheory.LoopC.PairMean.main Cg cb Cu cT CT c 1 3 (max C1a 0) (le_max_right _ _)
  obtain ⟨cH, -, hHH⟩ := GlobalTheory.GramHeight.height_bounds Cg cb Cu cT CT c 1
  obtain ⟨cS, hSW⟩ := GlobalTheory.LoopC.GenericMean.main Cg cb Cu cT CT c 1
  obtain ⟨c4, hC4⟩ := GlobalTheory.LoopC.Partner.partners_le Cg cb Cu cT CT c 1
  refine ⟨c3, cH, cS, c4, 1, fun C0 hC0 C' Cl _ hl D large₂ u => ?_⟩
  rw [Set.mem_singleton_iff] at hC0
  subst hC0
  refine ⟨fun C hC => ?_, ?_, ?_, ?_⟩
  · exact hC3 C hC _ _ u u _ _ hl (GlobalTheory.Mass.RowsRawMass.main _ u)
      (hC1 _ (le_max_left _ _) _ _ u u _ _ Cg cb Cu cT CT C0 1 hl)
  · exact hHH _ _ u u _ _ hl
  · exact hSW _ _ u u _ _ hl
      (GlobalTheory.Mass.PrimMeanCorankOne.main _ _ u u _ _ Cg cb Cu cT CT C0 1 (Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified hM _))
  · exact hC4 _ _ u u _ _ hl

end GlobalTheory.Core.Deg
end

section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Deg

theorem vanishingGramBound_uniformWindow_and_weightData : (VanishingGramTermsBoundWindow → ∀ c : ℝ, On {c} VanishingGramTermsBound) ∧ (VanishingGramTermsBoundParams → Led1 VanishingGramTermsBound) := by
  refine ⟨fun h c => ?_, fun h => ?_⟩
  · intro Cg cb Cu cT CT h1 h2
    obtain ⟨a, b, H⟩ := h Cg cb Cu cT CT c h1 h2
    refine ⟨max a b, fun C0 hC0 C' Cl hC' hCl D large₂ X Y hF hI u _ t r s d e => ?_⟩
    rw [Set.mem_singleton_iff] at hC0
    subst hC0
    exact H C' Cl (le_trans (le_max_left _ _) hC') (le_trans (le_max_right _ _) hCl) D large₂ X Y hF hI u t r s d e
  · intro Cg cb Cu cT CT h1 h2
    obtain ⟨a, b, H⟩ := h Cg cb Cu cT CT h1 h2
    exact ⟨max a b, fun C' Cl hC' hCl D large₂ X Y hF hI u _ t r s n d e =>
      H C' Cl (le_trans (le_max_left _ _) hC') (le_trans (le_max_right _ _) hCl) D large₂ X Y hF hI u t r s n d e⟩

end GlobalTheory.Core.Deg
end

section
section
noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc
namespace GlobalTheory.Core.Deg

theorem termSumBound_of_pairsAmplitude : TermSumBoundOfPairsAmplitude := by
  intro C' Cl Cg cb Cw cT CT C0 D large₂ X Y u hH hT ha hA
  have hN : NormExpDegC :=
    Formalism.L2.SG.Pf.normExpDegC_of_leaves Formalism.L2.SG.Closed.FinLeviC_holds Formalism.L2.SG.Closed.OOLintSumC_holds
  have hG0 : 0 ≤ (Y.tO u u).Gam1 := ha.2.2.le
  have hPg : 0 ≤ PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hGB : (Y.tO u u).GGBound (PgC Y) :=
    Formalism.L2.SG.TermOp.ggBound Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) Formalism.L2.SG.Closed.TermsGGBound_holds Y.psi_ne
      (fun v => card_ge_three hH.2 Y.TR v)
  refine ⟨ha.1.indicator _, ?_⟩
  exact Formalism.L2.SG.RowsOther.kppDiag_of_pairs (Y.tO u u) Formalism.FourierDecayAlt.P.price_of_index
    Formalism.FourierDecayAlt.P.equal_index Formalism.FourierDecayAlt.P.pair_split_alt Formalism.FourierDecayAlt.P.subfamilyAlt
    (PgC Y) (duC X Y u) D.R.k D.R.f hPg ha
    (Formalism.L2.SG.TermOp.rowOrth Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u))
    (Formalism.L2.SG.KappaOffDiagonal.corankPosC_holds D X Y u u hT) (hN D X Y u hT) hGB
    (Formalism.L2.SG.RowsOther.pairsDeg_of_amp _ hG0 _ _ _ _ hPg hA)

end GlobalTheory.Core.Deg
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_termSumBoundOfPairsAmplitude : GlobalTheory.Core.Deg.TermSumBoundOfPairsAmplitude := by
  atlas_forward_decl GlobalTheory.Core.Deg.termSumBound_of_pairsAmplitude
end

section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc

noncomputable section
open scoped Classical
open Formalism.MainNotions Formalism.MainNotions.KTwoCosetCount Formalism.MainNotions.MinorIntegralityTorus
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem sum_labels_one_record : ∀ (CH C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), 1 ≤ Cl → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E), (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) → ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b (21 + 4 * |CH|) D.R.m D.R.f ^ ((21 + 4 * |CH|) * (D.R.rS : ℝ)) := by
  intro CH C' Cl Cg cb Cw cT CT C0 D large₂ X Y u hCl1 hH j hj T hTm
  have hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1 := by
    intro δ hδ
    obtain ⟨t, -, rfl, rfl⟩ := hTm δ hδ
    exact labFacts_conc t
  have h := kloostermanCosetSum_le Formalism.MainNotions.MinorIntegralityTorus.NormLB_holds Formalism.MainNotions.LatticeSumConvergence.LatSum_holds large₂ hH CH j hj T hfact
  unfold H1C
  refine h.trans ?_
  have hb : 1 ≤ large₂.sc.b := by linarith [KappaEndpoints.two_le_scale_b D large₂]
  have hCl0 : 0 < Cl := by linarith
  have hc0 : 0 ≤ ccOf CH Cl := by unfold ccOf; positivity
  have hcle : ccOf CH Cl ≤ 21 + 4 * |CH| := by
    unfold ccOf
    have : 4 / Cl ≤ 4 := by rw [div_le_iff₀ hCl0]; linarith
    linarith
  unfold Hb
  rw [← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)]
  apply Real.rpow_le_rpow_of_exponent_le hb
  have hx : 0 ≤ (D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS := by positivity
  have e1 : ccOf CH Cl * (D.R.m : ℝ) ^ 2 * D.R.f * (ccOf CH Cl * D.R.rS) =
      ccOf CH Cl * ccOf CH Cl * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS) := by ring
  have e2 : (21 + 4 * |CH|) * (D.R.m : ℝ) ^ 2 * D.R.f * ((21 + 4 * |CH|) * D.R.rS) =
      (21 + 4 * |CH|) * (21 + 4 * |CH|) * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hcle hcle hc0 (by positivity)) hx

end GlobalTheory.Core.Deg
end
end

section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc

noncomputable section

namespace GlobalTheory.Core.Deg

theorem pgC_le_two_at_record : ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X),
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → PgC Y ≤ 2 := by
  intro C' Cl Cg cb Cw cT CT C0 D large₂ X Y hH
  have hPg := Formalism.L2.SG.Pf.SatGram.tt_eq' Formalism.L2.SG.Pf.splitPrimeLoc_holds
    Formalism.L2.SG.Pf.SatGramLoc.reduction_structure_holds Y.TR
  unfold Formalism.L2.SG.RowsConc.PgC
  rw [hPg, Formalism.L2.SG.KappaOffDiagonal.PgLe.finrank_F X]
  obtain ⟨⟨hS0, -, -⟩, hP⟩ := hH
  obtain ⟨-, -, -, hfk, -⟩ := hS0
  have hg := hP.2.1
  have hb := Formalism.MainNotions.KappaEndpoints.two_le_scale_b D large₂
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have h0 := Formalism.L2.SG.KappaOffDiagonal.PgLe.one_factor (D.R.k : ℝ) large₂.sc.b (D.host.g 0 : ℝ) D.R.f hk hb (hg 0).1 hf
  have h1 := Formalism.L2.SG.KappaOffDiagonal.PgLe.one_factor (D.R.k : ℝ) large₂.sc.b (D.host.g 1 : ℝ) D.R.f hk hb (hg 1).1 hf
  calc (1 + 3 / (D.host.g 0 : ℝ)) ^ D.R.f * (1 + 3 / (D.host.g 1 : ℝ)) ^ D.R.f
      ≤ Real.exp (1 / 4) * Real.exp (1 / 4) :=
        mul_le_mul h0 h1 (by positivity) (Real.exp_pos _).le
    _ ≤ 2 := Formalism.L2.SG.KappaOffDiagonal.PgLe.exp_quarter_mul_exp_quarter_le_two

end GlobalTheory.Core.Deg
end
end

section
section
noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc
namespace GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pairsDegOfType_holds : PairsDegOfType := by
  intro CH Ch Cp C hCH hCh hCp hC
  set Cc : ℝ := 21 + 4 * |CH| with hCcdef
  have hCc : 0 ≤ Cc := by positivity
  have hC0 : 0 ≤ C := by linarith
  refine ⟨max 1 (k2C0 (k2Cf C Ch Cc)), fun C' Cl Cg cb Cw cT CT C0 D large₂ X Y u h2 hH hTie tAt => ?_⟩
  have b1 : (1 : ℝ) ≤ Cl := le_trans (le_max_left _ _) h2
  have b5 : k2C0 (k2Cf C Ch Cc) ≤ Cl := le_trans (le_max_right _ _) h2
  have dAt : ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 :=
    fun t ht => delta_pos_le_height_sq (PFHost_of_data D hH.1.2.1) large₂ hCH hC t ht
  have cAt := GlobalTheory.Core.Deg.sum_labels_one_record CH C' Cl Cg cb Cw cT CT C0 D large₂ X Y u b1 hH
  have pg := GlobalTheory.Core.Deg.pgC_le_two_at_record C' Cl Cg cb Cw cT CT C0 D large₂ X Y hH
  obtain ⟨hΓ, hdim⟩ := kappa_off_diagonal_dim_form_C D X Y u hTie
  have hJ := JPosC_holds Cg cb Cw cT CT C0 C' Cl D large₂ X Y u hH hTie
  obtain ⟨hL, -, -, -, hWd, -⟩ := hTie
  have hF := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u
  have hI := Formalism.L2.SG.Closed.OOIntAllC_outright D X Y u u (Formalism.L2.SG.Closed.FoldOKC_outright D X Y u hL hWd)
    (Formalism.L2.SG.Closed.FoldOKC_outright D X Y u hL hWd) hF
  have hIrr := IrrVecC_holds D X Y u hF hI
  have hdpi : 0 ≤ dpiC X u := Nat.cast_nonneg _
  have hmass : 0 ≤ massC Y u := Finset.sum_nonneg fun Λ _ => by unfold wRow; positivity
  have hK : 0 ≤ dpiC X u * massC Y u := mul_nonneg hdpi hmass
  set B := dpiC X u * massC Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 with hB
  set g : GTu Y u × GTu Y u → ℝ := ((Y.tO u u).allPairs (Y.tO u u).degSet).indicator
    (fun p => ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖) with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => Set.indicator_nonneg (fun p _ => by positivity) p
  have hfin : ∀ s : Finset (GTu Y u × GTu Y u), ∑ p ∈ s, g p ≤ B := by
    intro s
    have : ∑ p ∈ s, g p = ∑ p ∈ s.filter (fun p => p ∈ (Y.tO u u).allPairs (Y.tO u u).degSet),
        ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ := by
      rw [Finset.sum_filter]
      rfl
    rw [this]
    exact fin_bound hC0 hCh (le_refl _) hK hIrr hJ tAt dAt cAt _ (fun p hp => (Finset.mem_filter.1 hp).2)
  have hsum : Summable g := summable_of_sum_le hg0 hfin
  have htsum : Formalism.L2.SG.RowsOther.ampSum (Y.tO u u) ((Y.tO u u).allPairs (Y.tO u u).degSet) ≤ B :=
    tsum_le_of_sum_le' (mul_nonneg hK (sq_nonneg _)) hfin
  refine ⟨hsum, ?_⟩
  have hPg0 : 0 ≤ PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hdu : 0 ≤ duC X Y u := Nat.cast_nonneg _
  have hCf : 1 ≤ k2Cf C Ch Cc := by unfold k2Cf; nlinarith [sq_nonneg C, sq_nonneg Ch, sq_nonneg Cc]
  have hk : k2C0 (k2Cf C Ch Cc) * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k := by
    have hL0 : 0 ≤ large₂.sc.L := by
      rw [← log_scale_eq_L]; exact Real.log_nonneg (by linarith [two_le_scale_b large₂ (D := D)])
    have hm6 : 0 ≤ (D.R.m : ℝ) ^ 6 * large₂.sc.L := mul_nonneg (by positivity) hL0
    have := hH.2.1
    calc k2C0 (k2Cf C Ch Cc) * (D.R.m : ℝ) ^ 6 * large₂.sc.L = k2C0 (k2Cf C Ch Cc) * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) := by ring
      _ ≤ Cl * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) := mul_le_mul_of_nonneg_right b5 hm6
      _ = Cl * (D.R.m : ℝ) ^ 6 * large₂.sc.L := by ring
      _ ≤ _ := this
  have hA : (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 ≤ k2B D large₂ (k2Cf C Ch Cc) := by
    unfold k2B
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => kloostermanTermA_nonneg large₂ hC0 hCh hCc j)
      (Finset.sum_le_sum fun j hj => rank_contribution_le large₂ hC0 j hj) 2
  have hclose := final_bound_closes D large₂ (k2Cf C Ch Cc) hCf _ hdu hk
  have hGB : (Y.tO u u).Gam1 * B ≤ duC X Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
    have e : (Y.tO u u).Gam1 * B =
        ((Y.tO u u).Gam1 * massC Y u * dpiC X u) * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
      rw [hB]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hdim (sq_nonneg _)
  calc PgC Y * ((Y.tO u u).Gam1 *
        Formalism.L2.SG.RowsOther.ampSum (Y.tO u u) ((Y.tO u u).allPairs (Y.tO u u).degSet))
      ≤ PgC Y * ((Y.tO u u).Gam1 * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htsum hΓ) hPg0
    _ ≤ PgC Y * (duC X Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2) :=
        mul_le_mul_of_nonneg_left hGB hPg0
    _ ≤ 2 * (duC X Y u * k2B D large₂ (k2Cf C Ch Cc)) :=
        mul_le_mul pg (mul_le_mul_of_nonneg_left hA hdu) (mul_nonneg hdu (sq_nonneg _)) (by norm_num)
    _ = 2 * duC X Y u * k2B D large₂ (k2Cf C Ch Cc) := by ring
    _ ≤ _ := hclose

end GlobalTheory.Core.Deg
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairsAmplitudeBound_of_typeBound : GlobalTheory.Core.Deg.PairsDegOfType := by
  atlas_forward_decl GlobalTheory.Core.Deg.pairsDegOfType_holds
end

section
namespace GlobalTheory.Core.Deg

theorem vanishingGramBoundWindow_of_termPairTypeBound (hT : GlobalTheory.TypeAsm.TypeP) : VanishingGramTermsBoundWindow := by
  intro Cg cb Cu cT CT C0 hcb hcT
  obtain ⟨CH, Ch, Cp, hCH, hCh, hCp, H⟩ := hT Cg cb Cu cT CT C0 hcb hcT
  obtain ⟨C₀, H2⟩ := H (Cp + 4) le_rfl
  obtain ⟨C'₀, Cl₀, H3⟩ := H2 (max C₀ (2 * (CH + 1))) (le_max_left _ _)
  obtain ⟨Cl₁, H4⟩ := GlobalTheory.T.pairsAmplitudeBound_of_typeBound CH Ch Cp (max C₀ (2 * (CH + 1))) hCH hCh hCp (le_max_right _ _)
  refine ⟨max C'₀ 1, max Cl₀ Cl₁, fun C' Cl hC' hCl D large₂ X Y _ _ u hTies _ h0 hC hAbs => ?_⟩
  have hK2 : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 :=
    Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of D large₂ C' Cl Cg cb Cu cT CT C0 h0.2.1 h0.1 h0.2.2 ((le_max_right _ _).trans hC')
  have hType := H3 C' Cl ((le_max_left _ _).trans hC') ((le_max_left _ _).trans hCl) D large₂ X Y u hTies hK2 hC
  have hPairs := H4 C' Cl Cg cb Cu cT CT C0 D large₂ X Y u ((le_max_right _ _).trans hCl) hK2 hC hType
  exact GlobalTheory.T.deg_termSumBoundOfPairsAmplitude C' Cl Cg cb Cu cT CT C0 D large₂ X Y u hK2 hC hAbs hPairs

example : GlobalTheory.TypeAsm.TypeP → GlobalTheory.Core.Deg.VanishingGramTermsBoundWindow := vanishingGramBoundWindow_of_termPairTypeBound

end GlobalTheory.Core.Deg
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem degenerate_and_collisions_uncond : (∀ c : ℝ, On {c} VanishingGramTermsBound) ∧ ∀ c : ℝ, On {c} CollS := by
  have hSM : Formalism.HermitianLatticesTheory.SiegelMassRatio := GlobalTheory.Mass.siegelMassRatio_holds
  have hS : ∀ c : ℝ, SmallOn {c} := fun c =>
    (inputs_of_subset_widths {c} Set.univ (Set.subset_univ _)).2.1 smallOn_univ_unconditional
  have hP : GlobalTheory.TypeAsm.TypeP := GlobalTheory.rowsPos_typeP
  refine ⟨vanishingGramBound_uniformWindow_and_weightData.1 (vanishingGramBoundWindow_of_termPairTypeBound hP), fun c => ?_⟩
  exact collS_on hSM {c} (GlobalTheory.T.rowAmplitudeBoundsUniform_singleton_width c) (corankTwoCountBounds_of_rowCountBoundsUniform {c} (cntOn_singleton hSM c)) (hS c)
    (tieOn_singleton_uncond c)

end GlobalTheory.Core.Deg
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerateTerms_and_collisionBounds_uniform_widths : (∀ c : ℝ, On {c} VanishingGramTermsBound) ∧ ∀ c : ℝ, On {c} CollS := by
  atlas_forward_decl GlobalTheory.Core.Deg.degenerate_and_collisions_uncond
end
