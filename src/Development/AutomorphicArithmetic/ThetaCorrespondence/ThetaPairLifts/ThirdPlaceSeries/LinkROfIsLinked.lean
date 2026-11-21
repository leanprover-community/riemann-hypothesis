import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkedBundlesOfCasselmanWallach
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricWeakTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AllRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodEntriesAtBuiltStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodEntriesAtBuilt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RanksFramesOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RanksFramesClosedStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RanksAndFrameOfTiedClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoopRowOfFiniteDim
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowJOnOfRowHPA
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowAAtGAtBuilt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowRepresentationBasePosition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBOfDecayStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FireStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowHTwOfTie
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieTwRecOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowHServOfLinkStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LPrjSurjAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowCountsOfLabels
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowCountsOfLinkedTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupAllUsedAtPart

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc
theorem six_rows_at_member_alt : ∀ (𝒮 : Slots) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition),
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.ReferenceChainEvaluationAtBundlePoints S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.TwistedPointAtBundlePoints S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.PeriodAtZeroAtBundlePoints S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.TwistedPeriodAtBundlePoints S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.Row_tie S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => AllBundlePointProperties.LevelPrimeColumnValuationsAtBundlePoints S Lk) := by
  intro 𝒮 Lk
  have hC : OverCols (sAnd (IsGoodE 𝒮) fun _ _ _ _ _ => True) :=
    (GlobalTheory.T.goodTwistCores_over_trueColumns 𝒮 (fun _ _ _ _ _ => True)).2
  have hT : LargeBaseCondition KPx (IsBuiltE 𝒮) fun _ _ _ _ _ => True := largeBaseProperty_true
  exact ⟨⟨_, hT, GlobalTheory.T.referenceChainEvaluationAtBundlePoints_of_overCols _ hC _ Lk⟩, ⟨_, hT, GlobalTheory.T.twistedChainEvaluation_rational_integral_bundlePoints _ hC _ Lk⟩,
    ⟨_, hT, GlobalTheory.T.referencePeriodIntegral_bundlePoints_of_overColumns _ hC _ Lk⟩, ⟨_, hT, GlobalTheory.T.twistedPeriods_integral_at_bundlePoints _ hC _ Lk⟩,
    ⟨_, hT, GlobalTheory.T.realSideColumnsCompatible_bundlePoints_overColumns _ hC _ Lk⟩, ⟨_, hT, GlobalTheory.T.levelPrimeColumnValuations_bundlePoints_overColumns _ hC _ Lk⟩⟩
end GlobalTheory.Fc
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_entries_tie_and_level_valuations_at_built : ∀ (𝒮 : Slots) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.ReferenceChainEvaluationAtBundlePoints S Lk) ∧ (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.TwistedPointAtBundlePoints S Lk) ∧ (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.PeriodAtZeroAtBundlePoints S Lk) ∧ (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.TwistedPeriodAtBundlePoints S Lk) ∧ (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.Row_tie S Lk) ∧ (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => AllBundlePointProperties.LevelPrimeColumnValuationsAtBundlePoints S Lk) := by
  atlas_forward_decl _root_.GlobalTheory.Fc.six_rows_at_member_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ranksF_tFrame_closed_of_mass_ratio : (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (𝒞 : FamClass), _root_.Formalism.L2.TwistSelection 𝒞 → (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) ∧ Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 := by
  first | exact @_root_.GlobalTheory.ranks_and_frame_of_tied_class_alt | exact _root_.GlobalTheory.ranks_and_frame_of_tied_class_alt | (intros; apply _root_.GlobalTheory.ranks_and_frame_of_tied_class_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory
theorem bothRowsFromSiegelWeil_alt :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (𝒞 : FamClass), _root_.Formalism.L2.TwistSelection 𝒞 →
      (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) ∧
        Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 :=
  fun hSW => _root_.GlobalTheory.T.ranksF_tFrame_closed_of_mass_ratio (GlobalTheory.T.unitary_hyperplane_volumeRatio_siegelWeil hSW)
end GlobalTheory
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.ThmSOwn
namespace GlobalTheory.LoopRowsByName
theorem loopRows_of_rowsFinDim_alt :
    Formalism.L2.SG.RowsDef.RowsFinDim → (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (𝒞 : FamClass), _root_.Formalism.L2.TwistSelection 𝒞 →
      ∀ sel : SSel 𝒞, (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) → LoopRowS 3 𝒞 sel := by
  intro hFin hUT 𝒞 hT sel hTu
  exact GlobalTheory.T.loopRows_of_large_gap_discreteSeries (GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.T.bessel_multiplicity_one_large_gap_and_whittaker_bessel.1) GlobalTheory.T.bessel_multiplicity_one_large_gap_and_whittaker_bessel.2 GlobalTheory.T.discreteSeriesCoef_pointwiseBound_unconditional
    GlobalTheory.wuDecayOfGap hFin 𝒞 sel hTu (_root_.GlobalTheory.ranks_and_frame_of_tied_class_alt hUT 𝒞 hT).1
end GlobalTheory.LoopRowsByName
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.Cp
namespace GlobalTheory.LocalRows
theorem at_choice_alt (hSW : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent) (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) :
    _root_.GlobalTheory.Fc.R1.SelectionLpBound 𝒜 σ ∧ _root_.GlobalTheory.Fc.R1.SelectionOrderBound 𝒜 σ ∧ R1.H_hTF 𝒜 := by
  let T : _root_.Formalism.L2.TwistSelection (D3 3 𝒜) := fun Fm hc => (_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc)
  have hB := _root_.GlobalTheory.bothRowsFromSiegelWeil_alt hSW (D3 3 𝒜) T
  have hL : _root_.GlobalTheory.Fc.R1.SelectionLpBound 𝒜 σ :=
    _root_.GlobalTheory.LoopRowsByName.loopRows_of_rowsFinDim_alt GlobalTheory.rowsFinDim_link (GlobalTheory.VolRatioFromSiegelWeil.volumeRatio hSW) (D3 3 𝒜) T _ (fun Fm hw => hw.2.2.1)
  exact ⟨hL, GlobalTheory.CarrierGap.offDiag (GlobalTheory.St.swxs_of_siegelWeil hSW) (GlobalTheory.rowNGP_of_siegelWeil hSW) GlobalTheory.rowsFinDim_link (D3 3 𝒜) _
    (fun Fm hc x hx h i => ((_root_.GlobalTheory.Fc.spectralConditionOfRawSelection σ) Fm (d3_a hc) x hx h i).locTied) hB.1 hL, hB.2⟩
theorem sLp_sO_hTF_of_siegelWeil : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), _root_.GlobalTheory.Fc.R1.SlotLpCondition Q Lk ∧ _root_.GlobalTheory.Fc.R1.SlotOrderCondition Q Lk ∧ _root_.GlobalTheory.Fc.R1.SlotTorsionFreeCondition Q Lk := fun hSW Q Lk =>
  ⟨Row.of_sel fun 𝒜 σ _ => (_root_.GlobalTheory.LocalRows.at_choice_alt hSW 𝒜 σ).1, Row.of_sel fun 𝒜 σ _ => (_root_.GlobalTheory.LocalRows.at_choice_alt hSW 𝒜 σ).2.1,
    Row.of_sel fun 𝒜 σ _ => (_root_.GlobalTheory.LocalRows.at_choice_alt hSW 𝒜 σ).2.2⟩
theorem lg1_sLp_sO_hTF : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), (Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotLpCondition S Lk) ∧ (Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotOrderCondition S Lk) ∧ Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotTorsionFreeCondition S Lk := fun hSW KP Q Q' Lk =>
  ⟨⟨_, largeBaseProperty_true, (_root_.GlobalTheory.LocalRows.sLp_sO_hTF_of_siegelWeil hSW _ Lk).1⟩, ⟨_, largeBaseProperty_true, (_root_.GlobalTheory.LocalRows.sLp_sO_hTF_of_siegelWeil hSW _ Lk).2.1⟩, ⟨_, largeBaseProperty_true, (_root_.GlobalTheory.LocalRows.sLp_sO_hTF_of_siegelWeil hSW _ Lk).2.2⟩⟩
end GlobalTheory.LocalRows
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
namespace GlobalTheory.Fc
theorem row_aAtG_at_built_alt (𝒮 : Slots) (hR : 𝒮.Rx = RX) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) :
    Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => AllBundlePointProperties.ArithmeticConditionAtBundlePoints S Lk := by
  refine ⟨fun _ _ _ _ _ => True, largeBaseProperty_true, ?_⟩
  refine GlobalTheory.T.holds_at_bundlePoints_of_trueColumns _ Lk fun K X f T c h => ?_
  refine positionOf_mono (P := GoodE 𝒮) ?_ K X f T c h.1
  rintro K B f T w Z c ⟨⟨b, -⟩, -⟩
  refine ⟨(GlobalTheory.Svd.builtC_hasPart 𝒮).1 K B f T w Z c ⟨b⟩, fun a => ?_⟩
  have hx : RX K B f T w Z c.Wt c.O.p0 b.what₂ := hR ▸ b.rx
  exact GlobalTheory.T.rowFormsMatchPeriodMap_of_furtherProperties K B f T w Z c.Wt c.O.p0 b.what₂ hx a
end GlobalTheory.Fc
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.R1
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem row_hRB_univ_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), _root_.GlobalTheory.Fc.R1.SlotRowBoundCondition Q Lk := by
  intro hDS hHC hRD hCW Q Lk
  refine Row.of_sel fun 𝒜 σ _ _ Fm hc x hx i => ?_
  exact _root_.GlobalTheory.T.indefinite_scale_theta_bound_right_alt hRD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B (Fm.parT x hx i).nV_ge
    (_root_.GlobalTheory.T.indefinite_scale_theta_equality_alt hDS hHC hRD hCW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B).1
end GlobalTheory.Fc.R1
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc
theorem row_hTw_of_tie_alt : ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), Row Q Lk (AtAll _root_.GlobalTheory.Fc.HasCompatibility) → _root_.GlobalTheory.Fc.R1.SlotTwistCondition Q Lk := by
  intro Q Lk h
  refine h.imp fun 𝒜 σ _ hT => ?_
  intro eps Fm hc x hx i
  obtain ⟨t⟩ := hT Fm hc x hx i
  exact _root_.Formalism.L2.Top4.tie_tw_rec_of_real_rec (Q := (σ Fm hc x hx i).B.Q) t.1 (Fm.tw_supp x hx i)
end GlobalTheory.Fc
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.R1.ZLAt
theorem lPrj_surj_at_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (k : Fin D.R.m) :
    Function.Surjective (Formalism.L2.DIV.lPrj D b.P.A3.A b.P.P0 b.P.ψ0 (b.P.A3.fam3.toSub2 b.P.Zs) k b.P.A3.A.μ0).mulVec :=
  GlobalTheory.Mem.LiftProjOnto.lPrj_surjective D b.P.Gp b.P.Pl0 b.P.T b.P.A3.A b.P.P0 b.P.ψ0 (b.P.A3.fam3.toSub2 b.P.Zs) k
    b.P.A3.A.μ0 _ _ _ b.C.ok1.ok2 (b.P.tied.div.mt.forms k b.P.A3.A.μ0)
theorem zL_of_hPA : ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition Q Lk → _root_.GlobalTheory.Fc.R1.SlotZeroLocusCondition Q Lk := by
  intro Q Lk _
  refine Row.of_sel fun 𝒜 σ _ => ?_
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ hc => ⟨0, fun x hx _ _ i k => ?_⟩⟩⟩
  exact _root_.GlobalTheory.Fc.R1.ZLAt.lPrj_surj_at_alt (σ Fm (GlobalTheory.Cp.d3_a hc) x hx i) k
end GlobalTheory.Fc.R1.ZLAt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.Cp
namespace GlobalTheory.CountRow
theorem row_counts_of_ties_alt : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition),
    Row Q Lk (AtAll fun D _ _ _ => ∃ (X : HidaSetting D) (G : GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X),
      AutTie D X.B X.pl ∧ RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι) → _root_.GlobalTheory.Fc.R1.CountsIrreducibilityConstants' Q Lk := by
  intro hSW Q Lk hrow
  obtain ⟨c30, -, h1, -, -, h4⟩ := GlobalTheory.CountConstants.count_constants_of_siegelWeil hSW
  obtain ⟨cIc, hc, H⟩ := GlobalTheory.T.irreducibilityRow_of_concreteAutomorphicData hSW GlobalTheory.rowsFinDim_link
  refine ⟨c30, cIc, h1, hc, hrow.imp fun 𝒜 σ _ hA => ⟨?_, ?_⟩⟩
  · exact Formalism.MainNotions.Pk.Closed.of_class fun Fm _ _ => h4 _ Fm
  · exact H (D3 3 𝒜) (fun Fm hw => hw.2.2.1)
      (Formalism.MainNotions.Pk.Closed.of_class fun Fm _ hw _ => ⟨0, fun x hx _ i => hA Fm (d3_a hw) x hx i⟩)
end GlobalTheory.CountRow
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.CountRowByName
theorem row_counts_of_labels_alt : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), (Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.RL.RowLabelCondition S Lk) → Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.CountsIrreducibilityConstants' S Lk :=
  fun hSW _ _ _ Lk ⟨R, hR, h⟩ => ⟨R, hR, _root_.GlobalTheory.CountRow.row_counts_of_ties_alt hSW _ Lk h⟩
end GlobalTheory.CountRowByName
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.AllAtMemberStage0
section large₂
variable {KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop} {Q Q' : V4.Slot}
theorem forall_linked_bundles_and_alt {Lk : LkT _root_.GlobalTheory.Fc.BundleCondition} {H H' : ∀ 𝒜 : FamClass, RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜 → Prop}
    (h : Lg1 KP Q Q' fun S => Row S Lk H) (h' : Lg1 KP Q Q' fun S => Row S Lk H') :
    Lg1 KP Q Q' fun S => Row S Lk fun 𝒜 σ => H 𝒜 σ ∧ H' 𝒜 σ :=
  RowL.and (KP := KP) (Q := Q) (Q' := Q') h h'
end large₂
theorem linkR_of_isLinked' {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (β : BPt K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition β.D β.O c)
    (h : _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p K β c b) : _root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p K β c b.R := by
  obtain ⟨q, b', ⟨w⟩, e⟩ := h
  refine ⟨q, b'.R, w.recPin, ?_⟩
  exact congrArg (fun t : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => (⟨t.1, t.2.1, t.2.2.R⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c)) e
theorem allRows_of_open0_alt : GlobalTheory.Published.GlobalArtinReciprocity → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.DiscreteSeriesClassification → _root_.GlobalTheory.BigOn.SurjectiveOntoX → _root_.GlobalTheory.BigTop.LambdaLowerBound₂ → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) (NN : FamClass → Prop), _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.S0.CovolumeBoundThirdPlaceSeries → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.S0.FunctionalCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L NN) → _root_.GlobalTheory.Fc.AllRowsAlt KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ)) NN _root_.GlobalTheory.Fc.DefiniteSideCondition := by
  intro hA hSW p1 p2 p3 p4 p5 h3 h4 hL N S Γ NN o hl3 hfun hN
  have six := _root_.GlobalTheory.T.period_entries_tie_and_level_valuations_at_built (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ))
  have hU := GlobalTheory.VolRatioFromSiegelWeil.volumeRatio hSW
  have loc := _root_.GlobalTheory.LocalRows.lg1_sLp_sO_hTF hSW KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ))
  exact
    { hn4 := eventually_coreProperty_of_forall fun Q => (R0.classCountBound_paramsLambda_constructedPoints _ Q _).1
      jOn := eventually_coreProperty_mono o.hPA fun Q h => _root_.GlobalTheory.Fc.JOnBundle.row_jOn_of_row_hPA_alt Q _ h
      hInstR := eventually_coreProperty_of_forall fun Q => GlobalTheory.row_hInstR_of_hU hU _ Q _
      aC2 := eventually_coreProperty_of_forall fun Q => ClassTwoEntries.divisionSecondComplement_constructedPoints _ Q _
      aP10 := six.2.2.2.2.2
      aAtG := _root_.GlobalTheory.Fc.row_aAtG_at_built_alt _ rfl _
      aPt0 := six.1
      aPtTw := six.2.1
      aPer0 := six.2.2.1
      aPerTw := six.2.2.2.1
      tie := six.2.2.2.2.1
      hRB := eventually_coreProperty_of_forall fun Q => _root_.GlobalTheory.Fc.R1.row_hRB_univ_alt p1 p2 p3 p4 Q _
      hTw := eventually_coreProperty_mono o.tie fun Q h => _root_.GlobalTheory.Fc.row_hTw_of_tie_alt Q _ h
      hPA := o.hPA
      hLamP := o.hLamP
      hDivG := o.hDivG
      hDcPtG := o.hDcPtG
      selJ := o.selJ
      sLp := loc.1
      sO := loc.2.1
      hServ := _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (_root_.GlobalTheory.T.hServ_of_linkR hA (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _ (_root_.GlobalTheory.Fc.AllAtMemberStage0.linkR_of_isLinked' _))
      zL := eventually_coreProperty_mono o.hPA fun Q h => _root_.GlobalTheory.Fc.R1.ZLAt.zL_of_hPA Q _ h
      hTF := loc.2.2
      c30 := _root_.GlobalTheory.CountRowByName.row_counts_of_labels_alt hSW KPx _ _ _ o.lab
      rRows := eventually_coreProperty_mono (_root_.GlobalTheory.Fc.AllAtMemberStage0.forall_linked_bundles_and_alt (_root_.GlobalTheory.Fc.AllAtMemberStage0.forall_linked_bundles_and_alt (_root_.GlobalTheory.Fc.AllAtMemberStage0.forall_linked_bundles_and_alt o.hPA o.hDivG) (_root_.GlobalTheory.Fc.AllAtMemberStage0.forall_linked_bundles_and_alt o.good o.geo))
          (_root_.GlobalTheory.Fc.AllAtMemberStage0.forall_linked_bundles_and_alt (_root_.GlobalTheory.Fc.AllAtMemberStage0.forall_linked_bundles_and_alt hl3 hfun) (_root_.GlobalTheory.Fc.AllAtMemberStage0.forall_linked_bundles_and_alt (_root_.GlobalTheory.Fc.AllAtMemberStage0.forall_linked_bundles_and_alt o.mi o.kap) o.df)))
        fun Q h => _root_.GlobalTheory.Fc.StageZeroRow.row_rRows_stage0_alt p1 p2 p3 p4 p5 h3 h4 Q _
          (h.imp fun _ _ _ t => t.1.1.1) (h.imp fun _ _ _ t => t.1.1.2) (h.imp fun _ _ _ t => t.1.2.1)
          (h.imp fun _ _ _ t => t.1.2.2) (h.imp fun _ _ _ t => t.2.1.1) (h.imp fun _ _ _ t => t.2.1.2)
          (h.imp fun _ _ _ t => t.2.2.1.1) (h.imp fun _ _ _ t => t.2.2.1.2) (h.imp fun _ _ _ t => t.2.2.2)
      nRest := hN }
end GlobalTheory.Fc.AllAtMemberStage0
end
end
