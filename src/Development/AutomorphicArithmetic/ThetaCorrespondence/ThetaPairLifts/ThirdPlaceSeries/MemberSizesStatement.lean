import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConstantsExistForBundleStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConstantsExistForBundle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdmissibleRanksAllMembersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdmissibleRanksAllMembers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HypLAtPointsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeFrameAllMembersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeFrameAllMembers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataNonvanishingAllMembersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataNonvanishingAllMembers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankMuOfBundle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RankConditionAllMembersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LargeGapAllMembersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LargeGapAllMembers

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MemberRanks
theorem admissible_ranks_at_member_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D) := by
  intro hL p
  refine GlobalTheory.Fc.RowE.of_all fun κ K β c b h0 h1 h2 => ?_
  obtain ⟨hv, -⟩ :=
    GlobalTheory.Fc.built_val _root_.GlobalTheory.Fc.BundleCondition (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) κ β.D β.O c b (GlobalTheory.Fc.Built.intro h0 h1 h2)
  exact columnRowRanks_admissible_of_massFormula β.D β.O.lev b.R.T.cols (dstar_mass K β.X β.c.isOver β.c.dsig_eq)
    (GlobalTheory.Proof.ColumnStabilizerTrivialLocal.gBig_of_large (typePrimesLarge_of_val β.O.L hv)) (fun u => GlobalTheory.CollCompare.splits_level β.D u)
end GlobalTheory.MemberRanks
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyMidVolume_at_linked : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D) := by
  atlas_forward_decl _root_.GlobalTheory.MemberRanks.admissible_ranks_at_member_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.MemberData
theorem val_sizes_at_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p)
    (fun κ _ O _ _ => Std κ.C ∧ Val κ.C κ.cD κ.ch O.L ∧ SizesAt O.L) := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb he _ h52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, h1⟩ := szRow_sizesAt eps he h52 C hC
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h2⟩ := h1 cD hcD
  refine ⟨c2, fun ch hch _ => ?_⟩
  obtain ⟨x0, h3⟩ := h2 ch hch
  refine ⟨x0, fun K hK hx β _ c b _ => ?_⟩
  obtain ⟨e1, e2, e3, e4, -⟩ := hK
  have hv : Val C cD ch β.O.L := val_congr e1 e2 e3 (β.p.pt_val β.val)
  have hs : β.O.L.sc = K.s := β.sc
  refine ⟨hC, hv, h3 β.D β.O.L ?_ ?_ hv⟩
  · rw [hs]; exact e4
  · rw [hs]; exact hx
theorem dataNW_of_isGoodE_of_isLinked : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.Core.Deg.DataNW D) := fun hL p =>
  ((_root_.GlobalTheory.Fam.MemberData.val_sizes_at_alt hL p).and (_root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked hL p)).imp fun _ _ β _ _ _ _ _ H =>
    dataNW_of_val H.1.1 β.O.L H.1.2.1 H.1.2.2 H.2
end GlobalTheory.Fam.MemberData
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dataNW_all_linked_good_members : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.Core.Deg.DataNW D) := by
  atlas_forward_decl _root_.GlobalTheory.Fam.MemberData.dataNW_of_isGoodE_of_isLinked
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankMu_all_linked_members : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  first | exact @_root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked | exact _root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked | (intros; apply _root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.MemberFrame
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL)
theorem admissible_ranks_of_mass_alt : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => LocalBesselAndTopKernel.FamilyMidVolume D) :=
  RowE.of_all fun _ K β _ b _ _ _ =>
    admissible_ranks_of_mass_formula β.D β.O.ex.lev b.R.T.toTiedDataS.cols (Dstar_eq_mass K β.X β.c.isOver β.c.dsig_eq)
theorem three_mul_L_le_m_sub_one_and_cGam : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun κ D O _ _ =>
    3 * O.L.sc.L ≤ (D.R.m : ℝ) - 1 ∧ O.L.CGam = κ.C.CGam) := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb _ _ he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ =>
    ⟨0, fun cD _ => ⟨0, fun ch _ _ => ⟨256, fun K hK hx β _ c b _ => ?_⟩⟩⟩⟩⟩
  have hs : β.O.L.sc = K.s := β.sc
  have hc : β.O.L.CGam = C.CGam := β.val.CGam_eq.trans (congrArg Inhab.FC.CGam hK.1)
  have he' : K.s.eps = eps := hK.2.2.2.1
  exact ⟨three_L_le β.val.ranks (by rw [hs, he']; exact he) (by rw [hs]; exact hx), hc⟩
theorem tFrameAt_at_linked : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p)
    (fun _ D _ _ _ => Formalism.L2.SG.RowsConc.TFrameAt D) := by
  have h := ((((_root_.GlobalTheory.Fam.MemberFrame.admissible_ranks_of_mass_alt hL p).and (_root_.GlobalTheory.T.degHypL_all_linked_good_members hL p (fun _ => 29) (fun _ => 0))).and (_root_.GlobalTheory.T.dataNW_all_linked_good_members hL p)).and
    (_root_.GlobalTheory.T.rankMu_all_linked_members hL p)).and (_root_.GlobalTheory.Fam.MemberFrame.three_mul_L_le_m_sub_one_and_cGam hL p)
  refine RowE.imp h ?_
  intro κ K β c b _ _ _ H0
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5, h6⟩ := H0
  have hH : Formalism.MainNotions.S.StandingHypotheses β.D β.O.L (max 29 (8 * κ.C.CGam)) (max 0 40) (κ.C.P.CYL + 1) (1 / 4) 3 (1 / 2) κ.C.CTu :=
    ⟨h6 ▸ le_max_right _ _, h2.2⟩
  exact member_frame_of_standing_hypotheses_window_three β.p.pt.xa.ties h1 ⟨hH, GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu _ h3 h4, by norm_num⟩
    (le_max_left _ _) (le_max_right _ _) h5
theorem tFrameAt_at_linked_of_recT : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.L2.SG.RowsConc.TFrameAt D) :=
  fun hL p => _root_.GlobalTheory.Fam.MemberFrame.tFrameAt_at_linked hL p
end GlobalTheory.Fam.MemberFrame
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_frame_all_members' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.L2.SG.RowsConc.TFrameAt D) := by
  atlas_forward_decl _root_.GlobalTheory.Fam.MemberFrame.tFrameAt_at_linked_of_recT
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Rk.GapAt
theorem rowE_bigGap_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.Core.Rk.BigGap D) := by
  intro hL p
  refine ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ =>
    ⟨11311, fun ch hch _ => ⟨300000 * 4 ^ 30, fun K hK hx β _ _ _ _ => ?_⟩⟩⟩⟩⟩
  show BigGap β.X.toD7
  refine bigGap_of_val β.val ?_ ?_
  · rw [hK.2.2.1]; exact hch
  · rw [β.sc]; exact hx
end GlobalTheory.Core.Rk.GapAt
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigGap_of_isGoodE_isLinked : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.Core.Rk.BigGap D) := by
  atlas_forward_decl _root_.GlobalTheory.Core.Rk.GapAt.rowE_bigGap_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.MemberSizes
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL)
theorem ties_at_alt : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.BasicNotions.Ties D) :=
  RowE.of_all fun _ _ β _ _ _ _ _ => β.p.pt.xa.ties
theorem linked_scale_ge_H_and_cgam_eq (H : Formalism.MainNotions.Inhab.FC → ℝ) : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun κ _ O _ _ =>
    H κ.C ≤ O.L.sc.L ∧ O.L.CGam = κ.C.CGam ∧ 1 ≤ κ.C.CGam) := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb he _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ =>
    ⟨0, fun cD _ => ⟨0, fun ch _ _ => ⟨max 1 (max (H C) 1 ^ eps⁻¹), fun K hK hx β _ c b _ => ?_⟩⟩⟩⟩⟩
  have hG : 1 ≤ C.CGam := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [Inhab.FC.cMid])
  have hs : β.O.L.sc = K.s := β.sc
  have hc : β.O.L.CGam = C.CGam := β.val.CGam_eq.trans (congrArg Inhab.FC.CGam hK.1)
  refine ⟨?_, hc, hG⟩
  show H C ≤ β.O.L.sc.x ^ β.O.L.sc.eps
  rw [hs, hK.2.2.2.1]
  have h1 : 0 ≤ max (H C) 1 := le_trans zero_le_one (le_max_right _ _)
  calc H C ≤ max (H C) 1 := le_max_left _ _
    _ = (max (H C) 1 ^ eps⁻¹) ^ eps := (Real.rpow_inv_rpow h1 he.ne').symm
    _ ≤ K.s.x ^ eps := Real.rpow_le_rpow (Real.rpow_nonneg h1 _) (le_trans (le_max_right _ _) hx) he.le
theorem parameters_scale_rank_gap_bounds (F G H : ℝ → ℝ → ℝ) : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D O _ _ =>
    ∃ C' Cl Cg CT : ℝ, F Cg CT ≤ C' ∧ G Cg CT ≤ Cl ∧ H Cg CT ≤ O.L.sc.L ∧
      GlobalTheory.Core.Rk.HD D O.L.sc.L C' Cl Cg (1 / 4) 3 (1 / 2) CT ∧ GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D O.L.sc.L C' ∧
      (∀ u, GlobalTheory.Core.Rk.RankMu D u) ∧ GlobalTheory.Core.Rk.BigGap D ∧ 1 ≤ D.R.rS) := by
  have h := (((((((_root_.GlobalTheory.Fam.MemberSizes.ties_at_alt hL p).and (_root_.GlobalTheory.T.familyMidVolume_at_linked hL p)).and (_root_.GlobalTheory.T.degHypL_all_linked_good_members hL p (fun C => F (C.P.CYL + 1) C.CTu) (fun C => G (C.P.CYL + 1) C.CTu))).and (_root_.GlobalTheory.T.dataNW_all_linked_good_members hL p)).and (_root_.GlobalTheory.T.type_frame_all_members' hL p)).and (_root_.GlobalTheory.T.rankMu_all_linked_members hL p)).and (_root_.GlobalTheory.T.bigGap_of_isGoodE_isLinked hL p)).and (_root_.GlobalTheory.Fam.MemberSizes.linked_scale_ge_H_and_cgam_eq hL p (fun C => H (C.P.CYL + 1) C.CTu))
  refine RowE.imp h ?_
  intro κ K β c b _ _ _ H0
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8, h9, h10⟩ := H0
  have hm : max (G (κ.C.P.CYL + 1) κ.C.CTu) 40 ≤ (β.D.R.m : ℝ) :=
    h3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨max (F (κ.C.P.CYL + 1) κ.C.CTu) (8 * κ.C.CGam), max (G (κ.C.P.CYL + 1) κ.C.CTu) 40, κ.C.P.CYL + 1, κ.C.CTu,
    le_max_left _ _, le_max_left _ _, h8, ⟨h1, h2, h3, h4, h5⟩, ⟨β.O.L, rfl, h9 ▸ le_max_right _ _, h9 ▸ h10⟩, h6, h7, ?_⟩
  have h40 : (40 : ℝ) ≤ β.D.R.m := le_trans (le_max_right _ _) hm
  have : 40 ≤ β.D.R.m := by exact_mod_cast h40
  show 1 ≤ β.D.R.m / 2 - 1
  omega
theorem parameters_scale_size_bounds_of_member : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (F G H : ℝ → ℝ → ℝ),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D O _ _ => ∃ C' Cl Cg CT : ℝ, F Cg CT ≤ C' ∧ G Cg CT ≤ Cl ∧
      H Cg CT ≤ O.L.sc.L ∧ GlobalTheory.Core.Rk.HD D O.L.sc.L C' Cl Cg (1 / 4) 3 (1 / 2) CT ∧ GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D O.L.sc.L C' ∧
      (∀ u, GlobalTheory.Core.Rk.RankMu D u) ∧ GlobalTheory.Core.Rk.BigGap D ∧ 1 ≤ D.R.rS) :=
  fun hL p F G H => _root_.GlobalTheory.Fam.MemberSizes.parameters_scale_rank_gap_bounds hL p F G H
end GlobalTheory.Fam.MemberSizes
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constants_for_parameters_scale_bundle : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (F G H : ℝ → ℝ → ℝ), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D O _ _ => ∃ C' Cl Cg CT : ℝ, F Cg CT ≤ C' ∧ G Cg CT ≤ Cl ∧ H Cg CT ≤ O.L.sc.L ∧ GlobalTheory.Core.Rk.HD D O.L.sc.L C' Cl Cg (1 / 4) 3 (1 / 2) CT ∧ GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D O.L.sc.L C' ∧ (∀ u, GlobalTheory.Core.Rk.RankMu D u) ∧ GlobalTheory.Core.Rk.BigGap D ∧ 1 ≤ D.R.rS) := by
  atlas_forward_decl _root_.GlobalTheory.Fam.MemberSizes.parameters_scale_size_bounds_of_member
end
end
