import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceExtendsToIso
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.TieStabKaAtAny
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelProjection
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelSeries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesIndependentAwayFromPlaceOverP
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesAllStepsLtM
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepSuccStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleBasesSpanAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartSuccEqComponentChart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReindexRenamePointDetLatK
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesDataBelowLastStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLawAndFixedCoordinateStabiliserLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteArithmeticGroupMovesFrames
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLatticeTuplePairsAdmissible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddings
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiAlgUnitInert
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.GlobalTheory.GL3.DeterminantNormOneOfUnitDisc
import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedFamilySatisfiesEquivarianceLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SystemWeightsEqShiftedCharacterExponents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLambdaCharacterNormOneIdeleEqPPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTuplePointDetNormOneOrderEqNegLength
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MInvFdOfCharts
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.LocalModelLatticesAdmissibleSmall
import Formalism.LocalToGlobal.GlobalTheory.GL3.IsIntegralOfMemQbar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointDataAtPAndAdelicDatumNonempty

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU

theorem std_at_served : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D), LatTied hT X Y → 2 * rG L.sc ≤ D.R.k → ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (D.gat u w hg).P.m (Y.Fl u w hg).t (Y.Fl u w hg).mm (Y.Fl u w hg).c (D.gat u w hg).P.r ((Y.Fl u w hg).TT v) ((Y.Fl u w hg).a v) ((Y.Fl u w hg).b v) ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) := by
  intro D u w hg L hT X Y hLT hk v
  obtain ⟨hmm, -, -, hr, -⟩ := hLT u w hg
  have hS := (D.gat u w hg).P.setting v
  have hgk := hT.gat_k u w hg
  have hrG : 1 ≤ rG L.sc := Nat.succ_le_succ (Nat.zero_le _)
  have hm2 := D.R.two_le_m
  refine ⟨hg.1, hg.2.1, hS.two_le, hS.even, ?_, ?_, ?_, (Y.Fl u w hg).base v, (D.gat u w hg).P.dom v, ?_, ?_⟩
  · rw [hr]; split_ifs <;> omega
  · rw [hr, hgk]; split_ifs <;> omega
  · rw [hmm]; omega
  · exact fun s => ⟨le_trans (le_max_left _ _) ((Y.Fl u w hg).w_ge v s),
      le_trans (le_max_right _ _) ((Y.Fl u w hg).w_ge v s)⟩
  · exact fun s l hl _ => (Y.Fl u w hg).w_mono v s l hl

end GlobalTheory.TwU
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV.StepDel

theorem del_of_pos : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j, 1 ≤ j → j < D.R.m → S.Del j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hP hPo hL j _ hj
  exact GlobalTheory.T.kernelSite_frameValues_all_steps_lt_m S hD hP hPo hL j hj

end GlobalTheory.TwV.StepDel
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_frameValues_positive_steps : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j, 1 ≤ j → j < D.R.m → S.Del j) := by
  atlas_forward_decl GlobalTheory.TwV.StepDel.del_of_pos
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV.StepZero

theorem del_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → S.Pair → S.Pos → S.Law → S.Del 0) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hP hPos hL
  exact GlobalTheory.T.kernelSite_frameValues_all_steps_lt_m S hD hP hPos hL 0 (by have := GlobalTheory.TwU.m_eq t μ; omega)

end GlobalTheory.TwV.StepZero
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_frameValues_step_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → S.Del 0) := by
  atlas_forward_decl GlobalTheory.TwV.StepZero.del_zero
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

theorem GlobalTheory.TwV.Joint.pt_zero_eq_rat_mul_rep_mul : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), ((sysS H X std).Pj 0).IsLatTup La.2 → ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)), ∃ κ : ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.U, (J.pt std 0 (Nat.zero_le _) La).1 = ratA D.host.F γ * ((J.St 0 (Nat.zero_le _)).y (clsAt X H 0 La.1 La.2)).1 * κ.1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J La hLa
  obtain ⟨-, hA⟩ := GlobalTheory.T.lattice_tuple_adelic_point_step_zero t std J La
  have hb := GlobalTheory.T.lattice_tuple_bases_span_at_places t std J 0 La hLa
  obtain ⟨hγ, κ, hκ⟩ := pt00 J.one La.1 La.2 _ hb _ hA
  have hc : clsAt X H 0 La.1 La.2 = J.e0 (levelZeroClass J.one La.1 La.2) := J.cls0 La.1 La.2 hLa

  obtain ⟨κ', hκ'⟩ := (J.y0 (levelZeroClass J.one La.1 La.2)).imp fun _ h => h.1
  have hU := (J.lev0 (J.chart std 0 (Nat.zero_le _) La)).2.2.1
  have hm : κ'.1⁻¹ * κ.1 ∈ (J.Gd.forms u).cls0.lev.U := Subgroup.mul_mem _ (Subgroup.inv_mem _ κ'.2) κ.2
  refine ⟨rationalElementZero J.one La.1 La.2, hγ, ⟨κ'.1⁻¹ * κ.1, by rw [hU]; exact hm⟩, ?_⟩
  rw [hc, hκ', hκ]
  show _ = _ * _ * (κ'.1⁻¹ * κ.1)
  simp only [mul_assoc, mul_inv_cancel_left]
  rfl
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZero_point_mem_doubleCoset_classRep : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), ((sysS H X std).Pj 0).IsLatTup La.2 → ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)), ∃ κ : ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.U, (J.pt std 0 (Nat.zero_le _) La).1 = ratA D.host.F γ * ((J.St 0 (Nat.zero_le _)).y (clsAt X H 0 La.1 La.2)).1 * κ.1 := by
  atlas_forward_decl GlobalTheory.TwV.Joint.pt_zero_eq_rat_mul_rep_mul
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.TwV.Joint.pt_succ_coset : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj), ∃ κ : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U, (J.pt std (j + 1) hj La).1 = ratA D.host.F γ * ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 * κ.1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La hLa
  have hb := GlobalTheory.T.lattice_tuple_bases_span_at_places t std J (j + 1) La hLa
  obtain ⟨-, -, hU, -, hy⟩ := GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart t std J j hj La hLa
  have hp := (GlobalTheory.T.lattice_tuple_adelic_point_step_succ t std J j hj La).2
  obtain ⟨hc, κ, hγ, e⟩ := kaAt_pt H j hj ((I.at' j hj).st.eC.symm La.1).1 ((I.at' j hj).st.eC.symm La.1).2 La.2 _
    (fun v => hb v) (J.pt std (j + 1) hj La) hp
  have ea : (I.at' j hj).st.eC ⟨((I.at' j hj).st.eC.symm La.1).1, ((I.at' j hj).st.eC.symm La.1).2⟩ = La.1 :=
    Equiv.apply_symm_apply _ _
  have hc' : (I.at' j hj).st.chOf (clsOf (S := (I.at' j hj).st) (H.core j hj) La.1 La.2) = ((I.at' j hj).st.eC.symm La.1).1 := by
    rw [ea] at hc; exact hc
  refine ⟨_, hγ, ⟨κ.1, (SetLike.ext_iff.1 hU κ.1).2 κ.2⟩, ?_⟩
  rw [hy hc']
  have e2 : ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc⟩ =
      ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc'⟩ :=
    congrArg _ (Subtype.ext (congrArg (fun a => clsOf (S := (I.at' j hj).st) (H.core j hj) a La.2) ea))
  rw [← e2]
  exact e
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.succStep_point_mem_doubleCoset_classRep : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj), ∃ κ : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U, (J.pt std (j + 1) hj La).1 = ratA D.host.F γ * ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 * κ.1 := by
  atlas_forward_decl GlobalTheory.TwV.Joint.pt_succ_coset
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

theorem GlobalTheory.kerN_zero_eq_latK_pt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), HEq ((J.fd std).kerN 0 La) (latK D.sp (gramN D 0 (Nat.zero_le _)) J.a (J.pt std 0 (Nat.zero_le _) La).1 ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.Lb) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J La
  obtain ⟨⟨hr, hx⟩, -⟩ := GlobalTheory.T.lattice_tuple_adelic_point_step_zero t std J La
  have hre := GlobalTheory.reindex_rename_point_det_latK D.sp (lev0At J.Gd u w hg).A.rk.symm (gramN D 0 (Nat.zero_le _)) J.a
    (Classical.epsilon fun x => (lev0At J.Gd u w hg).A.IsPt La.1 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om 0 La.2) x ∧
        x ∈ Formalism.UG.UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (lev0At J.Gd u w hg).Lb
  have hpt : (J.pt std 0 (Nat.zero_le _) La).1 = (Classical.epsilon fun x => (lev0At J.Gd u w hg).A.IsPt La.1 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om 0 La.2) x ∧
        x ∈ Formalism.UG.UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [hx]
    exact hre.1
  have hLb : ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.Lb = (lev0At J.Gd u w hg).Lb := (J.lev0 _).1
  rw [hpt, hLb]
  exact hre.2.2
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZero_kernelLattice_eq_pointKernelLattice : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), HEq ((J.fd std).kerN 0 La) (latK D.sp (gramN D 0 (Nat.zero_le _)) J.a (J.pt std 0 (Nat.zero_le _) La).1 ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.Lb) := by
  atlas_forward_decl GlobalTheory.kerN_zero_eq_latK_pt
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.TwV.KerSucc

theorem latK_of_renamed {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N n : ℕ} (h : N = n) (hr : n = N) (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) (Lb Lb₁ : Submodule (𝓞 E) (Fin N → E))
    (J' : Matrix (Fin n) (Fin n) E) (y : GL (Fin n) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) (Lb' : Submodule (𝓞 E) (Fin n → E))
    (hJ : J' = J.reindex (finCongr h) (finCongr h)) (hy : x = Formalism.L2.PairingIndexBounds.F.reGL (finCongr hr) y)
    (hLb : Lb' = Lb.map ((reE (E := E) h).toLinearMap.restrictScalars (𝓞 E))) (h₁ : Lb₁ = Lb) :
    HEq ((latK sp J' a y Lb').map ((reE (E := E) (rfl : n = n)).toLinearMap.restrictScalars (𝓞 E))) (latK sp J a x Lb₁) := by
  have h1 := (GlobalTheory.reindex_rename_point_det_latK sp hr J' a y Lb').1
  have h3 := (GlobalTheory.reindex_rename_point_det_latK sp h J a x Lb).2.2
  have hy' : y = Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) x := by rw [hy]; exact h1.symm
  rw [hJ, hLb, h₁, hy']
  exact h3

section Unfold

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)
  {n0 : ℕ} (A0 : LocAt D.host.F D.host.E n0 (D.gat u w h)) (J0 : Matrix (Fin n0) (Fin n0) D.host.E)
  (Lb0 : Submodule (𝓞 D.host.E) (Fin n0 → D.host.E))
  (Uloc0 : ∀ v : HeightOneSpectrum (𝓞 D.host.F), Subgroup (GL (Fin n0) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)))

theorem gram_succ (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1))
    (hr : D.R.N (i + 1) = ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).m + 1) :
    (cpAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0).J (i + 1) La =
      (Formalism.L2.Forms.gramN D (i + 1) hi).reindex (finCongr hr) (finCongr hr) := by
  show (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).J = _
  rw [chAt, dif_pos hi]

theorem base_succ (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1))
    (hr : D.R.N (i + 1) = ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).m + 1) :
    (cpAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0).Lb (i + 1) La =
      ((I.at' i hi).st.K ((I.at' i hi).st.eC.symm La.1).1).lev.Lb.map
        ((reE (E := D.host.E) hr).toLinearMap.restrictScalars (𝓞 D.host.E)) := by
  show (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).Lb = _
  rw [chAt, dif_pos hi]

end Unfold

end GlobalTheory.TwV.KerSucc

theorem GlobalTheory.TwV.Joint.kerN_succ_heq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → HEq ((J.fd std).kerN (j + 1) La) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La).1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Lb) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La hLa
  obtain ⟨hr, hx⟩ := (GlobalTheory.T.lattice_tuple_adelic_point_step_succ t std J j hj La).1
  have hLb := (GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart t std J j hj La hLa).2.1
  have hJ : (J.cp std).J (j + 1) La = (gramN D (j + 1) hj).reindex (finCongr hr.symm) (finCongr hr.symm) :=
    GlobalTheory.TwV.KerSucc.gram_succ _ _ _ _ _ _ _ _ _ I _ _ _ _ j hj La hr.symm
  have hL : (J.cp std).Lb (j + 1) La = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Lb.map
      ((reE (E := D.host.E) hr.symm).toLinearMap.restrictScalars (𝓞 D.host.E)) :=
    GlobalTheory.TwV.KerSucc.base_succ _ _ _ _ _ _ _ _ _ I _ _ _ _ j hj La hr.symm
  exact GlobalTheory.TwV.KerSucc.latK_of_renamed D.sp hr.symm hr _ J.a _ _ _ _ _ _ hJ hx hL hLb
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.succStep_kernelLattice_eq_pointKernelLattice : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → HEq ((J.fd std).kerN (j + 1) La) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La).1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Lb) := by
  atlas_forward_decl GlobalTheory.TwV.Joint.kerN_succ_heq
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

set_option maxHeartbeats 2000000 in

theorem joint_dt_eq_det_of_isPt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j) x, J.IsPt std j hj La x → (J.fd std).dt j La = Matrix.GeneralLinearGroup.det x.1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La x hx
  obtain ⟨hr, hx⟩ := hx
  have h1 : (J.fd std).dt j La = Matrix.GeneralLinearGroup.det ((J.cp std).y j La) := rfl
  rw [h1, hx]
  exact ((reindex_rename_point_det_latK D.sp hr 0 0 ((J.cp std).y j La) ⊥).2.1).symm

end GlobalTheory
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_tuple_det_eq_adelic_point_det : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j) x, J.IsPt std j hj La x → (J.fd std).dt j La = Matrix.GeneralLinearGroup.det x.1 := by
  atlas_forward_decl GlobalTheory.joint_dt_eq_det_of_isPt
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.joint_dict : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  intro j hj La hLa
  cases j with
  | zero =>
    have hp := (GlobalTheory.T.lattice_tuple_adelic_point_step_zero t std J La).1
    exact ⟨hp, GlobalTheory.T.stepZero_point_mem_doubleCoset_classRep t std J La hLa, GlobalTheory.T.stepZero_kernelLattice_eq_pointKernelLattice t std J La, GlobalTheory.T.lattice_tuple_det_eq_adelic_point_det t std J 0 hj La _ hp⟩
  | succ j =>
    have hp := (GlobalTheory.T.lattice_tuple_adelic_point_step_succ t std J j hj La).1
    exact ⟨hp, GlobalTheory.T.succStep_point_mem_doubleCoset_classRep t std J j hj La hLa, GlobalTheory.T.succStep_kernelLattice_eq_pointKernelLattice t std J j hj La hLa, GlobalTheory.T.lattice_tuple_det_eq_adelic_point_det t std J (j + 1) hj La _ hp⟩
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTuple_joint_dictionary : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std := by
  atlas_forward_decl GlobalTheory.TwV.joint_dict
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.DetIdealUnitary

theorem determinantIdeal_normOne_and_char_unitary_smul : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → IsSDLat D.host.E N L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) ∧ ∀ e : Matrix (Fin N) (Fin N) D.host.E, e * star e = 1 → χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (SDLat.smulLat e L)) = (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ e.det)⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := by
  letI := fun D : D7 => D.host.cmStar
  intro D χ hχ N L hN hsd
  refine ⟨Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N _ _ hN (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N) hsd, ?_⟩
  intro e he
  have hu : e ∈ Matrix.unitaryGroup (Fin N) D.host.E := Matrix.mem_unitaryGroup_iff.2 he
  have h := GlobalTheory.Mem.NatEqui.chi_smulLat hχ (L := L) hsd ⟨e, hu⟩
  rw [Finset.prod_inv_distrib] at h
  exact h

end GlobalTheory.DetIdealUnitary
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinantIdeal_normOne_char_unitary_smul : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → IsSDLat D.host.E N L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) ∧ ∀ e : Matrix (Fin N) (Fin N) D.host.E, e * star e = 1 → χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (SDLat.smulLat e L)) = (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ e.det)⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := by
  atlas_forward_decl GlobalTheory.DetIdealUnitary.determinantIdeal_normOne_and_char_unitary_smul
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.KerInert.ScalM (qbar_zpow_mem lamC_mul_mem lamC_inv_mem lamC_zpow_mem)

noncomputable section

namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000 in

theorem scal_of_pos_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    S.Pos → S.Pair → S.Scal) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS hPos hPair
  obtain ⟨hmm, -, -, -⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  obtain ⟨hp5, -, hIn, -, -, -, hχ, -, -⟩ := S.curve
  have hp2 : D.what₂.places.resChar w ≠ 2 := by omega
  intro j hj L0 hL0 La' hLa'
  have hj' : j < D.R.m := hmm ▸ hj
  have hL0lat : ((sysS H X std).Pj j).IsLatTup L0.2 := Formalism.L2.G.Pend.repOf_lat _ S.hfin j L0 hL0
  obtain ⟨hAdm, -, -, -, -, -, -, -⟩ := hPair j hj L0 La' hL0lat hLa'
  obtain ⟨hN, hN', hsd, hsd'⟩ := hAdm
  obtain ⟨ha, -, hu⟩ := chi_alg_unit_inert D _ S.lam t.χ hχ hp2 hIn _ (GlobalTheory.T.determinantIdeal_normOne_char_unitary_smul D t.χ hχ _ _ hN hsd).1
  obtain ⟨ha', -, hu'⟩ := chi_alg_unit_inert D _ S.lam t.χ hχ hp2 hIn _ (GlobalTheory.T.determinantIdeal_normOne_char_unitary_smul D t.χ hχ _ _ hN' hsd').1
  obtain ⟨hU0, hord0⟩ := GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hS j hj'.le L0 hL0lat
  obtain ⟨hU1, hord1⟩ := GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hS (j + 1) hj' La' hLa'
  have hfill := GlobalTheory.T.systemWeights_eq_shifted_character_exponents S hD hS j hj' La'.1
  have hm1 := S.law.mu_alg j hj' _ hU1
  have hm0 := S.law.mu_alg j hj' _ hU0
  have hn1 := GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow S hD hS hPos j hj' hfill _ hU1
  have hn0 := GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow S hD hS hPos j hj' hfill _ hU0

  have hcf : Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La') ∈ TaylorLogMetric.Qbar := by
    unfold Base.chiFac
    exact TaylorLogMetric.Qbar.mul_mem (qbar_zpow_mem ha _) (qbar_zpow_mem ha' _)
  have hcfn : ‖TaylorLogMetric.lamC S.lam (Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La'))‖ = 1 := by
    unfold Base.chiFac
    rw [lamC_mul_mem S.lam (qbar_zpow_mem ha _) (qbar_zpow_mem ha' _), lamC_zpow_mem S.lam ha,
      lamC_zpow_mem S.lam ha', norm_mul, norm_zpow, norm_zpow, hu, hu', one_zpow, one_zpow, mul_one]
  have hmr : S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹ ∈ TaylorLogMetric.Qbar :=
    TaylorLogMetric.Qbar.mul_mem hm1 (TaylorLogMetric.Qbar.inv_mem hm0)
  refine ⟨?_, ?_⟩
  · unfold KG.scalG
    exact TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _))
      (qbar_zpow_mem ha' _)
  have hexp : TaylorLogMetric.lamC S.lam (KG.scalG (J.fd std) t.χ S.muT j L0 La') =
      TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹) *
        (TaylorLogMetric.lamC S.lam (Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La')))⁻¹ *
        TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j L0))) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) *
        TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN (j + 1) La'))) ^ ((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)) := by
    unfold KG.scalG
    rw [lamC_mul_mem S.lam (TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _))
        (qbar_zpow_mem ha' _),
      lamC_mul_mem S.lam (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _),
      lamC_mul_mem S.lam hmr (TaylorLogMetric.Qbar.inv_mem hcf), lamC_inv_mem S.lam hcf, lamC_zpow_mem S.lam ha, lamC_zpow_mem S.lam ha']
  have hp0 : ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact_mod_cast (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero
  have hB' : ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ KG.expG (sysS H X std) j L0 La' *
      TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹)‖ = 1 := by
    rw [lamC_mul_mem S.lam hm1 (TaylorLogMetric.Qbar.inv_mem hm0), lamC_inv_mem S.lam hm0, norm_mul, norm_mul, norm_inv, norm_zpow,
      hn1, hn0, ← zpow_neg, ← mul_assoc, ← zpow_add₀ hp0, ← zpow_add₀ hp0]
    convert zpow_zero (‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖) using 2
    simp only [hord1, hord0, KG.expG, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun v _ => by ring
  rw [hexp]
  calc ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ KG.expG (sysS H X std) j L0 La' *
        (TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹) *
          (TaylorLogMetric.lamC S.lam (Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La')))⁻¹ *
          TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j L0))) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) *
          TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN (j + 1) La'))) ^ ((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)))‖
      = ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ KG.expG (sysS H X std) j L0 La' *
          TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹)‖ := by
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc, norm_mul, norm_mul, norm_mul, norm_inv, norm_zpow, norm_zpow, hcfn, hu, hu',
          one_zpow, one_zpow, inv_one, mul_one, mul_one, mul_one]
    _ = 1 := hB'
    _ ≤ 1 := le_rfl

end GlobalTheory.TwV.Xc
end
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_scalar_bounded_of_pos_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → S.Pair → S.Scal) := by
  atlas_forward_decl GlobalTheory.TwV.Xc.scal_of_pos_pair
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section
namespace GlobalTheory.TwV

theorem scal_at_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Scal) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hd
  exact GlobalTheory.T.thetaSeries_scalar_bounded_of_pos_pair S hd ⟨J.alg0, J.alg⟩ (pos_at_site S) (GlobalTheory.T.kernelSite_latticeTuplePairs_admissible S hd)

end GlobalTheory.TwV
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_seriesScalar_pow_integral : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Scal) := by
  atlas_forward_decl GlobalTheory.TwV.scal_at_site
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwV

set_option maxHeartbeats 4000000 in

private theorem admissible_at_each_site : Lt.AdmAtEnt2 → AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => DV.Used D μ → OrbitPlaces.Stab0 D → admitted D (sysS H X std) S.Y) := by
  intro hA D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hU hS0
  have hDict := GlobalTheory.T.latticeTuple_joint_dictionary t std J
  have hPair := GlobalTheory.T.kernelSite_latticeTuplePairs_admissible S hDict
  have hPos := GlobalTheory.T.site_place_induces_position_embeddings S
  have hMove := GlobalTheory.T.kernelSite_arithmeticGroup_moves_frames S hDict
  have hAway := GlobalTheory.T.kernelSite_series_independent_away_from_place_over_p S hDict
  have hScal := GlobalTheory.T.kernelSite_seriesScalar_pow_integral S hDict
  have hK1 := GlobalTheory.T.allSites_k1_of_dict_pair_pos_scal S hDict hPair hPos hScal
  obtain ⟨hLaw, hLawIn, hXi⟩ := GlobalTheory.T.kernelSite_law_and_fixedCoordinateStabiliserLaw S hPair hPos hMove hAway
  obtain ⟨ι, hι⟩ := GlobalTheory.ThLoc.place_extends_to_iso _ S.lam
  haveI := Lt.fracAt Gl u w hg
  have key := hA D L hT Gi Gl Kc Dx cX ex t u μ w hg (Gl.Fl u w hg) Lv (chainAt H hT) (kaAt X H hT) std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg))
    (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)))
    (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)))
    (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT))
    (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le)
    S.E S.hfin S.hst S.g S.hLT
    (hT.gat_pos u w hg) ex.tw I (Formalism.L2.PairingIndexBounds.F.lev0At J.Gd u w hg) J.a ∅ t.cc t.δ t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT
  have k2 := key S.curve hK1 hXi hLawIn
  refine k2 ⟨ι.toRingHom, Formalism.L2.KerInert.SecondKernelProjection.rdJ I X.onCh ι.toRingHom, Formalism.L2.KerInert.SecondKernelSeries.srOf S.Y, fun j hj => ⟨J.sharp j hj, ?_, ?_, ?_, ?_⟩⟩
  · have h1 := tieStab_kaAtAny X H hT (chainAt H hT) (chainMu_cmp_K _) std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg)) (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT)) (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le) S.Y hU hS0 j hj.le
    rw [kaAtAny_cls] at h1
    rw [kaAt_cls]
    exact h1
  · refine Formalism.L2.KerInert.SecondKernelProjection.series_reading_entries D L hT Gi Gl Kc Dx cX ex u μ w hg (Gl.Fl u w hg) Lv (chainAt H hT) (labAt X H) I H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds hT (chainMu_cmp_K _) X.onCh std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg)) (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT)) (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le) S.Y ι.toRingHom ?_ j
    intro r
    have hz : D.what₂.embLL r ∈ algebraicClosure ℚ ℂ := by
      rw [mem_algebraicClosure_iff]
      exact (Algebra.IsAlgebraic.isAlgebraic r).algHom D.what₂.embLL.toRatAlgHom
    show ι (D.what₂.embLL r) = S.E.iK (ex.cmp.embW u w hg r)
    rw [S.hK r hz, ← hι]
  · exact Formalism.L2.KerInert.SecondKernelSeries.series_compatibility_of (D.what₂.places.resChar w) _ S.Y j
  · have hD : S.Del j := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        exact GlobalTheory.T.kernelSite_frameValues_step_zero S hDict hPair hPos hLaw
      · exact GlobalTheory.T.kernelSite_frameValues_positive_steps S hDict hPair hPos hLaw j hpos hj
    obtain ⟨cK, hn, hd⟩ := hD ι.toRingHom (fun z => hι z)
    refine ⟨cK, ?_, ?_, ?_, hd⟩
    · show ‖cK‖ ≤ 1
      rw [hn]
    · show ‖cK⁻¹‖ ≤ 1
      rw [norm_inv, hn, inv_one]
    · intro h
      rw [h, norm_zero] at hn
      exact zero_ne_one hn

theorem site_cmpLite_siteAdm : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}, Joint t H X → DV.Used D μ → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → GlobalTheory.TwU.CmpLite D ex.cmp ex.tw u μ w hg (chainAt H hT) ∧ GlobalTheory.TwU.SiteAdm D u w hg (Gl.Fl u w hg) Lv (chainAt H hT) := by
  intro hAdm hCur D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X J hU hS hk
  haveI : Fact (D.what₂.places.resChar w).Prime := ⟨hg.1⟩
  refine ⟨⟨(kaAt X H hT).cmp, (kaAt X H hT).cmp_zero, (kaAt X H hT).cmp_K, (kaAt X H hT).rat, (kaAt X H hT).val⟩, ?_⟩
  have std : Lt.StdAtW D Gl u w hg := GlobalTheory.TwU.std_at_served D u w hg L hT Gi Gl J.tied hk
  obtain ⟨S⟩ := GlobalTheory.T.jointData_at_p_and_adelicDatum_nonempty hCur t std J
  have hA : admitted D (sysS H X std) S.Y := admissible_at_each_site hAdm S hU hS
  refine ⟨inferInstance, std, vpOf (D.gat u w hg), vpOf_irreducible (D.gat u w hg),
    eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)),
    eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)),
    Lt.dGT D u (D.what₂.places.resChar w), Lt.dGT_spec (kaAt X H hT), _, S.Y, hA, Lt.dGT_zero _ _ _, fun j => ?_⟩
  unfold Lt.dGT
  split_ifs <;> simp

end GlobalTheory.TwV

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointSite_chain_compared_carries_admittedSystem : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}, Joint t H X → DV.Used D μ → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → GlobalTheory.TwU.CmpLite D ex.cmp ex.tw u μ w hg (chainAt H hT) ∧ GlobalTheory.TwU.SiteAdm D u w hg (Gl.Fl u w hg) Lv (chainAt H hT) := by
  atlas_forward_decl GlobalTheory.TwV.site_cmpLite_siteAdm
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem modelsOK_of_joints : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex), (∀ μ, DV.Used D μ → JointsAt t μ) → (∀ u, ex.tw.e0 u D.what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _)) → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → GlobalTheory.TwU.ModelsOK D Gl ex.cmp Dx ex.tw := by
  intro hA hC D L hT Gi Gl Kc Dx cX ex t hJ h0 hS hk
  classical
  refine ⟨h0, fun μ u w hg => if h : DV.Used D μ ∧ D.what₂.places.resChar w ∉ Dx.Qp μ then
      ⟨Classical.choose (hJ μ h.1 u w hg h.2),
        chainAt (Classical.choose (Classical.choose_spec (Classical.choose_spec (hJ μ h.1 u w hg h.2)))) hT⟩
    else ⟨Gl.Lv u w hg, Gl.Ch u w hg⟩, ?_⟩
  intro μ hU u w hg hq
  have hP : DV.Used D μ ∧ D.what₂.places.resChar w ∉ Dx.Qp μ := ⟨hU, hq⟩
  dsimp only
  have key : ∀ x : (Σ Lv : Levels (Gl.Fl u w hg), Chain Lv),
      x = ⟨_, chainAt (Classical.choose (Classical.choose_spec (Classical.choose_spec (hJ μ hP.1 u w hg hP.2)))) hT⟩ →
      GlobalTheory.TwU.CmpLite D ex.cmp ex.tw u μ w hg x.2 ∧ GlobalTheory.TwU.SiteAdm D u w hg (Gl.Fl u w hg) x.1 x.2 := by
    rintro x rfl
    exact GlobalTheory.T.jointSite_chain_compared_carries_admittedSystem hA hC t
      (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hJ μ hP.1 u w hg hP.2))))).some
      hU hS hk
  exact key _ (dif_pos hP)

end GlobalTheory.TwV
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLocalModels_of_splitUnramified_joints : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex), (∀ μ, DV.Used D μ → JointsAt t μ) → (∀ u, ex.tw.e0 u D.what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _)) → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → GlobalTheory.TwU.ModelsOK D Gl ex.cmp Dx ex.tw := by
  atlas_forward_decl GlobalTheory.TwV.modelsOK_of_joints
end
