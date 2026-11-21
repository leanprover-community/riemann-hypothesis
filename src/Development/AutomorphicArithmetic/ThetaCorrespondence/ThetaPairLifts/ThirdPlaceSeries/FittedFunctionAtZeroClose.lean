import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquareTopTermJoinedEstimates
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SumSizeFiniteAwayArchimedeanCombined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.JoinedLocalSumEstimates
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedConvergenceWithRealPlaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeAtHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeAtHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetAtOfSizeAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetAtOfSizeAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivLOneBoundFamily
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThmAUpperStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomTripleIntegralEqConstMulLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareRatioInEmbeddingRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleOfRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingFunctionBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingFunctionBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExOfClaimsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityAtFittedPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityAtFittedPoints
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneMapOfRowsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KerEqOfFormulaStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafFixedPointOfFinKAwayKStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpaTieStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpbOfLamLowStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneSqTieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorFittedIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorFittedIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GBigAtTiedStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IntTieStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ArchTieStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThbTieStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtTieStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DesHLeaf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RamifiedSumsFifthBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsSeventhEstimateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsSeventhEstimate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DesPolStatement

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun.SizeProof
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Sizes
variable {D : D7} {L : SizeData₂ D}
end Sizes
section Main
variable {D : D7} {L : SizeData₂ D}
theorem sizeAt_alt : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt :=
  ⟨1, one_pos, fun _ he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hF _ =>
    let ⟨x₀, h⟩ := sizeRows_fam he Fm hF
    ⟨x₀, fun x hx h0 i _ _ => h x hx h0 i⟩⟩⟩
end Main
end GlobalTheory.BigTop.Fun.SizeProof
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_at' : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt := by
  atlas_forward_decl _root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun.SetFromSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
set_option maxHeartbeats 1600000 in
theorem setting_of_size_alt (p : PtAt ex Csz) (hp : p.PointConditions') (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) (he : GlobalTheory.GLq.ESerTie D) :
    HidaSetting L p.R.toRealDat p.F.lv2 :=
  setting_of_exAt p hp.exAt hs he
end GlobalTheory.BigTop.Fun.SetFromSize
namespace GlobalTheory.BigTop.Fun
theorem setAt_of_sizeAt_alt (h : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt) : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint :=
  h.imp fun _ _ _ a => _root_.GlobalTheory.BigTop.Fun.evPt_mono a fun _ _ _ p hp b he => _root_.GlobalTheory.BigTop.Fun.SetFromSize.setting_of_size_alt p hp b he
end GlobalTheory.BigTop.Fun
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.set_at_of_size_at' : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint := by
  atlas_forward_decl _root_.GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
namespace GlobalTheory
theorem logDeriv_LFunction_at_one_le_along_family_alt :
    _root_.GlobalTheory.FunPr.ThetaLocalInputs → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ =>
      |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) := by
  intro _
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  exact ⟨0, fun x hx _ i _ _ => (Fm.params x hx i).logDerivative_le_power⟩
end GlobalTheory
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_logDerivativeAtOne_le_x_rpow_eps : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) := by
  first | exact @_root_.GlobalTheory.logDeriv_LFunction_at_one_le_along_family_alt | exact _root_.GlobalTheory.logDeriv_LFunction_at_one_le_along_family_alt | (intros; apply _root_.GlobalTheory.logDeriv_LFunction_at_one_le_along_family_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2 Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1600000 in
theorem square_ratio_at_point_of_leading_term_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.RowClaim.ConstK → LNe → TriEx → Tower → (_root_.GlobalTheory.BigTop.Fun.CharacterAtPoint fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ i j t, GlobalTheory.RowTest.sqRatio ch i j t ∈ Set.range D.what₂.embLL) := by
  intro hP hAg hMa hSet hdl hC hLN hTX hTW
  have hBF := _root_.GlobalTheory.T.bottom_triple_integral_eq_const_mul_local hP hAg hMa hLN
  obtain ⟨c3, h3⟩ := hSet.atPt hC
  obtain ⟨c5, h5⟩ := Model.gBig_and (Model.gBig_and hLN hTX) (Model.gBig_and hTW hBF)
  refine ⟨max c3 c5, fun CF hCF => ?_⟩
  have k3 : c3 ≤ CF := le_trans (by simp) hCF
  have k5 : c5 ≤ CF := le_trans (by simp) hCF
  obtain ⟨e0, he0, H⟩ := (h3 CF k3).and (hdl.and hSet)
  refine ⟨e0, he0, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := H eps he hle
  obtain ⟨C0, x₀, hg⟩ := h5 eps CF k5
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨y3, g3⟩, ⟨y5, g5⟩, ⟨y6, g6⟩⟩ := hK Fm CH hc hL
  refine ⟨max (max y3 y5) (max y6 x₀), fun x hx hle i p hp G W n a ha => ?_⟩
  have l3 : y3 ≤ x := le_trans (by simp) hle
  have l5 : y5 ≤ x := le_trans (by simp) hle
  have l6 : y6 ≤ x := le_trans (by simp) hle
  have l7 : x₀ ≤ x := le_trans (by simp) hle
  have hset := g6 x hx l6 i p hp ha.eser
  have hrec : Rec (Fm.L x i) := ⟨hset.size, hset.host, hset.hF, g5 x hx l5 i p hp⟩
  obtain ⟨⟨hLN', hTX'⟩, hTW', hBF'⟩ := hg C0 le_rfl _ (Fm.L x i) (Fm.L_eps x i)
    (by rw [Fm.L_x x i hx]; exact l7) hrec _ _ _ hset.core.lev G
  have hc := g3 x hx l3 i p hp G W n a ha
  have hstd : IsStdChar (Fm.D x i) W.ψ (-1) := (ha.is.weil.ψ : a.ch.W.ψ = _) ▸ hset.std
  exact fun i' j' t => sqRatio_mem_of G _ W a.S.toGridChoice a.rm a.c hstd ha.field hc ha.is.const
    (fun i j => (hLN' i j).1) (hTX' W hstd) (hTW' W a.S.toGridChoice a.rm hstd ha.field) (hBF' W hstd) i' j' t
end GlobalTheory.BigTop.Fun
end
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_ratio_mem_range_emb_ll : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.RowClaim.ConstK → LNe → TriEx → Tower → (_root_.GlobalTheory.BigTop.Fun.CharacterAtPoint fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ i j t, GlobalTheory.RowTest.sqRatio ch i j t ∈ Set.range D.what₂.embLL) := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.square_ratio_at_point_of_leading_term_alt | exact _root_.GlobalTheory.BigTop.Fun.square_ratio_at_point_of_leading_term_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.square_ratio_at_point_of_leading_term_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
noncomputable section
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem bundle_of_rows_alt : _root_.GlobalTheory.BigTop.Fun.BundleCondition := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp
  have hR := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  exact ⟨hR.wf false, Formalism.IndefR.Links.primRows3 hp.ok hp.sep p.R p.F p.charW hp.prim,
    Formalism.IndefR.Links.primRows3_data hp.ok hp.sep p.charW hp.prim⟩
end GlobalTheory.BigTop.Fun
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Filter Asymptotics
namespace GlobalTheory.BigTop.Fun
theorem existsIntegralMultiple_holds_alt : _root_.GlobalTheory.BigTop.Fun.ScaleCondition := by
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := exists_log_le_two_rpow he
  refine ⟨x0, fun x hx hle i p _ => ?_⟩
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hx1 : 1 < x := Fm.one_lt_family_threshold.trans hx
  have hZx : p.Z.x = x := hsx
  have hZb : p.Z.b = Real.exp (x ^ eps) := by
    show Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) = _
    rw [hsx, hse]
  show 1 ≤ p.Z.x ∧ 1 ≤ Real.log p.Z.b ∧ Real.log p.Z.b + Real.log p.Z.x ≤ 3 * Real.log p.Z.b
  rw [hZx, hZb, Real.log_exp]
  have h1 : 1 ≤ x ^ eps := Real.one_le_rpow hx1.le he.le
  exact ⟨hx1.le, h1, by linarith [hx0 x hle]⟩
end GlobalTheory.BigTop.Fun
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaling_function_bound' : _root_.GlobalTheory.BigTop.Fun.ScaleCondition := by
  atlas_forward_decl _root_.GlobalTheory.BigTop.Fun.existsIntegralMultiple_holds_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest
namespace GlobalTheory.BigTop.Fun.LeafMMTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Spread
open GlobalTheory.SignedHC
variable (D : D7) (C : ℝ) (τ : D.what₂.Tau)
end Spread
section Leaf
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Leaf
theorem mm_tie_alt : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → _root_.GlobalTheory.BigTop.Fun.LeafMinimalMass @GlobalTheory.BigTop.Fun.Comparison₂ := fun h =>
  ⟨0, fun _ _ => h.imp fun _ _ _ _ _ => ⟨1, fun _ hC => _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun _ _ _ _ _ d hd =>
    let ⟨_, a, ha⟩ := hd
    leafMM_of_test d a ha.test hC⟩⟩
end GlobalTheory.BigTop.Fun.LeafMMTie
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leafMinimalMass_of_setAt : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → _root_.GlobalTheory.BigTop.Fun.LeafMinimalMass @GlobalTheory.BigTop.Fun.Comparison₂ := by
  atlas_forward_decl _root_.GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
namespace GlobalTheory.BigTop.Fun
theorem den_tie_alt : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) →
    DenSum → _root_.GlobalTheory.BigTop.Fun.LeafDensity @Comparison₂ := by
  intro hS hL hD
  refine _root_.GlobalTheory.BigTop.Fun.LeafConditions.mono (_root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hL hD) fun {D _ _ _ _ _ _ _ _ _} p CF d C CH _ hd => ⟨hd, fun hq => ?_⟩
  obtain ⟨-, a, ha⟩ := hd
  have hsq := ha.sq
  refine ⟨fun l hl => ((hsq.den l).1 hl).1, fun ij s h1 h2 => ?_⟩
  lift s to ℕ using (by omega)
  have h1' : 1 ≤ s := by exact_mod_cast h1
  have h2' : s ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 := by
    have h2'' : s ≤ sqRank D ij / 2 := by exact_mod_cast h2
    exact h2''.trans_eq (halfRank_eq_sqRank_div D ij).symm
  exact hq ij.1 ij.2 s h1' h2' _ (hsq.inside ij s h1' h2').2 d.Sd fun l hl => ((hsq.den l).1 hl).1
end GlobalTheory.BigTop.Fun
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leafDensity_of_logDeriv_bound_and_denSum : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → DenSum → _root_.GlobalTheory.BigTop.Fun.LeafDensity @Comparison₂ := by
  atlas_forward_decl _root_.GlobalTheory.BigTop.Fun.den_tie_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
noncomputable section
namespace GlobalTheory.BigTop.Fun.RamSum
section Norms
variable {F : Type} [Field F] [NumberField F]
end Norms
end GlobalTheory.BigTop.Fun.RamSum
namespace GlobalTheory.BigTop.Fun
open RamSum
theorem ramified_sums_seventh_bound_alt : _root_.GlobalTheory.BigTop.Fun.RamifiedSumBound' := by
  refine ⟨0, fun CF _ => ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ _ => ?_⟩⟩⟩
  refine ⟨42, fun C hC => _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p _ d _ => ?_⟩
  obtain ⟨-, -, hg, h1, h2, -⟩ := hF.1.2.2.2.2.2.2.2.2 x hx i
  have h3 := hF.2.2.1 x hx i
  have hb : 1 ≤ (Fm.L x i).sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  refine leaves_of_sum d.O C p.Z.b (Real.log_nonneg hb) (d.G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)) (fun v _ => isPrimePow_absNorm v)
    (ramifiedPlaces_sum_log_absNorm_le d.G.pl (Fm.L x i).sc hg h1 h2 h3) (fun v _ => ?_)
    (le_PPF d.O hC hb ?_ ?_ ((Fm.D x i).host.g_prime 0).pos ((Fm.D x i).host.g_prime 1).pos (Fm.D x i).host.pde_prime.pos
      (Fm.D x i).host.pde'_prime.pos (discr_ne_zero _))
  · unfold FunIn.O FunIn.data
    dsimp only
    split_ifs <;> omega
  · have := (Fm.D x i).R.m_le_f
    have := (Fm.D x i).R.two_le_m
    show 1 ≤ (Fm.D x i).R.f
    unfold Ranks.f Ranks.n
    omega
  · have := (Fm.D x i).R.two_le_m
    show 1 ≤ (Fm.D x i).R.k + (Fm.D x i).R.m
    omega
end GlobalTheory.BigTop.Fun
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramified_sum_bound' : _root_.GlobalTheory.BigTop.Fun.RamifiedSumBound' := by
  atlas_forward_decl _root_.GlobalTheory.BigTop.Fun.ramified_sums_seventh_bound_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
noncomputable section
namespace GlobalTheory.BigTop.Fun.Close
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem fittedFunction_at_zero_close_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator →
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → GlobalTheory.ToricTransport.TwistedTransport → GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → GlobalTheory.SqTop.Refl →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate →
    _root_.GlobalTheory.BigTop.LambdaLowerBound₂ → _root_.GlobalTheory.BigTop.Fun.ConstantFunctionFits @GlobalTheory.BigTop.Fun.Fld := by
  intro hP hH hTD hTr hTw hZ hR hAg hMa hFS hL
  obtain ⟨hDenSum, hThbSt, hOneSqSt, hBotSmall, hBotNe, hFieldDat, hTorEx, hDenEx, hBotEx, hLNe, hTriEx, hTower⟩ :=
    _root_.GlobalTheory.T.square_leading_term_bound hP.howeDualityReal hP hH hTD hTr hZ hR hAg hMa
  obtain ⟨hFin, hAway, hInf⟩ := _root_.GlobalTheory.T.sum_size_bound_all_places hP
  obtain ⟨hSumOK, hConst, hLin, hF2, hSumRat⟩ := _root_.GlobalTheory.T.local_sum_estimates_joined hP hAg hMa
  have hInj := GlobalTheory.RowTest.injK_of_separates hFS (_root_.GlobalTheory.RowTest.twisted_convergence_with_real_places hP (_root_.GlobalTheory.T.twisted_thetaLift_cuspidal hP))
  have hSize := _root_.GlobalTheory.T.size_at'
  have hSet := _root_.GlobalTheory.T.set_at_of_size_at' hSize
  have hDl := _root_.GlobalTheory.T.abs_logDerivativeAtOne_le_x_rpow_eps hP
  have hInp := GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied
  have hIntSt := GlobalTheory.T.classSumDenominatorBound_of_cmThetaHypotheses hInp
  have hArchSt := GlobalTheory.ArchTop.archSt_of_inp hInp
  have hThA := _root_.GlobalTheory.T.toric_ratio_family_estimate' (GlobalTheory.ToricTransport.toricRatioConjugates_of_transport hTw) hSet hDl hFieldDat hTorEx
  have hSq := _root_.GlobalTheory.T.sq_ratio_mem_range_emb_ll hP hAg hMa hSet hDl hConst hLNe hTriEx hTower
  have hB : _root_.GlobalTheory.BigTop.Fun.BundleCondition := @_root_.GlobalTheory.BigTop.Fun.bundle_of_rows_alt
  exact _root_.GlobalTheory.BigTop.Fun.fun0Fit_of_leaves_alt _ _ hB _root_.GlobalTheory.T.scaling_function_bound'
    (_root_.GlobalTheory.T.existsFunctionIn_of_sqRatio_range hSet hDl hSumOK hSumRat hConst hSq hIntSt hFieldDat hTorEx hDenEx hBotEx hBotSmall)
    (_root_.GlobalTheory.T.leafMinimalMass_of_setAt hSet) (_root_.GlobalTheory.T.oneMap_of_bundle_setAt_lin_inj_const_formula hB hSet hLin hInj hConst hF2) (_root_.GlobalTheory.T.leafKernel_tie_of_claim_inputs hB hSet hLin hInj hConst hF2)
    (_root_.GlobalTheory.T.leafFixedPoint_of_finK_awayK hSet hFin hAway) (_root_.GlobalTheory.T.leafHeightMapBound_of_infK hB hSet hInf) (_root_.GlobalTheory.T.leafInfinitePlaceBound_of_lamLow hL)
    (_root_.GlobalTheory.T.oneSq_of_log_derivative_bound_and_oneSqSt hSet hDl hThA hOneSqSt) (_root_.GlobalTheory.T.leafDensity_of_logDeriv_bound_and_denSum hSet hDl hDenSum) (_root_.GlobalTheory.T.leafIntegrality_of_logDeriv_bound hSet hDl hBotSmall hBotNe)
    (_root_.GlobalTheory.T.arch_tie_of_setAt_logDeriv hSet hDl hArchSt hBotSmall) (_root_.GlobalTheory.T.leaf_theta_bound_of_set_at hSet hDl hThbSt) (_root_.GlobalTheory.T.weight_of_size_bound' hSize)
    _root_.GlobalTheory.BigTop.Fun.Close.desHLeaf_alt _root_.GlobalTheory.T.rank_gap_bound _root_.GlobalTheory.T.ramified_sum_bound' _root_.GlobalTheory.T.polynomial_descent_estimate'
end GlobalTheory.BigTop.Fun.Close
end
end
end
end
