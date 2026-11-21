import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinkRStdTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BuiltCHasPart
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmGoodModelOfGlobalArtinReciprocity
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AdmissibleEntriesOfKernelLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubTwoOmegaSq
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JInvNormLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
import ReciprocityTheory.ClassFieldTheory.GlobalClassField.IsFrobAtMulOfMemInertiaGroup
import ReciprocityTheory.Chebotarev.CyclotomicIrreducibleOfForallIsUnramifiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedEmbeddingValues
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TorsionTaylorAlgebraicLatticeExistsOfCm
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.StatementJets
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
import Formalism.LocalToGlobal.InertKernelTheory.KernelsIntegralInert
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroTrivialStabilisersTrueColumns
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLocalModelsOfSplitUnramifiedJoints
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnJointsHoldAllTuples
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChiDValuesAndCcTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowTwUHolds
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CapLeWidth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumConditionsAtStandardKernelComparison

section
namespace GlobalTheory.TwV.Lt

theorem inert_theta_admissibility_of_complex_multiplication : Formalism.L2.Th1.CM.CM2 → GlobalTheory.TwV.Lt.AdmAtEnt2 := fun h => by
  haveI : Fact Formalism.L2.Th1.CM.CM2 := ⟨h⟩
  exact Formalism.L2.KerInert.AdmLoc2.admissible_entries_small_chain

end GlobalTheory.TwV.Lt
end

section
namespace GlobalTheory.TwV.Lt

theorem curveEx_of_cm (h2 : Formalism.L2.Th1.CM.CM2) (h3 : Formalism.L2.Th1.CM.CM3) : CurveEx := by
  intro D cc δ B χ hc hd hχ p _ hcop h5 hIn lam
  obtain ⟨g, hgl, hAt, hM, hLT⟩ :=
    GlobalTheory.InertGenusOne.datum_exists_coprime h2 h3 D cc δ hc hd p hcop h5 hIn lam
  exact ⟨g, hLT, h5, hAt, hIn, hM, hc, hd, hχ, hgl.symm, hAt.2.2.2.1⟩

theorem exists_genusOne_formal_iso_of_unramified_good_reduction (h : Formalism.L2.Th1.CM.CM2) : CurveEx :=
  curveEx_of_cm h GlobalTheory.HondaCM3.cm3

end GlobalTheory.TwV.Lt
end

section
namespace GlobalTheory

theorem intInert_of_complexMultiplication_condition : Formalism.L2.Th1.CM.CM2 → Formalism.L2.KerInert.IntInert :=
  fun h => by
    haveI : Fact Formalism.L2.Th1.CM.CM2 := ⟨h⟩
    exact Formalism.L2.KerInert.kernels_integral_inert

end GlobalTheory
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Pdv.stdKer_stdRd_mark : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned ∧ (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t'.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hS
  dsimp only at hX hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hX
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  have hA : ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) Bb χ cD = I.J.amb B χ := eq_of_heq hamb
  have hm := hOk.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.1
  refine ⟨⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, _, _, seam_ok, _, pr_ok, g_rec, _, _, _, _, T_rec, _, Q_rec, _, _, _, _, glob_σ, glob_xi, idx_ok, O, I.kerRd l Z, fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hOk.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a), O_dgen, O_S, ?_, ?_, unf, ent, ent_lam, kf, kf_un, served⟩, ?_, ?_, ?_, ?_⟩
  · exact fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
  · intro u a i c c'
    rw [hA, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J χ, χ_rec]
    exact (hO.Th u a i c c').trans (I.kerRd_Th l Z hOk idl_ok hO u a i c c').symm
  · exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, heq_of_eq hA, hδ, hO⟩
  · exact fun u a => ⟨I.kerRd l Z u a, HEq.rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact fun u a => I.kerRd_top l Z hm u a
  · exact fun u a i c => Iff.rfl
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.TwV
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Pdv.oneTie_jointsAt_all : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch), tp.xi = I.xi → I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → I.StdC l Z C → (∀ u, I.StdLvC l Z u (C.forms u)) → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → G.LatTied hT Gi Gl → (∃ t' : KerEntTied ex, ∀ μ, JointsAt t' μ) ∧ ∀ u, ex.tw.e0 u (I.rec7 l Z).what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  intro B X I hOk hP l l0 Z L hT Gi Gl K Y cX ex t C full g nch tp _htp hTw hJ htw hpi hS hC _hLv hDt hg hgf hD hLat
  obtain ⟨t', hS', hR', _, hM'⟩ := GlobalTheory.Pdv.stdKer_stdRd_mark I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  obtain ⟨h1, h2⟩ := GlobalTheory.T.trueColumn_joints_hold_all_tuples I hOk hP l Z l0 L hT Gi Gl K Y cX ex t' C full g hTw hJ htw hpi hS' hR' hM' hC hDt hg hgf hD hLat
  exact ⟨⟨t', h1⟩, h2⟩
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.TwV
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_relation_true_columns_joints_all_tuples : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch), tp.xi = I.xi → I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → I.StdC l Z C → (∀ u, I.StdLvC l Z u (C.forms u)) → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → G.LatTied hT Gi Gl → (∃ t' : KerEntTied ex, ∀ μ, JointsAt t' μ) ∧ ∀ u, ex.tw.e0 u (I.rec7 l Z).what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  atlas_forward_decl GlobalTheory.Pdv.oneTie_jointsAt_all
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

set_option maxHeartbeats 1000000

theorem GlobalTheory.Svd.jointsAt_all_std : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), Part w Z (ofObj O) → G.LatTied O.gatT O.Gx O.Gy → (∃ t : KerEntTied O.ex, ∀ μ, GlobalTheory.TwV.JointsAt t μ) ∧ ∀ u, O.ex.tw.e0 u (w.D Z).what₂.mu0 = O.ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  intro B f T w Z O P hL
  obtain ⟨htw, -, hpiT, -, t, hstd, -, -⟩ := GlobalTheory.Svd.Part.kerTie B f T w Z O P
  have hchi := (GlobalTheory.Mem.ChiDVal.chiD_values_and_cc_top B f T w Z).1
  obtain ⟨L, gatT, Gx, Gy, K, X, cX, ex⟩ := O
  obtain ⟨pin, col, errX, tp, xi, qp, ker0, ker_eq, ker⟩ := P
  simp only [ofObj, extraObj] at ker_eq
  have h1 := congrArg Sigma.fst ker_eq
  simp only at h1
  subst h1
  have h2 := eq_of_heq (Sigma.mk.inj ker_eq).2
  have h3 := congrArg Sigma.fst h2
  simp only at h3
  obtain ⟨lev, th, th_io, cmp, lat, tw, exker⟩ := ex
  simp only at h3
  subst h3
  exact GlobalTheory.T.kernel_relation_true_columns_joints_all_tuples w.I w.ok w.pins w.l w.l0 Z L col.Gt Gx Gy K X cX _ t col.C col.full col.g _ tp xi
    pin.isTw pin.jets htw hpiT hstd col.std col.stdLv col.stdDt col.herm_eq col.forms_eq hchi hL
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem modelsAt_of_part : GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), Part w Z (ofObj O) → ModelsAt (w.D Z) O := by
  intro hA hC B f T w Z O hP hL hk
  obtain ⟨⟨t, hJ⟩, he⟩ := GlobalTheory.Svd.jointsAt_all_std B f T w Z O hP hL
  have hS : OrbitPlaces.Stab0 (w.D Z) := GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns w.I w.ok w.pins w.l Z O.ex.lev
  exact GlobalTheory.T.thetaLocalModels_of_splitUnramified_joints hA hC t (fun μ _ => hJ μ) he hS hk

end GlobalTheory.Svd
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuplesHaveLocalModels_of_standardColumnObjects : GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), Part w Z (ofObj O) → ModelsAt (w.D Z) O := by
  atlas_forward_decl GlobalTheory.Svd.modelsAt_of_part
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

theorem GlobalTheory.TwU.siteAdm_setDiv : ∀ (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : G.Fills (D.gat u w hg)) (Lv : G.Levels Fl) (Ch : G.Chain Lv), GlobalTheory.TwU.SiteAdm D u w hg Fl Lv Ch → GlobalTheory.TwU.SiteAdm (setDiv D N h) u w hg Fl Lv Ch := by
  intro D N h u w hg Fl Lv Ch H
  exact H
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siteAdmissible_indep_divisionLattices : ∀ (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : G.Fills (D.gat u w hg)) (Lv : G.Levels Fl) (Ch : G.Chain Lv), GlobalTheory.TwU.SiteAdm D u w hg Fl Lv Ch → GlobalTheory.TwU.SiteAdm (setDiv D N h) u w hg Fl Lv Ch := by
  atlas_forward_decl GlobalTheory.TwU.siteAdm_setDiv
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

set_option maxHeartbeats 1000000 in

theorem cmpLite_setDiv : ∀ (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : G.Fills (D.gat u w hg)) (Lv : G.Levels Fl) (Ch : G.Chain Lv), GlobalTheory.TwU.CmpLite D c Tw u μ w hg Ch → GlobalTheory.TwU.CmpLite (setDiv D N h) (cmpTr N h c) (twTr N h Tw) u μ w hg Ch := by
  intro D N h c Tw u μ w hg Fl Lv Ch H
  exact H

end GlobalTheory.Svd
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeChainComparison_indep_divisionLattices : ∀ (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : G.Fills (D.gat u w hg)) (Lv : G.Levels Fl) (Ch : G.Chain Lv), GlobalTheory.TwU.CmpLite D c Tw u μ w hg Ch → GlobalTheory.TwU.CmpLite (setDiv D N h) (cmpTr N h c) (twTr N h Tw) u μ w hg Ch := by
  atlas_forward_decl GlobalTheory.Svd.cmpLite_setDiv
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

set_option maxHeartbeats 800000 in

theorem modelsAt_tr : ∀ (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ),
    ModelsAt D O → ModelsAt (setDiv D N h) (O.tr N h) := by
  intro D O N h H hT hk
  obtain ⟨h0, LC, hLC⟩ := H hT hk
  refine ⟨h0, LC, fun μ hμ u w hg hq => ?_⟩
  obtain ⟨c1, c2⟩ := hLC μ hμ u w hg hq
  exact ⟨GlobalTheory.T.latticeChainComparison_indep_divisionLattices D N h _ _ u μ w hg _ _ _ c1, GlobalTheory.T.siteAdmissible_indep_divisionLattices D N h u w hg _ _ _ c2⟩

end GlobalTheory.Svd
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuplesLocalModels_of_otherDivisionLatticesHeights : ∀ (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), ModelsAt D O → ModelsAt (setDiv D N h) (O.tr N h) := by
  atlas_forward_decl GlobalTheory.Svd.modelsAt_tr
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem modelsAt_bpt : GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ (K : Ctx) (β : BPt K), β.Is (positionOf HasPart) → ModelsAt β.D β.O := by
  intro h1 h2 K β hβ
  have key : ∀ O : Obj β.X.toD7, ofObj O = β.c.O → ModelsAt β.X.toD7 O := by
    refine positionOf_ind (P := HasPart) (R := fun K X f T c => ∀ O : Obj X.toD7, ofObj O = c.O → ModelsAt X.toD7 O) ?_ hβ
    intro K B f T w Z c hc O hO
    obtain ⟨b⟩ := hc
    have b' : Part w Z (ofObj O) := hO ▸ b
    exact GlobalTheory.T.tuplesHaveLocalModels_of_standardColumnObjects h1 h2 B f T w Z O b'
  have hm := key (β.Y.obj β.p) (by rw [ofObj_obj]; exact β.hY)
  exact GlobalTheory.T.tuplesLocalModels_of_otherDivisionLatticesHeights β.X.toD7 (β.Y.obj β.p) (nPrime β.p.L) β.p.ht hm

end GlobalTheory.Svd
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuplesHaveLocalModels_at_constructedPoint_over_trueColumns : GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ (K : Ctx) (β : BPt K), β.Is (positionOf HasPart) → ModelsAt β.D β.O := by
  atlas_forward_decl GlobalTheory.Svd.modelsAt_bpt
end

section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.ShapeUniform

def Big (eps x : ℝ) : Prop := 4 ≤ x ∧ x ^ 6 ≤ Real.exp (x ^ (eps / 3))

variable {eps : ℝ} (Fm : FamP eps) {x : ℝ}

theorem size_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) :
    ((Fm.D x i).R.k : ℝ) * (Fm.D x i).R.N (Fm.D x i).R.m ≤ (Fm.L x i).Sc / 4 ∧ ((Fm.D x i).R.k : ℝ) * (Fm.L x i).Sc ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ ((Fm.D x i).R.m : ℝ) * (((Fm.D x i).R.t : ℝ) + 1) * (Fm.L x i).etaSz ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).etaSz ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).sc.w'' (Fm.D x i).R.n ≤ (Fm.L x i).sc.b' / (Fm.L x i).sc.x ∧ 4 ≤ (Fm.L x i).sc.x ∧ 2 * (Fm.L x i).sc.b' ≤ (Fm.L x i).sc.b ∧ ((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b' ≤ (Fm.L x i).sc.b ∧ 1 ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).etaSz + 1 + 3 * (Fm.L x i).Sc ≤ (Fm.L x i).sc.b := by
  apply GlobalTheory.ShNums.size_rel_at (Fm.L x i) (Fm.sizes x hx1 i)
  · rw [Fm.L_x x i hx1]; exact hg.1
  · unfold Scale.X'
    rw [Fm.L_x x i hx1, Fm.L_eps x i]; exact hg.2

theorem windows_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) : ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (Fm.L x i).sc.w'' (Fm.D x i).R.n ≤ wPl (Fm.D x i) (j + 1) z ∧ wPl (Fm.D x i) (j + 1) z ≤ (Fm.L x i).sc.b + (Fm.L x i).etaSz + 1 ∧ (IsTopPl (Fm.D x i) z → (Fm.L x i).sc.b' ≤ wPl (Fm.D x i) (j + 1) z ∧ wPl (Fm.D x i) (j + 1) z ≤ 2 * (Fm.L x i).sc.b') := by
  intro j hj z
  obtain ⟨-, -, -, heta, hw, h4, h2b, -, -, -⟩ := size_at Fm hx1 i hg
  have P := Fm.params x hx1 i
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have he := L.etaSz_pos
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) h4
  have hq0 : 0 < L.sc.b' / L.sc.x := div_pos hb' hxp
  have htop : ∀ (τ : D.what₂.Tau) (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t →
      L.sc.b' ≤ wj D (j + 1) τ ∧ wj D (j + 1) τ ≤ 2 * L.sc.b' := by
    intro τ t ht
    obtain ⟨a1, a2⟩ := L.win_top (j + 1) (by omega) (by omega) τ t ht
    have a3 := L.bT_ge t
    have a4 := GlobalTheory.Ggeo.bT_le_five_quarters P t
    constructor <;> linarith
  unfold wPl
  refine ⟨?_, ?_, ?_⟩
  · by_cases h1 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces
    · have := (L.win_thick (j + 1) (by omega) (by omega) _ h1).1
      linarith
    by_cases h2 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have := (htop _ ⟨t, ht⟩ e.symm).1
      linarith
    · exact (L.win_thin (j + 1) (by omega) (by omega) _ ⟨(D.eTau _).2, h2, h1⟩).1
  · by_cases h1 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces
    · exact (L.win_thick (j + 1) (by omega) (by omega) _ h1).2
    by_cases h2 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have := (htop _ ⟨t, ht⟩ e.symm).2
      linarith
    · have := (L.win_thin (j + 1) (by omega) (by omega) _ ⟨(D.eTau _).2, h2, h1⟩).2
      linarith
  · rintro ⟨hz1, hz2⟩
    refine htop _ ⟨z.2, hz2⟩ ?_
    unfold tauPl
    rw [Equiv.apply_symm_apply]
    simp [plGG, hz1]

theorem long_at (hx : Fm.x1 < x) (i : Fm.Ix x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), ∀ r < (Fm.D x i).R.k, (¬ IsTopPl (Fm.D x i) z → wPl (Fm.D x i) (j + 1) z - (Fm.D x i).R.N (Fm.D x i).R.m - 1 / 2 < DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r < wPl (Fm.D x i) (j + 1) z + (if r = 0 then 3 * (Fm.L x i).Sc else (Fm.L x i).Sc)) ∧ (IsTopPl (Fm.D x i) z → 1 ≤ r → r + 1 < (Fm.D x i).R.k → wPl (Fm.D x i) (j + 1) z - (Fm.D x i).R.N (Fm.D x i).R.m < DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r < wPl (Fm.D x i) (j + 1) z + (Fm.L x i).Sc) := by
  intro u j hj z r hr
  obtain ⟨h1, h2⟩ := GlobalTheory.LongRows.row_bounds (Fm.D x i) u j hj z r hr
  refine ⟨fun hz => ?_, fun _ hr1 hr2 => ?_⟩
  · obtain ⟨h3, h4⟩ := GlobalTheory.LongRows.u_bounds_off (Fm.params x hx i) u _ (GlobalTheory.LongRows.not_mem_topPlaces _ z hz) r hr
    constructor <;> linarith
  · obtain ⟨h3, h4⟩ := (Fm.L x i).cloud_u u (tauPl (Fm.D x i) z) ⟨r, hr⟩ hr1 hr2
    constructor <;> linarith

theorem block_at (i : Fm.Ix x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), ∀ r, (Fm.D x i).R.k ≤ r → r < (Fm.D x i).R.N j → 0 ≤ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ≤ (Fm.L x i).etaSz := by
  intro u j hj z r hk hr
  refine ⟨(RowWeightLemmas.nuRow_pos _ u j hj _ r hr).le, ?_⟩
  obtain ⟨q, s, hq, hs, rfl⟩ := RowWeightLemmas.block_decomp _ j r hk hr
  rw [RowWeightLemmas.nuRow_block _ u j hj _ q s hq hs, (Fm.D x i).hcW_e u]
  have h1 := (Fm.L x i).be_close (tauPl (Fm.D x i) z) ⟨q, by omega⟩ ⟨j, hj⟩
  have h2 := ((Fm.D x i).hc (tauPl (Fm.D x i) z)).gap_be ⟨q, by omega⟩
  have h3 : (0 : ℚ) ≤ ((j : ℚ) - q) * (((Fm.D x i).R.t : ℚ) + 1) := by
    have : (q : ℚ) ≤ j := by exact_mod_cast hq.le
    exact mul_nonneg (by linarith) (by positivity)
  have h4 : (0 : ℚ) ≤ (((Fm.D x i).R.t : ℚ) + 3) / 2 := by positivity
  refine le_trans ?_ h1
  refine le_trans ?_ (neg_le_abs _)
  rw [← Rat.cast_neg]
  exact Rat.cast_le.2 (by linarith)

theorem top_rows_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) 0 = (aL (Fm.L x i) z.2 : ℝ) + (wPl (Fm.D x i) (j + 1) z - kaJ (Fm.D x i) (j + 1)) ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) = (wPl (Fm.D x i) (j + 1) z - kaJ (Fm.D x i) (j + 1)) - (bL (Fm.L x i) z.2 : ℝ) ∧ 0 ≤ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) ≤ 2 * (Fm.L x i).sc.b' / (Fm.L x i).sc.x := by
  intro u j hj z hz
  have h4 := GlobalTheory.TopRows.eta_le (Fm.params x hx1 i)
  obtain ⟨e1, e2, e3, e4⟩ := GlobalTheory.TopRows.nuRow_tauPl_of_isTopPl (Fm.L x i) u j hj z hz
  refine ⟨e1, e2, e3, e4.trans ?_⟩
  rw [mul_div_assoc]
  linarith

theorem nuRow_le_at (hx2 : 2 ≤ x) (hx1 : Fm.x1 < x) (i : Fm.Ix x) : ∀ u, ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ τ, ∀ l < (Fm.D x i).R.N (j - 1), 0 ≤ DV.nuRow (Fm.D x i) u j τ l ∧ DV.nuRow (Fm.D x i) u j τ l ≤ 10 * x * (Fm.L x i).sc.b := by
  intro u j hj τ l hl
  have hS := Fm.sizes x hx1 i
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have h2x : 2 ≤ (Fm.L x i).sc.x := by rw [hsx]; exact hx2
  obtain ⟨h1j, hmj⟩ := Finset.mem_Icc.1 hj
  obtain ⟨a1, hw3⟩ := GlobalTheory.HCEntries.wj_bounds hS h2x j h1j hmj τ
  have hwe : DV.wSz (Fm.D x i) j τ = wj (Fm.D x i) j τ := by
    unfold DV.wSz wj
    rw [dif_pos ⟨h1j, hmj⟩, dif_pos (by omega)]
  have hj' := Finset.mem_Icc.1 hj
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hl' : l < (Fm.D x i).R.N j' := by simpa using hl
  have hjm : j' < (Fm.D x i).R.m := by omega
  have hk : 0 < (Fm.D x i).R.k := by have := (Fm.D x i).R.m_add_three_le_k; omega
  refine ⟨(RowWeightLemmas.nuRow_pos _ u j' hjm τ l hl').le, ?_⟩
  have h1 := RowWeightLemmas.nuRow_anti' _ u j' hjm τ l 0 (Nat.zero_le _) hl'
  have h2 := GlobalTheory.nuRow_zero_le (Fm.D x i) u (j' + 1) τ hk
  have hu : |((((Fm.D x i).hcW u τ).u ⟨0, hk⟩ : ℚ) : ℝ)| ≤ 4 * x * (Fm.L x i).sc.b := by
    have := GlobalTheory.HCEntries.u_bound hS (Fm.params x hx1 i) h2x u τ ⟨0, hk⟩
    rwa [hsx] at this
  have h3 := (abs_le.1 hu).2
  have hb : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  have hx' : 1 < x := Fm.one_lt_family_threshold.trans hx1
  have h4 : (Fm.L x i).sc.b ≤ x * (Fm.L x i).sc.b := le_mul_of_one_le_left hb.le hx'.le
  nlinarith

theorem excess_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), ¬ IsTopPl (Fm.D x i) z → 0 ≤ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z ∧ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z ≤ 4 * wPl (Fm.D x i) (j + 1) z := by
  intro u j hj z hz
  obtain ⟨a1, a2, a3, -⟩ := size_at Fm hx1 i hg
  have hk := (Fm.D x i).R.m_add_three_le_k
  rw [GlobalTheory.nuD_card_eq_sum_nuRow (Fm.D x i) (nuRowOK _) u j hj z]
  have heta := (Fm.L x i).etaSz_pos
  refine GlobalTheory.ExcessLow.excess_sum _ (Fm.D x i).R.k (j * ((Fm.D x i).R.t + 1)) _
    ((Fm.D x i).R.N (Fm.D x i).R.m) (Fm.L x i).Sc (Fm.L x i).etaSz
    ((Fm.L x i).sc.w'' (Fm.D x i).R.n) (by omega) ?_ (Fm.L x i).Sc_pos.le
    (fun r hr => (long_at Fm hx1 i u j hj z r hr).1 hz)
    (fun r hr hr' => block_at Fm i u j hj z r hr hr') a1 a2 ?_ (windows_at Fm hx1 i hg j hj z).1
  · have : 1 ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
      unfold Ranks.N
      omega
    exact_mod_cast this
  · refine le_trans ?_ a3
    apply mul_le_mul_of_nonneg_right _ heta.le
    push_cast
    have : (j : ℝ) ≤ (Fm.D x i).R.m := by exact_mod_cast hj.le
    exact mul_le_mul_of_nonneg_right this (by positivity)

theorem top_excess_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → 0 ≤ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) - ((((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z - 2 * wPl (Fm.D x i) (j + 1) z) ∧ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) - ((((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z - 2 * wPl (Fm.D x i) (j + 1) z) ≤ 4 * wPl (Fm.D x i) (j + 1) z := by
  intro u j hj z hz
  obtain ⟨a1, a2, a3, -, a5, a6, -, -, a9, -⟩ := size_at Fm hx1 i hg
  obtain ⟨b1, -, b3⟩ := windows_at Fm hx1 i hg j hj z
  obtain ⟨b3, -⟩ := b3 hz
  have c := long_at Fm hx1 i u j hj z
  obtain ⟨-, -, d3, d4⟩ := top_rows_at Fm hx1 i u j hj z hz
  have e := block_at Fm i u j hj z
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hN : D.R.N j = D.R.k + j * (D.R.t + 1) := by unfold Ranks.N; omega
  have hok := nuRowOK D
  rw [GlobalTheory.nuD_card_eq_sum_nuRow D hok u j hj z, hok u j hj z 0, if_pos (by omega), hN,
    GlobalTheory.TopExcess.sum_range_split _ _ _ (by omega)]
  obtain ⟨m1, m2⟩ := GlobalTheory.TopExcess.sum_Ico_bounds (DV.nuRow D u (j + 1) (tauPl D z)) 1 (D.R.k - 1) _ _
    (fun r hr1 hr2 => let h := (c r (by omega)).2 hz hr1 (by omega); ⟨h.1.le, h.2.le⟩)
  obtain ⟨n1, n2⟩ := GlobalTheory.TopExcess.sum_Ico_bounds (DV.nuRow D u (j + 1) (tauPl D z)) D.R.k (D.R.k + j * (D.R.t + 1)) _ _
    (fun r hr1 hr2 => e r hr1 (by omega))
  have hkc : ((D.R.k - 1 - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 2 := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; norm_num
  rw [hkc] at m1 m2
  rw [Nat.add_sub_cancel_left] at n1 n2
  push_cast at n1 n2
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hj' : (j : ℝ) ≤ D.R.m := by exact_mod_cast hj.le
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hNm : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hx0 : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx0 hb) (Real.exp_pos _)
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) a6
  have hbl : (j : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by gcongr
  have hS1 : L.Sc ≤ (D.R.k : ℝ) * L.Sc := le_mul_of_one_le_left hS.le (by linarith)
  rw [mul_div_assoc] at d4
  constructor <;> nlinarith

theorem two_w_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → 2 * wPl (Fm.D x i) (j + 1) z ≤ (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) := by
  intro u j hj z hz
  obtain ⟨-, -, -, -, -, h4, h2b, -, -, -⟩ := size_at Fm hx1 i hg
  obtain ⟨e1, e2, e3, -⟩ := top_rows_at Fm hx1 i u j hj z hz
  obtain ⟨-, -, hw⟩ := windows_at Fm hx1 i hg j hj z
  obtain ⟨-, hw2⟩ := hw hz
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have ha : aL L z.2 = L.aT ⟨z.2, hz.2⟩ := by unfold aL; rw [dif_pos hz.2]
  have hbb : bL L z.2 = L.bT ⟨z.2, hz.2⟩ := by unfold bL; rw [dif_pos hz.2]
  have a1 := (L.aT_win ⟨z.2, hz.2⟩).1
  have a2 := L.bT_ge ⟨z.2, hz.2⟩
  have a3 : 4 * L.sc.b ≤ L.sc.a := by
    unfold Scale.a
    exact mul_le_mul_of_nonneg_right h4 hb.le
  have hN : 0 < D.R.N j := by
    have := D.R.m_add_three_le_k
    unfold Ranks.N
    omega
  rw [nuRowOK D u j hj z 0, if_pos hN, e1]
  rw [e2, hbb] at e3
  rw [ha]
  linarith

theorem card_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) ≤ (Fm.L x i).sc.a ^ 2 := by
  intro u j hj z
  have hr := nuRow_le_at Fm (by linarith [hg.1]) hx1 i u (j + 1)
    (Finset.mem_Icc.2 ⟨by omega, by omega⟩) (tauPl (Fm.D x i) z)
  simp only [Nat.add_sub_cancel] at hr
  obtain ⟨hkN, -, -, -, -, h4, -, -, -, hS⟩ := size_at Fm hx1 i hg
  have hsx := Fm.L_x x i hx1
  rw [GlobalTheory.nuD_card_eq_sum_nuRow _ (nuRowOK _) u j hj z]
  have hsum := Finset.sum_le_card_nsmul (Finset.range ((Fm.D x i).R.N j))
    (fun r => DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r) (10 * x * (Fm.L x i).sc.b)
    (fun r hr' => (hr r (Finset.mem_range.1 hr')).2)
  rw [Finset.card_range, nsmul_eq_mul] at hsum
  have hNle : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
    have : (Fm.D x i).R.N j ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
      unfold Ranks.N
      have := Nat.mul_le_mul_right ((Fm.D x i).R.t + 1) hj.le
      omega
    exact_mod_cast this
  have hk : (1 : ℝ) ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ (Fm.D x i).R.k)
  have hN0 : (0 : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m := Nat.cast_nonneg _
  have hNk := le_mul_of_one_le_left hN0 hk
  have heta := (Fm.L x i).etaSz_pos
  have hb : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  have hN : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.L x i).sc.b / 10 := by linarith
  rw [hsx] at h4
  have hxb : 0 ≤ 10 * x * (Fm.L x i).sc.b := by positivity
  have h5 := mul_le_mul_of_nonneg_right hN hxb
  have ha : (Fm.L x i).sc.a = x * (Fm.L x i).sc.b := by
    unfold Scale.a
    rw [hsx]
  rw [ha]
  have h6 : x * (Fm.L x i).sc.b ^ 2 ≤ x * (x * (Fm.L x i).sc.b ^ 2) :=
    le_mul_of_one_le_left (by positivity) (by linarith)
  nlinarith

theorem rank_at (hx3 : 3 ≤ x) (hx1 : Fm.x1 < x) (i : Fm.Ix x) :
    2 * Real.logb 5 ((Fm.L x i).sc.a ^ 2) + 2 ≤ ((Fm.D x i).R.k : ℝ) - 1 := by
  have hK := (Fm.sizes x hx1 i).2.2.1.1
  have hsx := Fm.L_x x i hx1
  have he := (Fm.L x i).sc.eps_pos
  have he' := (Fm.L x i).sc.eps_lt
  have hx0 : (0 : ℝ) < x := by linarith
  rw [hsx] at hK
  have h4 : x ^ (4 : ℕ) ≤ ((Fm.D x i).R.k : ℝ) := by
    refine le_trans ?_ hK
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    unfold szTh
    push_cast
    linarith
  have hL : (Fm.L x i).sc.L ≤ x := by
    unfold Scale.L
    rw [hsx]
    calc x ^ (Fm.L x i).sc.eps ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = x := Real.rpow_one x
  have hL0 : 0 ≤ (Fm.L x i).sc.L := by
    unfold Scale.L
    rw [hsx]
    positivity
  have hla : Real.log (Fm.L x i).sc.a = Real.log x + (Fm.L x i).sc.L := by
    unfold Scale.a Scale.b
    rw [hsx, Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hlx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h5 : 1 ≤ Real.log 5 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hb : Real.logb 5 ((Fm.L x i).sc.a ^ 2) ≤ 4 * x := by
    rw [Real.logb, Real.log_pow, hla]
    push_cast
    refine (div_le_self (by linarith) h5).trans (by linarith)
  have h27 : 27 ≤ x ^ 3 := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx3 3
  have : 27 * x ≤ x ^ 4 := by
    calc 27 * x ≤ x ^ 3 * x := mul_le_mul_of_nonneg_right h27 hx0.le
      _ = x ^ 4 := by ring
  linarith

theorem xa_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) :
    (Fm.L x i).sc.X'' (Fm.D x i).R.n ≤ (Fm.L x i).sc.a := by
  obtain ⟨-, -, -, -, -, h4, -, -, hw, -⟩ := size_at Fm hx1 i hg
  have ha : 0 ≤ (Fm.L x i).sc.a := by
    have h0 : 0 ≤ (Fm.L x i).sc.x := by linarith
    unfold Scale.a Scale.b
    positivity
  rw [Scale.X'']
  exact div_le_self ha hw

theorem cap_width_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (if IsTopPl (Fm.D x i) z then (((nuD (Fm.D x i) u j z).rowLen 1 : ℕ) : ℝ) else (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ)) ≤ (Fm.L x i).sc.b + (Fm.L x i).etaSz + 1 + 3 * (Fm.L x i).Sc := by
  intro u j hj z
  obtain ⟨-, hw, -⟩ := windows_at Fm hx1 i hg j hj z
  have hr := long_at Fm hx1 i u j hj z
  have hk : 5 ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    have := (Fm.D x i).R.two_le_m
    omega
  have hN : (Fm.D x i).R.k ≤ (Fm.D x i).R.N j := by unfold Ranks.N; omega
  have hS := (Fm.L x i).Sc_pos
  split_ifs with hz
  · have e := nuRowOK (Fm.D x i) u j hj z 1
    rw [if_pos (by omega)] at e
    have := ((hr 1 (by omega)).2 hz le_rfl (by omega)).2
    rw [e]
    linarith
  · have e := nuRowOK (Fm.D x i) u j hj z 0
    rw [if_pos (by omega)] at e
    have := ((hr 0 (by omega)).1 hz).2
    rw [if_pos rfl] at this
    rw [e]
    linarith

theorem cap_fill_at (hx : Fm.x1 < x) (i : Fm.Ix x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (if IsTopPl (Fm.D x i) z then (((nuD (Fm.D x i) u j z).rowLen 1 : ℕ) : ℝ) else (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ)) ≤ fillG (Fm.Gx x i) (bL (Fm.L x i)) (j + 1) z + cG (Fm.L x i) := by
  intro u j hj z
  have hfill : fill (Fm.Gx x i) (bL (Fm.L x i)) (j + 1) z = wPl (Fm.D x i) (j + 1) z := by
    obtain ⟨w⟩ := GlobalTheory.nonempty_places_of_record (Fm.D x i)
    refine (Fm.fills x hx i w).1 (j + 1) ?_ (tauPl _ z) z ?_
    · simp only [SizeData₂.lifts, Finset.mem_Icc]; omega
    · simp [tauPl]
  have hk : 5 ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k; have := (Fm.D x i).R.two_le_m; omega
  have hS := (Fm.L x i).Sc_pos
  unfold fillG cG
  rw [hfill]
  split_ifs with hz
  · have h1 := GlobalTheory.CapBound.row_le (Fm.D x i) u j hj z 1 le_rfl (by omega)
    obtain ⟨-, h4⟩ := (Fm.L x i).cloud_u u (tauPl (Fm.D x i) z) ⟨1, by omega⟩ le_rfl (by show 1 + 1 < _; omega)
    linarith
  · have h1 := GlobalTheory.CapBound.row_le (Fm.D x i) u j hj z 0 (by omega) (by omega)
    obtain ⟨-, h4⟩ := GlobalTheory.LongRows.u_bounds_off (Fm.params x hx i) u _
      (GlobalTheory.LongRows.not_mem_topPlaces _ z hz) 0 (by omega)
    rw [if_pos rfl] at h4
    linarith

theorem gap_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ t ∈ (Fm.D x i).host.TT, (((nuD (Fm.D x i) u j (false, t)).rowLen 0 : ℕ) : ℝ) - (((nuD (Fm.D x i) u j (false, t)).rowLen 1 : ℕ) : ℝ) ≤ 2 * (Fm.L x i).sc.a := by
  intro u j hj t ht
  obtain ⟨s1, -, -, -, -, h4, -, -, -, s2⟩ := size_at Fm hx1 i hg
  have hz : IsTopPl (Fm.D x i) (false, t) := ⟨rfl, ht⟩
  have hk : 5 ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    have := (Fm.D x i).R.two_le_m
    omega
  obtain ⟨r1, -⟩ := (long_at Fm hx1 i u j hj (false, t) 1 (by omega)).2 hz le_rfl (by omega)
  obtain ⟨e1, -⟩ := GlobalTheory.TopRows.nuRow_tauPl_of_isTopPl (Fm.L x i) u j hj (false, t) hz
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hN : D.R.k ≤ D.R.N j := by unfold Ranks.N; omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hb : 0 < L.sc.b := Real.exp_pos _
  have ha : aL L t = L.aT ⟨t, ht⟩ := by unfold aL; rw [dif_pos ht]
  have a1 := (L.aT_win ⟨t, ht⟩).2
  have a3 : 4 * L.sc.b ≤ L.sc.a := by
    unfold Scale.a
    exact mul_le_mul_of_nonneg_right h4 hb.le
  have hp : 1 ≤ L.sc.x ^ (Scale.A / 2) :=
    Real.one_le_rpow (by linarith) (by unfold Scale.A; norm_num)
  have a4 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) (by nlinarith)
  have hka : 0 ≤ kaJ D (j + 1) := by
    unfold kaJ
    push_cast
    have : (0 : ℝ) ≤ (2 * ((j : ℝ) + 1) - 1) := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
    positivity
  have hNm : (D.R.N D.R.m : ℝ) ≤ (D.R.k : ℝ) * D.R.N D.R.m :=
    le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith)
  have he := L.etaSz_pos
  rw [nuRowOK D u j hj, nuRowOK D u j hj, if_pos (by omega), if_pos (by omega), e1]
  simp only [ha]
  linarith

theorem three_le_split_at (h0 : 0 < eps) (hx : (3 : ℝ) ^ (5 / eps) ≤ x) (h1 : Fm.x1 < x)
    (i : Fm.Ix x) : 3 ≤ (Fm.D x i).host.splitBound := by
  have h11 := Formalism.MainNotions.SizesAt.eleven_le (Fm.sizes x h1 i)
  omega

theorem shape_uniform : ∀ eps : ℝ, ∃ x0 : ℝ, ∀ (Fm : FamP eps), ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) (Ee : OrbitPlaces.Ent (Fm.D x i)), OrbitPlaces.Shape (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Ee ∧ (∀ u, ∀ j < (Fm.D x i).R.m, ∀ t ∈ (Fm.D x i).host.TT, Ee.row u j (false, t) 0 - Ee.row u j (false, t) 1 ≤ 2 * (Fm.L x i).sc.a) ∧ 3 ≤ (Fm.D x i).host.splitBound := by
  intro eps
  by_cases he : 0 < eps
  · obtain ⟨x0, hx0⟩ := GlobalTheory.ShNums.pow_six_le_exp he
    refine ⟨max x0 ((3 : ℝ) ^ (5 / eps)), fun Fm x hx hx1 i Ee => ?_⟩
    have hg : Big eps x := hx0 x (le_trans (le_max_left _ _) hx)
    have h3 : (3 : ℝ) ^ (5 / eps) ≤ x := le_trans (le_max_right _ _) hx
    have hx3 : (3 : ℝ) ≤ x := by linarith [hg.1]
    refine ⟨?_, fun u j hj t ht => ?_, three_le_split_at Fm he h3 hx1 i⟩
    · exact
        { wpos := fun j hj z => by
            have h2 := (windows_at Fm hx1 i hg j hj z).1
            obtain ⟨-, -, -, -, -, -, -, -, hw, -⟩ := size_at Fm hx1 i hg
            linarith
          low := fun u j hj z hz => by
            rw [GlobalTheory.ShapeRows.ent_size Ee u j hj z]
            exact excess_at Fm hx1 i hg u j hj z hz
          top := fun u j hj z hz => by
            rw [GlobalTheory.ShapeRows.ent_size Ee u j hj z, GlobalTheory.ShapeRows.ent_row Ee u j hj z]
            exact top_excess_at Fm hx1 i hg u j hj z hz
          top1 := fun u j hj z hz => by
            rw [GlobalTheory.ShapeRows.ent_row Ee u j hj z]
            exact two_w_at Fm hx1 i hg u j hj z hz
          sizeA := fun u j hj z => by
            rw [GlobalTheory.ShapeRows.ent_size Ee u j hj z]
            exact card_at Fm hx1 i hg u j hj z
          rankA := rank_at Fm hx3 hx1 i
          xa := ⟨xa_at Fm hx1 i hg, GlobalTheory.scale_one_lt_a _⟩
          capW := fun u j hj z => by
            rw [GlobalTheory.ShapeRows.ent_cap Ee u j hj z]
            exact cap_width_at Fm hx1 i hg u j hj z
          alG := fun u j hj t ht => by
            rw [GlobalTheory.ShapeRows.ent_row Ee u j hj, GlobalTheory.ShapeRows.ent_row Ee u j hj]
            exact GlobalTheory.AlTop.al_le_rowLen_sub (Fm.L x i) u j hj t ht
          capG := fun u j hj z => by
            rw [GlobalTheory.ShapeRows.ent_cap Ee u j hj z]
            exact cap_fill_at Fm hx1 i u j hj z }
    · rw [GlobalTheory.ShapeRows.ent_row Ee u j hj, GlobalTheory.ShapeRows.ent_row Ee u j hj]
      exact gap_at Fm hx1 i hg u j hj t ht
  · refine ⟨0, fun Fm x _ _ i Ee => absurd ?_ he⟩
    obtain ⟨i0⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i0]
    exact (Fm.L 0 i0).sc.eps_pos

end GlobalTheory.ShapeUniform
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Pdv

theorem rowAt_of_stdTie : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex), RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (AtAll fun D O c b => GlobalTheory.Pdv.At O.ex (ker D O c b).ent) := by
  intro hA hG hD hI Bd Q Lk ker hE
  choose x0 hx0 using GlobalTheory.ShapeUniform.shape_uniform
  refine ⟨fun κ D O c b => x0 κ.eps ≤ O.L.sc.x ∧ StdTie D O (ker D O c b), ?_, ?_⟩
  · have h1 : RowE Q Lk (fun κ D O _ _ => x0 κ.eps ≤ O.L.sc.x) := by
      unfold RowE EvP
      refine ParEv.of_all fun κ _ => ⟨x0 κ.eps, fun K hk hx β _ c b _ => ?_⟩
      show x0 κ.eps ≤ β.p.L.sc.x
      rw [β.sc]
      exact hx
    exact (h1.and hE).mono fun _ _ _ H => H
  · intro 𝒜 σ s eps Fm hc x hx i
    obtain ⟨κ, hl, _, ht⟩ := s Fm hc
    obtain ⟨_, h0, hst⟩ := ht x hx i
    have hxx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
    have hge : x0 eps ≤ x := by
      have h0' : x0 κ.eps ≤ (Fm.L x i).sc.x := h0
      rw [hl.eps_eq, hxx] at h0'
      exact h0'
    have hsh := hx0 eps Fm x hge hx i
    have hsb : 3 ≤ (Fm.D x i).host.splitBound :=
      (hsh (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) (ker _ _ _ (σ Fm hc x hx i)).ent (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0))).2.2
    exact GlobalTheory.T.kernelDatumConditions_at_standardKernelComparison hA hG hD hI (Fm.D x i) (objAt Fm x hx i) (ker _ _ _ (σ Fm hc x hx i)) hst hsb
      Fm.fixed.2.1.ge Fm.fixed.2.2.1.ge (fun Ee => ⟨(hsh Ee).1, (hsh Ee).2.1⟩)

end GlobalTheory.Pdv
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem servH_row (hA : Formalism.L2.KerInert.AlgTAll) (hG : Formalism.L2.KerInert.GenusOneModelExistsLattice) (hC : Formalism.L2.KerInert.Rep.CurveDict)
    (hI : Formalism.L2.KerInert.IntInert) (hE : GlobalTheory.TwV.Lt.AdmAtEnt2) (hX : GlobalTheory.TwV.Lt.CurveEx) :
    ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex),
      (∀ K X f T c, Q K X f T c → positionOf HasPart K X f T c) →
      RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (ServH ker) := by
  intro Bd Q Lk ker hQ hT
  have hM : RowE Q Lk (fun _ D O _ _ => ModelsAt D O) :=
    RowE.of_all fun _ K β _ _ _ hq _ => GlobalTheory.T.tuplesHaveLocalModels_at_constructedPoint_over_trueColumns hE hX K β (hQ _ _ _ _ _ hq)
  exact Row.and (GlobalTheory.Svd.rowTwU Q Lk hM) (GlobalTheory.Pdv.rowAt_of_stdTie hA hG hC hI Q Lk ker hT)

end GlobalTheory.Svd
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bundle_bothParts_of_standardKernel_and_six_hypotheses : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex), (∀ K X f T c, Q K X f T c → positionOf HasPart K X f T c) → RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (ServH ker) := by
  atlas_forward_decl GlobalTheory.Svd.servH_row
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem servH_row_of_artin :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd)
      (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex),
      (∀ K X f T c, Q K X f T c → positionOf HasPart K X f T c) →
      RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (ServH ker) := by
  intro hA Bd Q Lk ker hQ hE
  have h2 : Formalism.L2.Th1.CM.CM2 := GlobalTheory.Corev.CmTwoClosing.cmGoodModel_of_globalArtinReciprocity hA
  obtain ⟨hT, hG, hC⟩ := GlobalTheory.CurveThetaInert.torsionTaylorAlgebraic_latticeExists_of_cm h2
  exact GlobalTheory.T.bundle_bothParts_of_standardKernel_and_six_hypotheses hT hG hC (GlobalTheory.intInert_of_complexMultiplication_condition h2) (GlobalTheory.TwV.Lt.inert_theta_admissibility_of_complex_multiplication h2)
    (GlobalTheory.TwV.Lt.exists_genusOne_formal_iso_of_unramified_good_reduction h2) Q Lk ker hQ hE

end GlobalTheory.Svd
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bundle_bothParts_of_standardKernel_of_globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex), (∀ K X f T c, Q K X f T c → positionOf HasPart K X f T c) → RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (ServH ker) := by
  atlas_forward_decl GlobalTheory.Svd.servH_row_of_artin
end

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd

namespace GlobalTheory.Svd

theorem servH_row_linkR : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL),
    Row (Bd := BdRec) (IsGoodE p.s) (LinkR p) (ServH (Bd := BdRec) fun _ _ _ R => R.T.ker) := by
  intro hA hL p
  exact GlobalTheory.T.bundle_bothParts_of_standardKernel_of_globalArtinReciprocity hA (Bd := BdRec) (IsGoodE p.s) (LinkR p) (fun _ _ _ R => R.T.ker)
    (fun K X f T c h => (GlobalTheory.Svd.builtC_hasPart p.s).2 K X f T c
      (IsBuiltE.isBuilt K X f T c (IsGoodE.isBuiltE K X f T c h)))
    (GlobalTheory.Svd.LinkStd.linkR_stdTie p (IsGoodE p.s))

end GlobalTheory.Svd
end
