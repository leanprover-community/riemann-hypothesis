import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DoublingInputsImply
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConditionOfMemberHypotheses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Hypotheses3OfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SiegelWeilDoublingAssembly
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMethodOfEisensteinFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SiegelWeilDoublingAssemblyStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AtDatMultEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DoublingInputsImplyStatement

section
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_zeta_of_eisenstein_facts : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals := by
  first | exact @_root_.ResidueKilled.dm_of_two | exact _root_.ResidueKilled.dm_of_two | (intros; apply _root_.ResidueKilled.dm_of_two <;> assumption)
end
end

section
section
namespace GlobalTheory.PrimIn
theorem twisted_siegel_weil_identity_of_formula :
    GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite →
    GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach →
    GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent →
    GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 →
    GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable →
    _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems := by
  intro q1 q2 q3 q4 q5 q6 q7 sw e1 e2 q10 q11 q12 q14
  exact ⟨q1, q2, q3, q4, q5, q6, q7, sw, _root_.GlobalTheory.T.doubling_zeta_of_eisenstein_facts q2 e1 e2, q10, q11, q12,
    GlobalTheory.weilRepresentationUnitaryPair, q14⟩
end GlobalTheory.PrimIn
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_siegel_weil_identity : GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems := by
  first | exact @_root_.GlobalTheory.PrimIn.twisted_siegel_weil_identity_of_formula | exact _root_.GlobalTheory.PrimIn.twisted_siegel_weil_identity_of_formula | (intros; apply _root_.GlobalTheory.PrimIn.twisted_siegel_weil_identity_of_formula <;> assumption)
end
end

section
section
namespace GlobalTheory
theorem twisted_siegel_weil_identity_of_siegel_weil_formula :
    GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite →
    GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach →
    GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitarySchrodinger →
    GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 →
    GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 =>
    _root_.GlobalTheory.T.twisted_siegel_weil_identity h1 h2 h3 h4 h5 h6 h7 (GlobalTheory.T.siegelWeil_doubledSpace_of_standardUnitary h8) h9 h10 h11 h12 h13 h14
end GlobalTheory
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
noncomputable section
namespace GlobalTheory.Mem.R3.Rw.MultAt
open GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 2000000 in
theorem twisted_local_multiplicity_eq : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation →
    GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing →
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal →
    AtDat fun _ _ _ _ _ _ _ _ z => GlobalTheory.CuspMult.MultEq z.R.toRealDat := by
  intro h1 h2 h3 h4 h5 h6 h7 h12 h13 hG
  have e1 := (evG_of_ev LedRec.ev_exists_sizeData).inter (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)
  have s1 : Step KPx (fun _ _ _ _ => True) _ := Step.of_evLgG (evLgG_of_evLg GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField)
  refine s1.trans (Step.of_evG (e1.imp ?_))
  rintro K - - - - ⟨hLed, hHost⟩ B f T hO - - hOk w hw Z hX Wt z g1 g2 hEx g4
  obtain ⟨Z', g1', hη, hA⟩ := LedRec.exists_bare hG (B := B) (C := w.C) Z f (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨L, hsc, hsz, hpar, hn⟩ := hLed (w.st Z') hO hη hA
  obtain ⟨hhost, -⟩ := hHost (w.st Z') hO
  have s : SameGrp Z Z' := LedRec.sameGrp g1 g1'
  refine (GlobalTheory.T.equalMultiplicities_rowTest_of_sameGroupTransfer B w.C Z Z' w.px w.I hX T Wt s z).1 ?_
  have hEx' := DatCopy.copy_exAt Z' s hEx
  generalize DatCopy.copy Z' s z = y at hEx' ⊢
  have hch := y.pins.char
  have hT : TypesTrue (w.st Z').toD7.ntypes y.R.C.P y.R.C.W := by
    rw [y.lev.C, w.C_eq]
    exact g1'
  exact _root_.GlobalTheory.T.twisted_multiplicity_one h1 h2 h3 h4 h5 h6 h7 h12 h13 hG y.R y.F
    ((hOk w.px w.I hX w.ok w.C_eq w.xi_range).2 _ y.Xg y.tr y.good.irr) hch hEx' hhost ⟨L, hpar⟩ B.ccK_top
    y.pins.keep.guard (GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue hch.base.lev hT)
end GlobalTheory.Mem.R3.Rw.MultAt
end
end
end

section
section
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Mem
theorem member_hodgeHyp_of_localInputs_rationalWeights : _root_.GlobalTheory.Mem.LiteralAutomorphy.MemberHypotheses → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitarySchrodinger → GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → RowRatW → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses :=
  fun m hm dc cw ws sw e1 e2 ud bz so r =>
    _root_.GlobalTheory.Mem.LiteralAutomorphy.condition_of_memberHypotheses dc (_root_.GlobalTheory.twisted_siegel_weil_identity_of_siegel_weil_formula GlobalTheory.Hk3.howeUnram_holds m.m3 m.m4 hm dc cw ws sw e1 e2 ud bz m.m14 so) GlobalTheory.Published.HeckeLPartialContinuation_holds
      (_root_.GlobalTheory.Mem.R3.Rw.MultAt.twisted_local_multiplicity_eq m.m1 m.m2 m.m3 m.m4 m.m5 m.m6 m.m7 m.m12 m.m13 m.m14) r
end GlobalTheory.Mem
end

section
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleSystem_member_rationalWeights : _root_.GlobalTheory.Mem.LiteralAutomorphy.MemberHypotheses → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitarySchrodinger → GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → RowRatW → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses := by
  first | exact @_root_.GlobalTheory.Mem.member_hodgeHyp_of_localInputs_rationalWeights | exact _root_.GlobalTheory.Mem.member_hodgeHyp_of_localInputs_rationalWeights | (intros; apply _root_.GlobalTheory.Mem.member_hodgeHyp_of_localInputs_rationalWeights <;> assumption)
end
end
