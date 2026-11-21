import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalLanglandsPrmReductionStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalLanglandsPrmReduction
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelectedRealizationStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSelectionPairLocalLanglands
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedRealizationGeometricStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedRealizationGeometric
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecInPartsExistsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedLowerMapHoldsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedLowerMapHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerMapSharpAmbientTie
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowerMapTieTw
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHostDatum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedSideRealizationHoldsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedSideRealizationHolds

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selected_realization_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (Del h0 : ℕ) (c : ℝ) (hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH (sS.toRealSpectralMatching R).X u (sS.toRealSpectralMatching R).Y.hK), ∃ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x ∧ ∃ C : _root_.GlobalTheory.Cp.SquareIntegrableColumns R.T (divisionPairOfAdelicFormsFaceColumnsData x), HEq (fun Zs => C.c.face Zs) x.F.Dc ∧ HEq C.Sp x.F.Sp ∧ HEq C.c.W q.B.wts ∧ HEq C.c.Xg q.x.what₂.r.z.Xg ∧ _root_.Formalism.L2.DIV.ColumnCharactersCompatible C.toS ∧ x.F.Zsc = GlobalTheory.Fc.zsc (divisionPairOfAdelicFormsFaceColumnsData x) Del h0 c ∧ HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := (sS.toRealSpectralMatching R).X) (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) (sS.toRealSpectralMatching R).Y.hK (sS.toRealSpectralMatching R).G x.wd (fun m => _root_.Formalism.IndefR.pwOf_alt (sS.toRealSpectralMatching R) hin (x.wd m)) x.bR) ∧ ∃ (κ : ℝ) (sEEc : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H →ₗ⋆[ℂ] Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX (sS.toRealSpectralMatching R).X)), HEq x.sEE sEEc ∧ 0 < κ ∧ ∀ (v : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))), sEEc v = Tw.mk (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (((1 : ℂ) * (κ : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) (sS.toRealSpectralMatching R).X (sS.toRealSpectralMatching R).G (Formalism.L2.SG.RowsJoinPinned.iotaX sP.X sP.inst).toMulEquiv q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c) ⟨x.R.HE.e (Tw.out v), hx⟩) ∧ RealDat.nP x.F.lv2 true * ‖sEEc v‖ ^ 2 = ‖v‖ ^ 2 := by
  atlas_forward_decl _root_.GlobalTheory.Mem.R3.SelectionPairing.exists_selection_pair_local_langlands_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.R3.TwIn.grp GlobalTheory.Mem.R3.TwIn.fin GlobalTheory.Mem.R3.TwIn.alg
namespace GlobalTheory.Mem.R3.SelRealIn
open Formalism.L2.SG.RowsJoinPinned Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta GlobalTheory.Mem.Top.Bl
section Gen
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Gen
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
theorem psi_eq_theta_psi_of_recPin (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex) (h : _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R) (x : TwIn q.O.ex) :
    x.R.ψ = R.T.theta.W.ψ := by
  have h1 := x.pins.keep.std
  have h2 := q.x.th.std
  have e := h.s.theta
  have h3 : Formalism.L2.Theta.IsStdChar (q.w.D q.Z) R.T.theta.W.ψ (-1) :=
    (congrArg (fun z : (Σ a, Formalism.L2.Theta.AllTied (q.w.D q.Z) q.O.ex.th a) => Formalism.L2.Theta.IsStdChar (q.w.D q.Z) z.2.W.ψ (-1)) e).mpr h2
  exact GlobalTheory.StdAdelicChar.isStdChar_unique h1 h3
set_option maxHeartbeats 4000000 in
theorem exists_ratDat_nExpRealS (q : WPt p.s K) (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex) (hx : HEq a.x x) :
    ∃ (Sx : Formalism.IndefR.NX.RatDat (q.w.D q.Z).ntw) (n : Formalism.IndefR.NX.NExpRealS x.R x.cG Sx),
      HEq Sx (Formalism.IndefR.NX.ratDatR (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R q.x.what₂.r.z.cG q.core_data_of_point.row.kKs q.core_data_of_point.row.hk) ∧
      HEq n.eF q.core_data_of_point.row.nexp.eF ∧ HEq n.fi q.core_data_of_point.row.nexp.fi := by
  obtain rfl : a.x = x := eq_of_heq hx
  obtain ⟨Dc, Sp, Zsc, lam, err, _, x, pack, _⟩ := a
  obtain ⟨G, Pl0, I0, T0, A3, core, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  have h := nexp_upd (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R q.x.what₂.r.z.cG _ q.core_data_of_point.row.nexp lam err
  exact (by with_unfolding_all exact (h :))
set_option maxHeartbeats 4000000 in
theorem realIn_exists_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH (sS.toRealSpectralMatching R).X u (sS.toRealSpectralMatching R).Y.hK), HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := (sS.toRealSpectralMatching R).X) (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) (sS.toRealSpectralMatching R).Y.hK (sS.toRealSpectralMatching R).G x.wd (fun m => _root_.Formalism.IndefR.pwOf_alt (sS.toRealSpectralMatching R) hin (x.wd m)) x.bR) → ∀ (κ : ℝ) (sEEc : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H →ₗ⋆[ℂ] Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX (sS.toRealSpectralMatching R).X)), HEq x.sEE sEEc → 0 < κ → (∀ (v : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))), sEEc v = Tw.mk (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (((1 : ℂ) * (κ : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) (sS.toRealSpectralMatching R).X (sS.toRealSpectralMatching R).G (Formalism.L2.SG.RowsJoinPinned.iotaX sP.X sP.inst).toMulEquiv q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c) ⟨x.R.HE.e (Tw.out v), hx⟩) ∧ RealDat.nP x.F.lv2 true * ‖sEEc v‖ ^ 2 = ‖v‖ ^ 2) → ∃ y : _root_.GlobalTheory.Mem.R3.RealInAlt x R (sS.toRealSpectralMatching R), HEq y.tS q.saturationAtWeightedPoint.t ∧ y.cS = q.saturationAtWeightedPoint.c ∧ HEq y.Sx (Formalism.IndefR.NX.ratDatR (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R q.x.what₂.r.z.cG q.core_data_of_point.row.kKs q.core_data_of_point.row.hk) ∧ HEq y.nexp.eF q.core_data_of_point.row.nexp.eF ∧ HEq y.nexp.fi q.core_data_of_point.row.nexp.fi ∧ y.uS = 1 := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 hL N Γ p hp hNE K q hHost hMult R hPin sP sS hsP hsS a x hax hin hsp κ sEEc hsEE hκ hdef
  obtain ⟨hsee, hev, -⟩ := GlobalTheory.Mem.R3.StageMove.spectralStage_point_rowPlacement_transfer K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a _ q.saturationAtWeightedPoint
  obtain ⟨Sx, nx, hSx, heF, hfi⟩ := _root_.GlobalTheory.Mem.R3.SelRealIn.exists_ratDat_nExpRealS q a x hax
  have hψ := _root_.GlobalTheory.Mem.R3.SelRealIn.psi_eq_theta_psi_of_recPin q R hPin x
  have eax : a.x = x := eq_of_heq hax
  rw [eax] at hsee hev
  obtain ⟨hH, -, -, hpos, -, -, hV, hX⟩ := hHost (q.w.st q.Z) q.x.isOver
  have hc : R.T.cols = q.x.col.C := hPin.s.cols
  have hF : (fun u => (R.T.cols.forms u).to0) = fun u => (q.x.col.C.forms u).to0 := by rw [hc]
  have e : (⟨_, sP⟩ : Σ F : ∀ u, Formalism.L2.Forms.Forms0 (q.w.D q.Z) u, GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) F) = ⟨_, q.saturationAtWeightedPoint.P⟩ :=
    Sigma.ext hF hsP
  have hm := (congrArg (fun z : (Σ F : ∀ u, Formalism.L2.Forms.Forms0 (q.w.D q.Z) u, GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) F) =>
      SeeAt x.R.toRealDat x.F.lv2 z.2.X z.2.inst q.saturationAtWeightedPoint.t ∧
      EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) z.2.X z.2.G
        (iotaX z.2.X z.2.inst).toMulEquiv q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c) e).mpr ⟨hsee, hev⟩
  refine ⟨{ psiPin := hψ
            hin := hin
            spPin := (by with_unfolding_all exact (hsp :))
            Sx := Sx
            nexp := nx
            stdV := (by with_unfolding_all exact (hV :))
            stdX := (by with_unfolding_all exact (hX :))
            tS := q.saturationAtWeightedPoint.t
            cS := q.saturationAtWeightedPoint.c
            κS := κ
            ιS := (iotaX sP.X sP.inst).toMulEquiv
            instEq := (by with_unfolding_all exact (sP.inst :))
            ιS_eq := (by with_unfolding_all exact ((GlobalTheory.Mem.JIota.heq_iota_iff (q.w.D q.Z) sP.X sP.inst (iotaX sP.X sP.inst).toMulEquiv).2 rfl :))
            sEEc := sEEc
            sEEj := hsEE
            seeLev := fun _ => (by with_unfolding_all exact (hm.1.conj :))
            seeEval := fun _ => (by with_unfolding_all exact (hm.2 :))
            uS := 1
            uS_norm := norm_one
            seeDef := fun v hx => (by with_unfolding_all exact ((hdef v hx).1 :))
            seeK := ⟨hκ, fun _ v hx => (by with_unfolding_all exact ((hdef v hx).2 :))⟩
            host := (by with_unfolding_all exact (hH :))
            vpos := (by with_unfolding_all exact (hpos :)) }, HEq.rfl, rfl, hSx, heF, hfi, rfl⟩
end GlobalTheory.Mem.R3.SelRealIn
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selected_realization_geometric_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH (sS.toRealSpectralMatching R).X u (sS.toRealSpectralMatching R).Y.hK), HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := (sS.toRealSpectralMatching R).X) (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) (sS.toRealSpectralMatching R).Y.hK (sS.toRealSpectralMatching R).G x.wd (fun m => _root_.Formalism.IndefR.pwOf_alt (sS.toRealSpectralMatching R) hin (x.wd m)) x.bR) → ∀ (κ : ℝ) (sEEc : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H →ₗ⋆[ℂ] Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX (sS.toRealSpectralMatching R).X)), HEq x.sEE sEEc → 0 < κ → (∀ (v : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))), sEEc v = Tw.mk (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (((1 : ℂ) * (κ : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) (sS.toRealSpectralMatching R).X (sS.toRealSpectralMatching R).G (Formalism.L2.SG.RowsJoinPinned.iotaX sP.X sP.inst).toMulEquiv q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c) ⟨x.R.HE.e (Tw.out v), hx⟩) ∧ RealDat.nP x.F.lv2 true * ‖sEEc v‖ ^ 2 = ‖v‖ ^ 2) → ∃ y : _root_.GlobalTheory.Mem.R3.RealInAlt x R (sS.toRealSpectralMatching R), HEq y.tS q.saturationAtWeightedPoint.t ∧ y.cS = q.saturationAtWeightedPoint.c ∧ HEq y.Sx (Formalism.IndefR.NX.ratDatR (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R q.x.what₂.r.z.cG q.core_data_of_point.row.kKs q.core_data_of_point.row.hk) ∧ HEq y.nexp.eF q.core_data_of_point.row.nexp.eF ∧ HEq y.nexp.fi q.core_data_of_point.row.nexp.fi ∧ y.uS = 1 := by
  atlas_forward_decl _root_.GlobalTheory.Mem.R3.SelRealIn.realIn_exists_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3
theorem lower_map_sharp_ambient_tie_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (T : _root_.Formalism.L2.TiedDataSKAlt ex), (∀ u, LowerMapTieS (T.cols.forms u)) → (∀ u μ (hμ : μ ≠ D.what₂.mu0) (_ : ∃ w, μ = D.what₂.muAt w) (h1 : 1 ≤ D.R.m), _root_.Formalism.L2.Rows.LowerMapTieTwAlt T u μ hμ h1) → (∃ J, AmbTie D x.A3.A (RowSide.sharp D) ex.amb x.F.P1 x.F.ψ1 x.Y.tup x.Y.jA J) → ((∀ (t : x.T) (c : (x.A3.A.fam.R t).S.Cl), Fintype.card ((x.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧ ∀ (j : Fin D.R.m) (t : x.T) (c : (x.A3.A.fam.L j t).S.Cl), Fintype.card ((x.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) → _root_.Formalism.L2.Rows.RowSideDeterminedAlt T (divisionPairOfAdelicFormsFaceColumnsData x) := by
  intro D L hT Gi Gl K Yd cX ex x T hL hLt hA hG
  exact
    { lowerMap := hL
      lowerMapTw := hLt
      buDef := x.Y.bu
      ambS := hA
      faces := ⟨x.F.Dc, x.F.Sp, rfl, HEq.rfl⟩
      gamDvd := hG }
end GlobalTheory.Mem.R3
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3.SelRowPin
set_option maxHeartbeats 4000000 in
theorem selected_lower_map_third_stage_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → _root_.Formalism.L2.Rows.RowSideDeterminedAlt R.T (divisionPairOfAdelicFormsFaceColumnsData x) := by
  intro _ _ _ _ _ _ _ _ _ hL N Γ p hp _ K q _ _ R hR sP sS _ _ a x hax
  obtain rfl := eq_of_heq hax
  obtain ⟨he, hTw⟩ := hR.s.tw
  have hC : TC.StdC q.w.I q.w.l q.Z R.T.cols := hR.s.cols ▸ q.x.col.std
  apply _root_.GlobalTheory.Mem.R3.lower_map_sharp_ambient_tie_alt _ _ _ _ _ _ _ _ q.O.ex a.x R.T
  · exact fun u => GlobalTheory.Mem.Col2.LowerTie.lowerMap_tie q.w.I q.w.ok q.w.pins q.w.l q.Z u _ _ _ (hC u)
  · exact fun u μ hμ _ h1 => _root_.GlobalTheory.Mem.Col2.LowerTie.lowerMap_tieTw_alt q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ _ _ _ _ _ _ q.O.ex R.T he hC hTw u μ hμ h1
  · cases a with
    | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
    cases x with
    | mk G Pl0 I0 T' A3 core R' F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
    cases pack
    exact amb_of_eq rfl (eq_of_heq htup) hjA q.x.obj.amb.1
  · cases a with
    | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
    cases x with
    | mk G Pl0 I0 T' A3 core R' F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
    cases pack
    exact GlobalTheory.Mem.R3.GamDvd.gamDvd q.w.I q.x.what₂.hX _ _ _ q.w.l q.Z
end GlobalTheory.Mem.R3.SelRowPin
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selected_lower_map_holds_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → _root_.Formalism.L2.Rows.RowSideDeterminedAlt R.T (divisionPairOfAdelicFormsFaceColumnsData x) := by
  atlas_forward_decl _root_.GlobalTheory.Mem.R3.SelRowPin.selected_lower_map_third_stage_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3.SelSideW
end GlobalTheory.Mem.R3.SelSideW
namespace GlobalTheory.Mem.R3.SelSideW
theorem de_pin_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (v)
    (h : (((q.w.D q.Z).host.pde : ℕ) : 𝓞 (q.w.D q.Z).host.E) ∈ (q.core_data_of_point.a.Pq v).asIdeal) :
    (q.core_data_of_point.a.Pq v).under (𝓞 (q.w.D q.Z).host.K) = q.x.pin.d3b.pK := by
  have hm : q.core_data_of_point.a.Pq v ∈ Set.range q.w.I.sel := q.core_data_of_point.sel ▸ Set.mem_range_self v
  obtain ⟨v', hv'⟩ := hm
  have ha := q.x.pin.above v'
  have hv : OverPF q.B.host q.B.host.pde v' := by
    unfold OverPF
    have h1 : (q.w.I.sel v').asIdeal.comap (algebraMap (𝓞 q.B.host.F) (𝓞 q.B.host.E)) = v'.asIdeal := by
      have := (Set.Finite.mem_toFinset _).1 ha
      first | exact this | exact this.symm | exact congrArg HeightOneSpectrum.asIdeal this
    rw [← h1, Ideal.mem_comap, map_natCast, hv']
    exact h
  have := (q.x.pin.d3b.P_mem v' hv).2
  rw [← q.x.pin.selectedPlacesAgree.1 v' hv] at this
  rw [← hv']
  exact this
theorem under_Pq_eq_pK'_of_pde'_mem {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (v)
    (h : (((q.w.D q.Z).host.pde' : ℕ) : 𝓞 (q.w.D q.Z).host.E) ∈ (q.core_data_of_point.a.Pq v).asIdeal) :
    (q.core_data_of_point.a.Pq v).under (𝓞 (q.w.D q.Z).host.K) = q.x.pin.d3b.pK' := by
  have hm : q.core_data_of_point.a.Pq v ∈ Set.range q.w.I.sel := q.core_data_of_point.sel ▸ Set.mem_range_self v
  obtain ⟨v', hv'⟩ := hm
  have ha := q.x.pin.above v'
  have hv : OverPF q.B.host q.B.host.pde' v' := by
    unfold OverPF
    have h1 : (q.w.I.sel v').asIdeal.comap (algebraMap (𝓞 q.B.host.F) (𝓞 q.B.host.E)) = v'.asIdeal := by
      have := (Set.Finite.mem_toFinset _).1 ha
      first | exact this | exact this.symm | exact congrArg HeightOneSpectrum.asIdeal this
    rw [← h1, Ideal.mem_comap, map_natCast, hv']
    exact h
  have := (q.x.pin.d3b.P'_mem v' hv).2
  rw [← q.x.pin.selectedPlacesAgree.2 v' hv] at this
  rw [← hv']
  exact this
open Classical in
set_option maxHeartbeats 4000000 in
theorem selected_side_realization_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R (sS.toRealSpectralMatching R)) (r : _root_.GlobalTheory.Mem.R3.RecursiveInput y) (HD : _root_.Formalism.L2.HostDatumWithTies R.T.toTiedDataS), HD.d3b = q.x.pin.d3b → _root_.Formalism.L2.SelectedSideOfRealRecord R (divisionPairOfAdelicFormsFaceColumnsData x) (_root_.GlobalTheory.Mem.R3.realisationOfInput y) (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r) HD q.core_data_of_point.a.Pq := by
  intro _ _ _ _ _ _ _ _ _ hL N Γ p hp _ K q _ _ R hR sP sS _ _ a x ax y r HD hHD
  have hQ := qe_image_std q.w q.Z R.T.ker hR.k.std
  have hsel : Set.range q.core_data_of_point.a.Pq = Set.range q.w.I.sel := q.core_data_of_point.sel
  have hlev0 := (twArgs_lev K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a).2.2.1
  have hlev : ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.st q.Z).toD7 μ → HEq (x.R.Q (x.Y.tupT μ)) (q.w.I.Q μ) := by
    have key : ∀ x' : TwIn q.O.ex, a.x = x' →
        ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.st q.Z).toD7 μ → HEq (x'.R.Q (x'.Y.tupT μ)) (q.w.I.Q μ) := by
      rintro x' rfl μ hμ
      exact (hlev0 μ hμ).1
    exact key x (eq_of_heq ax)
  refine ⟨⟨q.core_data_of_point.a.Pq_over, ?_⟩, ?_, ?_, ?_⟩
  · intro μ P hP P' hC
    have hP'eq : P' = Host.CT.plMap R.T.ker.seam.iE P :=
      HeightOneSpectrum.ext (hC.trans (SelJ.carried_plMap R.T.ker.seam P).symm)
    subst hP'eq
    have hm : Host.CT.plMap R.T.ker.seam.iE P ∈ q.w.I.Q μ := hQ μ ▸ Finset.mem_image_of_mem _ hP
    obtain ⟨v, -, hv, -⟩ := q.w.I.exists_of_mem_Q hm
    rw [hsel]
    exact ⟨v, hv⟩
  · intro μ hμ
    rw [hQ μ]
    exact (eq_of_heq (hlev μ hμ)).symm
  · intro v hv
    rw [hHD]
    exact _root_.GlobalTheory.Mem.R3.SelSideW.de_pin_alt q v hv
  · intro v hv
    rw [hHD]
    exact _root_.GlobalTheory.Mem.R3.SelSideW.under_Pq_eq_pK'_of_pde'_mem q v hv
end GlobalTheory.Mem.R3.SelSideW
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selected_side_realization_holds_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R (sS.toRealSpectralMatching R)) (r : _root_.GlobalTheory.Mem.R3.RecursiveInput y) (HD : _root_.Formalism.L2.HostDatumWithTies R.T.toTiedDataS), HD.d3b = q.x.pin.d3b → _root_.Formalism.L2.SelectedSideOfRealRecord R (divisionPairOfAdelicFormsFaceColumnsData x) (_root_.GlobalTheory.Mem.R3.realisationOfInput y) (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r) HD q.core_data_of_point.a.Pq := by
  atlas_forward_decl _root_.GlobalTheory.Mem.R3.SelSideW.selected_side_realization_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3.SelAll
theorem rpk_eq_alt {D : D7} {O : Obj D} {R : _root_.Formalism.L2.RecTAlt O.ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} (P : Formalism.L2.Rows.RowSideFamily O.ex)
    {Dc Dc' : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Sp : ∀ Zs, SPer (Dc Zs)} {Sp' : ∀ Zs, SPer (Dc' Zs)}
    {Z Z' : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {B : _root_.Formalism.IndefR.RealTBAlt R P Dc Sp Z S} {B' : _root_.Formalism.IndefR.RealTBAlt R P Dc' Sp' Z' S}
    (h1 : Dc = Dc') (h2 : HEq Sp Sp') (h3 : Z = Z') (h4 : HEq B B') :
    (⟨P, Dc, Sp, Z, B⟩ : _root_.GlobalTheory.Mem.Top.Bl.RealPackage R S) = ⟨P, Dc', Sp', Z', B'⟩ := by
  subst h1; subst h3; cases h2; cases h4; rfl
theorem real_tb_congr_of_heq {D : D7} {O : Obj D} (R : _root_.Formalism.L2.RecTAlt O.ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (P : Formalism.L2.Rows.RowSideFamily O.ex)
    {Dc Dc' : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Sp : ∀ Zs, SPer (Dc Zs)} {Sp' : ∀ Zs, SPer (Dc' Zs)}
    {Z Z' : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    (h1 : Dc = Dc') (h2 : HEq Sp Sp') (h3 : Z = Z') :
    _root_.Formalism.IndefR.RealTBAlt R P Dc Sp Z S = _root_.Formalism.IndefR.RealTBAlt R P Dc' Sp' Z' S := by
  subst h1; subst h3; cases h2; rfl
set_option maxHeartbeats 4000000 in
theorem bwit_exists_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat) → GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (c : ℝ) (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}), q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) := by
  intro hG hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN hM
  refine ((GlobalTheory.Fc.EvP.of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).and hM).mono ?_
  rintro κ K - ⟨hH, hMK⟩ q R hR c DH _ _
  have hMq := hMK q
  have hcols : R.T.cols = q.x.col.C := hR.s.cols
  obtain ⟨sP, sS, hP, hS⟩ : ∃ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP),
      HEq sP q.saturationAtWeightedPoint.P ∧ HEq sS q.saturationAtWeightedPoint.S := by
    rw [hcols]; exact ⟨q.saturationAtWeightedPoint.P, q.saturationAtWeightedPoint.S, HEq.rfl, HEq.rfl⟩
  have hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH (sS.toRealSpectralMatching R).X u (sS.toRealSpectralMatching R).Y.hK := sP.fin.inHH
  obtain ⟨a, x, ax, C, hDc, hSp, hW', hXg, hCP, hZ, hsp, κS, sEEc, hsE, hκ, hsee⟩ :=
    _root_.GlobalTheory.T.exists_selected_realization_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS DH.1.1 DH.1.2 c hin
  obtain ⟨y, hyt, hyc, hySx, hyeF, hyfi, hyu⟩ := _root_.GlobalTheory.T.selected_realization_geometric_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS a x ax hin hsp κS sEEc hsE hκ hsee
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.T.selected_realization_side_alt hG hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS a x ax y
  have pin := _root_.GlobalTheory.T.selected_lower_map_holds_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS a x ax
  obtain ⟨HD, hHD⟩ := _root_.GlobalTheory.HostDatumExists.exists_hostDatum_alt hGAR _ _ _ _ _ _ _ _ q.O.ex R.T.toTiedDataS (GlobalTheory.Mem.Top.Bl.hostPins_wpt hRF _ _ q) q.x.pin.d3b
  have side := _root_.GlobalTheory.T.selected_side_realization_holds_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS a x ax y r HD hHD
  have h1 : C.c.face = x.F.Dc := eq_of_heq hDc
  have h3 : GlobalTheory.Fc.zsc (divisionPairOfAdelicFormsFaceColumnsData x) DH.1.1 DH.1.2 c = x.F.Zsc := hZ.symm
  have hB := _root_.GlobalTheory.Mem.R3.SelAll.real_tb_congr_of_heq R (sS.toRealSpectralMatching R) (divisionPairOfAdelicFormsFaceColumnsData x) h1 hSp h3
  have hx : Holds x.R x.F := by
    have e : a.x = x := eq_of_heq ax
    rw [← e]; exact a.intersectionNumber_baseChange
  let b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c := ⟨R, sS.toRealSpectralMatching R, divisionPairOfAdelicFormsFaceColumnsData x, pin, DH, C, cast hB.symm (_root_.GlobalTheory.Mem.R3.boundedRealisationOfInput y)⟩
  have heq : _root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y := _root_.GlobalTheory.Mem.R3.SelAll.rpk_eq_alt (divisionPairOfAdelicFormsFaceColumnsData x) h1 hSp h3 (cast_heq _ _)
  exact ⟨b, rfl, ⟨{ x := x, a := a, ax := ax, y := ⟨hx, y, r, heq, HD⟩, recPin := hR, s := ⟨sP, sS, hP, hS, rfl⟩, pt := ⟨hyt, hyc⟩, sx := hySx, eF := hyeF, fi := hyfi, uS := hyu, parts := hr, cW := ⟨hW', hXg⟩, d3b := heq_of_eq hHD, side := side, colPins := hCP }⟩⟩
end GlobalTheory.Mem.R3.SelAll
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_prm_reduction_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat) → GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (c : ℝ) (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}), q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) := by
  atlas_forward_decl _root_.GlobalTheory.Mem.R3.SelAll.bwit_exists_alt
end
end
