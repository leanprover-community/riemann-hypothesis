import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualRowsOfClassSums
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationInputsAllPartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationInputsAllParts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FireStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBOfDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaSumStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FramesExOfRealisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsOfAllPartPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsOfAllPartProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelRowsEqDimensionAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelRowsEqDimensionAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PNmjOfPDivOfClassSumPinStatement

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory
theorem thetaFireRow_recTie_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks), ∀ (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q), Q.Rl.toRealDat.ExAt → Formalism.IndefR.RecTie.ThetaFireRow (Formalism.IndefR.RecTie.toLiftReal Q.Rl.toRealDat Q.F.lv2 Qr.tupT Qr.hm Qr.hTop Qr.hinj) Qr.IL := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S Ks _ _ _ Q Qr e
  exact GlobalTheory.thetaLiftRow_fires_of_weakCharacterisation Q.Rl Q.F Q.charW e P.tied.div.tup.v0 Qr.tupT Qr.hm Qr.hTop Qr.hinj Qr.IL
end GlobalTheory
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_scale_theta_identity_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks), ∀ (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q), Q.Rl.toRealDat.ExAt → Formalism.IndefR.RecTie.ThetaFireRow (Formalism.IndefR.RecTie.toLiftReal Q.Rl.toRealDat Q.F.lv2 Qr.tupT Qr.hm Qr.hTop Qr.hinj) Qr.IL := by
  atlas_forward_decl _root_.GlobalTheory.thetaFireRow_recTie_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framesEx_of_realPins_indefinite_scale : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks), _root_.Formalism.IndefR.IndefiniteRealisationNormalisation Q → Q.FramesEx := by
  first | exact @_root_.GlobalTheory.FramesAtReal.framesEx_of_realisation_alt | exact _root_.GlobalTheory.FramesAtReal.framesEx_of_realisation_alt | (intros; apply _root_.GlobalTheory.FramesAtReal.framesEx_of_realisation_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
namespace GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem atAll_fourRows' : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜),
      AtAll _root_.GlobalTheory.Fc.Ind.FiringPointSummands 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.summandRealBound 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.ThresholdPointSummands 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.FramePointSummands 𝒜 σ := by
  intro hDS hHC hRD hCW 𝒜 σ
  have hF : AtAll _root_.GlobalTheory.Fc.Ind.FiringPointSummands 𝒜 σ := fun Fm hc x hx i =>
    _root_.GlobalTheory.T.indefinite_scale_theta_equality_alt hDS hHC hRD hCW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B
  refine ⟨hF, fun Fm hc x hx i => ?_, fun Fm hc x hx i => ?_, fun Fm hc x hx i => ?_⟩
  · exact _root_.GlobalTheory.T.indefinite_scale_theta_bound_right_alt hRD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B (Fm.parT x hx i).nV_ge (hF Fm hc x hx i).1
  · exact _root_.GlobalTheory.T.indefinite_scale_theta_identity_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B.Q (σ Fm hc x hx i).Rr (hF Fm hc x hx i).1
  · exact _root_.GlobalTheory.T.framesEx_of_realPins_indefinite_scale _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B.Q (σ Fm hc x hx i).pins
end GlobalTheory.Fc.Ind
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fire_realBound_thR_frames_at_all : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.FiringPointSummands 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.summandRealBound 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.ThresholdPointSummands 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.FramePointSummands 𝒜 σ := by
  atlas_forward_decl _root_.GlobalTheory.Fc.Ind.atAll_fourRows'
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR
namespace GlobalTheory.Fc.Ind
theorem base_level_rows_eq_dimension_alt : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.summandDegreeZero D O c b := by
  intro D O c b
  have h1 : D.what₂.D0 = b.P.S0.D := GlobalTheory.rowSide_card_eq_of_coord O.ex.p0.s D.what₂.onb0 b.P.I.eRR0
  have key : ∀ (Z Z' : DefSub b.P.A3.fam3.amb3) (S : IndefData (b.P.A3.side3 b.P.P0 b.P.ψ0 Z))
      (S' : IndefData (b.P.A3.side3 b.P.P0 b.P.ψ0 Z')), Z = Z' → HEq S S' → S.D = S'.D := by
    intro Z Z' S S' h h'
    subst h
    cases eq_of_heq h'
    rfl
  have h2 := key _ _ _ _ b.B.Q.zs b.B.Q.s0
  have h3 := b.B.Q.zs
  unfold _root_.GlobalTheory.Fc.Ind.summandDegreeZero
  rw [h1, ← h2, ← h3]
  rfl
end GlobalTheory.Fc.Ind
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ind_piece_degree_zero : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.summandDegreeZero D O c b := by
  atlas_forward_decl _root_.GlobalTheory.Fc.Ind.base_level_rows_eq_dimension_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.Ind
theorem pRows_of_parts_alt : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.FiringPointSummands D O c b → _root_.GlobalTheory.Fc.Ind.summandRealBound D O c b →
    _root_.GlobalTheory.Fc.Ind.summandPrimitive D O c b → _root_.GlobalTheory.Fc.Ind.FramePointSummands D O c b → _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b → _root_.GlobalTheory.Fc.Ind.NormJumpPointSummands D O c b → Formalism.BasicNotions.GoodFTAll D → b.pt.CompatibilityConditions →
    _root_.GlobalTheory.Fc.Ind.RowPointSummands D O c b := by
  intro D O c b hF hB hP hFr hD hN hG hT
  exact
    { exAt := hF.1
      jEvBar := hF.2.1
      geoAct := hF.2.2.1
      evInj := hF.2.2.2
      ioExt := hB.ioExt
      oneMap := hB.oneMap
      prim := hP.1
      sep := hP.2
      ok := b.ok1
      framesOK := b.B.Q.frames hFr
      divRows := hD
      psi := b.psi
      d0 := _root_.GlobalTheory.T.ind_piece_degree_zero D O c b
      export_ := hN
      goodFT := hG
      w1 := fun w hw => ((b.muDef 0 0).2.2.2 w).2 hw
      ties := hT }
end GlobalTheory.Fc.Ind
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bundle_lines_of_primitive_frames_div_nmj : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.FiringPointSummands D O c b → _root_.GlobalTheory.Fc.Ind.summandRealBound D O c b → _root_.GlobalTheory.Fc.Ind.summandPrimitive D O c b → _root_.GlobalTheory.Fc.Ind.FramePointSummands D O c b → _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b → _root_.GlobalTheory.Fc.Ind.NormJumpPointSummands D O c b → Formalism.BasicNotions.GoodFTAll D → b.pt.CompatibilityConditions → _root_.GlobalTheory.Fc.Ind.RowPointSummands D O c b := by
  atlas_forward_decl _root_.GlobalTheory.Fc.Ind.pRows_of_parts_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.Ind
theorem evW_pRows_of_rows_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (τ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 τ → AtAll _root_.GlobalTheory.Fc.Ind.DivisorPointSummands 𝒜 τ → Ind.EvW (fun D _ _ _ => Formalism.BasicNotions.GoodFTAll D) 𝒜 τ → AtAll (fun D O c (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) => GlobalTheory.ExportPin.ClassSumPin b.pt ∧ b.pt.CompatibilityConditions) 𝒜 τ → Ind.EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 τ := by
  intro hDS hHC hCR hCW 𝒜 τ hPA hDiv hG hPin
  obtain ⟨hF, hRB, -, hFr⟩ := _root_.GlobalTheory.T.fire_realBound_thR_frames_at_all hDS hHC hCR hCW 𝒜 τ
  refine Formalism.MainNotions.Closed.imp hG ?_
  intro eps Fm CH _ h hc
  obtain ⟨x0, hx0⟩ := h hc
  refine ⟨x0, fun x hx h0 i => ?_⟩
  have ha := w3_a hc
  have hp := hPin Fm ha x hx i
  exact _root_.GlobalTheory.T.bundle_lines_of_primitive_frames_div_nmj _ _ _ _ (hF Fm ha x hx i) (hRB Fm ha x hx i) (hPA Fm ha x hx i) (hFr Fm ha x hx i)
    (hDiv Fm ha x hx i) (_root_.GlobalTheory.T.pNmj_of_pDiv_classSumPin _ _ _ _ (hDiv Fm ha x hx i) hp.1) (hx0 x hx h0 i) hp.2
end GlobalTheory.Fc.Ind
end
end
