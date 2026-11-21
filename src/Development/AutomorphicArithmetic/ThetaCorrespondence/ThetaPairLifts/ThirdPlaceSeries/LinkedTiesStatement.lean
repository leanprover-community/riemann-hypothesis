import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisorAllStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisorAll
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasExpOfLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEPartTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentReadingBundleStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartSel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentReadingBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisibilityBundleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisibilityBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowOfCovolumeOntoGrid
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TiesOfTiesB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtRealised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
namespace GlobalTheory.ExpTiesOfLayer
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem hasExp_of_layer_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), _root_.GlobalTheory.PlugPt.HasExponent' (_root_.GlobalTheory.HeightCounting.defaultExtension hL) ∧ ∀ (E : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL), (∀ K B f T w Z Wt p0 t nch n xd c, E K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.PlugPt.HasExponent' E := by
  intro hL
  have hNE : _root_.GlobalTheory.PlugPt.HasExponent' (_root_.GlobalTheory.HeightCounting.defaultExtension hL) := by
    intro K B f T w Z Wt p0 t nch n xd c y
    have hg := c.row.grp
    refine ⟨⟨⟨⟨⟨y.ser.ex⟩, ⟨fun g => (hg.lvl0 g).symm, ?_⟩, ?_⟩⟩, PUnit.unit⟩⟩
    · intro i b u hu
      obtain ⟨x, hx, hx'⟩ := hg.psi0 u hu i b
      exact ⟨x, hx, hx'⟩
    · intro i j b a _
      rw [y.xd i ((j : ℕ) + 1) b (by omega) (by omega)]
      exact Set.mem_univ _
  exact ⟨hNE, fun E hE K B f T w Z Wt p0 t nch n xd c e => by
    obtain ⟨y⟩ := hE K B f T w Z Wt p0 t nch n xd c e
    exact hNE K B f T w Z Wt p0 t nch n xd c y⟩
end GlobalTheory.ExpTiesOfLayer
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PlugPt
open GlobalTheory.Mem.R3 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
set_option maxHeartbeats 4000000 in
theorem sidePt_part_of_pack_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (t : b.Comparison₂) {x : R3.TwIn O.ex}
    (y : _root_.GlobalTheory.Mem.R3.RealInAlt x b.R b.S) (h : _root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y) :
    ∃ Tp : Formalism.L2.Host.TupTied D x.R.C O.ex.nch, HEq Tp t.1.Tp ∧
      sidePt (O := O) (b.part t).pt = ({ G := x.G, Pl0 := x.Pl0, I0 := x.I0, T := x.T, A3 := x.A3, J := x.core, R := x.R, P0 := x.F.P0, ψ0 := x.F.ψ0, cG := x.cG, v₀ := x.geo.v₀, S := y.Sx, YS := y.nexp, cf := x.R.C, tp := Tp } : Side D O.ex.nch) := by
  have key : ∀ (p : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S) (_ : p = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y) (Tq : Formalism.L2.Host.TupTied D p.B.Q.Rl.C O.ex.nch),
      ∃ Tp : Formalism.L2.Host.TupTied D x.R.C O.ex.nch, HEq Tp Tq ∧
        ({ G := p.P.Gp, Pl0 := p.P.Pl0, I0 := p.P.I0, T := p.P.T, A3 := p.P.A3, J := p.B.T, alg := p.B.alg, R := p.B.Q.Rl, P0 := p.P.P0, ψ0 := p.P.ψ0, cG := p.B.Q.cG, v₀ := p.B.v₀, S := p.B.Q.Sx, YS := p.B.Q.nexp, cf := p.B.Q.Rl.C, tp := Tq } : Side D O.ex.nch) =
          ({ G := x.G, Pl0 := x.Pl0, I0 := x.I0, T := x.T, A3 := x.A3, J := x.core, R := x.R, P0 := x.F.P0, ψ0 := x.F.ψ0, cG := x.cG, v₀ := x.geo.v₀, S := y.Sx, YS := y.nexp, cf := x.R.C, tp := Tp } : Side D O.ex.nch) := by
    intro p hp Tq
    subst hp
    exact ⟨Tq, HEq.rfl, rfl⟩
  exact key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) h t.1.Tp
set_option maxHeartbeats 4000000 in
theorem pin_pt_of_bundle_witness : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) (hE : _root_.GlobalTheory.PlugPt.HasExponent' N) (K : Ctx) (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (_ : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) q b) (t : b.Comparison₂), _root_.GlobalTheory.PlugPt.pinnedPointOfReading (_root_.GlobalTheory.PlugPt.ExtensionReading.of RX hE (SXE S) (OX Γ)) K q c (b.part t).pt := by
  intro hL N S Γ hE K q c b w t
  obtain ⟨x, a, ax, y, recPin, -, -, sx, eF, fi, -⟩ := w
  obtain rfl := eq_of_heq ax
  obtain ⟨Tp, hTp, h⟩ := _root_.GlobalTheory.PlugPt.sidePt_part_of_pack_alt b t y.y y.eq
  have htp : HEq Tp q.x.n.tp := hTp.trans (t.1.tpEq.trans (Sigma.mk.inj_iff.mp recPin.s.chr).2)
  have hcf : q.x.what₂.r.z.R.C = GlobalTheory.Mem.Col2.TC.cf q.w.I q.w.l q.Z := q.x.what₂.r.z.lev.C
  refine ⟨q.x.what₂.r.z.R.kap, a.lam, a.err, h.trans ?_⟩
  refine side_eq_upd (O := q.O) a.x (_root_.GlobalTheory.PlugPt.sideOf_alt q.x.what₂ q.x.n q.core_data_of_point) q.x.what₂.r.z.R.kap a.lam a.err (reFace q.x.what₂.r.z.F a.Dc a.Sp a.Zsc :)
    y.y.Sx y.y.nexp Tp ?pack rfl HEq.rfl ?v ?S ?fi ?eF hcf htp
  case pack => exact (by with_unfolding_all exact (a.pack :))
  case v => exact (by with_unfolding_all exact (a.v₀ :))
  case S => exact (by with_unfolding_all exact (sx :))
  case fi => exact (by with_unfolding_all exact (fi :))
  case eF => exact (by with_unfolding_all exact (eF :))
end GlobalTheory.PlugPt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_reading_of_hasExp_bundle : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) (hE : _root_.GlobalTheory.PlugPt.HasExponent' N) (K : Ctx) (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (_ : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) q b) (t : b.Comparison₂), _root_.GlobalTheory.PlugPt.pinnedPointOfReading (_root_.GlobalTheory.PlugPt.ExtensionReading.of RX hE (SXE S) (OX Γ)) K q c (b.part t).pt := by
  atlas_forward_decl _root_.GlobalTheory.PlugPt.pin_pt_of_bundle_witness
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop
namespace GlobalTheory.ClassSumPinLink
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end GlobalTheory.ClassSumPinLink
namespace GlobalTheory.ClassSumPinLink
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
section Pack
variable {D : D7} {O : Obj D}
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
def ReadAtAlt {R : _root_.Formalism.L2.RecTAlt O.ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} (k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage R S) : Prop :=
  ∃ Yr : R3.Read (A3 := k.P.A3) k.B.Q.Rl.toRealDat
      (⟨k.P.P0, k.P.ψ0, k.P.Ps, k.P.ψs, k.Dc, k.Sp, k.Zsc⟩ : Face3 D k.P.A3).lv2 O.ex.p0,
    (∀ (i : Fin D.R.m) (v : Fin ((k.P.A3.indefDown k.P.S0).dW i) → D.what₂.LL)
      (y : Fin (Module.finrank D.what₂.LL (k.B.Q.Rl.toRealDat.WL
        (⟨k.P.P0, k.P.ψ0, k.P.Ps, k.P.ψs, k.Dc, k.Sp, k.Zsc⟩ : Face3 D k.P.A3).lv2 false i)) → D.what₂.LL),
      HEq v y → Yr.mj.eW i (k.P.I.jW i v) = (k.B.Q.Rl.FW i).j (sg0 D k.P.A3.A)
        (jDL k.B.Q.Rl (⟨k.P.P0, k.P.ψ0, k.P.Ps, k.P.ψs, k.Dc, k.Sp, k.Zsc⟩ : Face3 D k.P.A3).lv2 i y)) ∧
    GlobalTheory.HeightCounting.EMtTheta Yr k.B.Q.nexp O.ex.nch
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem readAt_rpkX_of_eMtTheta {R : _root_.Formalism.L2.RecTAlt O.ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {x : R3.TwIn O.ex} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R S)
    (h : GlobalTheory.HeightCounting.EMtTheta x.Y y.nexp O.ex.nch) : _root_.GlobalTheory.ClassSumPinLink.ReadAtAlt (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y) := by
  refine ⟨x.Y, ?_, h⟩
  intro i v z hvz
  obtain rfl := eq_of_heq hvz
  exact x.Z.jW_read i v
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem classSumPin_of_readAt_of_pDiv {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (t : b.Comparison₂) (h : _root_.GlobalTheory.ClassSumPinLink.ReadAtAlt (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b)) (hD : _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c (b.part t)) :
    GlobalTheory.ExportPin.ClassSumPin (b.part t).pt := by
  obtain ⟨Yr, h1, h2⟩ := h
  exact classSumPin_of_read (b.part t).pt Yr h1 h2 hD
end Pack
end GlobalTheory.ClassSumPinLink
namespace GlobalTheory.ClassSumPinLink
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem eMtTheta_of_args_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {Z : w.Lt} {Wt : Set B.places.Pl} {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L}
    {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC}
    {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX} (t : RowsT K w Z Wt ex.p0) (n : NchT w Z Wt ex.nch) (c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n)
    (a : R3.TwArgs ex t) (x : R3.TwIn ex) (ax : HEq a.x x) {Sx : RatDat (w.st Z).toD7.ntw} (E : NExpRealS x.R x.cG Sx)
    (hS : HEq Sx (ratDatR (D := (w.st Z).toD7) t.r.z.R t.r.z.cG c.row.kKs c.row.hk))
    (hF : HEq E.eF c.row.nexp.eF) (hi : HEq E.fi c.row.nexp.fi)
    (h : GlobalTheory.HeightCounting.EMtTheta (D := (w.st Z).toD7) t.r.Y c.row.nexp ex.nch) : GlobalTheory.HeightCounting.EMtTheta x.Y E ex.nch := by
  cases ax
  exact eMtTheta_of_pack a.pack a.x.Y t.r.Y a.eW (eq_of_heq hS) E c.row.nexp hF hi h
end GlobalTheory.ClassSumPinLink
namespace GlobalTheory.ClassSumPinLink
set_option maxHeartbeats 4000000 in
theorem pIota_classSumPin_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (_ : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) q b) (t : b.Comparison₂), _root_.GlobalTheory.Fc.Ind.IotaPointSummands _ _ c (b.part t) ∧ (_root_.GlobalTheory.Fc.Ind.DivisorPointSummands _ _ c (b.part t) → GlobalTheory.ExportPin.ClassSumPin (b.part t).pt) := by
  intro hL N S Γ hN K q c b hb t
  refine ⟨?_, fun hD => ?_⟩
  · obtain ⟨sP, sS, -, -, hS⟩ := hb.s
    have key : ∀ S' : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt b.R, S' = sS.toRealSpectralMatching b.R → ∀ x : S'.X.B.I.E, HEq (S'.X.ιE x) x := by
      rintro S' rfl
      exact sP.pin
    exact key b.S hS
  · have hth : GlobalTheory.HeightCounting.EMtTheta hb.x.Y hb.y.y.nexp q.O.ex.nch := by
      obtain ⟨m⟩ := hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2
      exact _root_.GlobalTheory.ClassSumPinLink.eMtTheta_of_args_alt q.x.what₂ q.x.n (_root_.GlobalTheory.Mem.Top.Bl.WPt.core_data_of_point (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) q) hb.a hb.x hb.ax hb.y.y.nexp hb.sx hb.eF hb.fi m.1.th
    have hR : _root_.GlobalTheory.ClassSumPinLink.ReadAtAlt (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) := by
      rw [hb.y.eq]
      exact _root_.GlobalTheory.ClassSumPinLink.readAt_rpkX_of_eMtTheta hb.y.y hth
    exact _root_.GlobalTheory.ClassSumPinLink.classSumPin_of_readAt_of_pDiv b t hR hD
end GlobalTheory.ClassSumPinLink
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_sum_divisibility_of_extensionWithLaw : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (_ : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) q b) (t : b.Comparison₂), _root_.GlobalTheory.Fc.Ind.IotaPointSummands _ _ c (b.part t) ∧ (_root_.GlobalTheory.Fc.Ind.DivisorPointSummands _ _ c (b.part t) → GlobalTheory.ExportPin.ClassSumPin (b.part t).pt) := by
  atlas_forward_decl _root_.GlobalTheory.ClassSumPinLink.pIota_classSumPin_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.FourBoundsAtBundles
theorem tupAllUsed_part_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : Formalism.L2.DIV.TupAllUsed b.P := by
  intro t
  rcases b.pt.charW.tup.mu_used t with h | ⟨w, hw⟩
  · left
    subst h
    exact b.P.tied.div.tup.mu0
  · right
    refine ⟨D.plEq.symm w, ?_⟩
    have e1 := b.pt.tupAt (D.plEq.symm w)
    rw [Equiv.apply_symm_apply] at e1
    have e2 := b.pt.tupTie (D.what₂.muAt (D.plEq.symm w)) (Or.inr ⟨_, rfl⟩)
    rw [e1, hw] at e2
    exact e2
theorem p_div_of_div3g {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) (h : GlobalTheory.Cp.DivRows3G b.P) : _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b :=
  Formalism.L2.DIV.DivRows3G.toRows (_root_.GlobalTheory.Fc.FourBoundsAtBundles.tupAllUsed_part_alt b)
    ⟨h.sharpRR, h.baseRR, h.divisionRows_rationalLift, h.thTheta, ⟨h.num.Ij, h.num.jw, h.num.etaJ⟩, h.colsBk⟩
end GlobalTheory.Fc.FourBoundsAtBundles
namespace GlobalTheory.Fc.FourBoundsAtBundles
end GlobalTheory.Fc.FourBoundsAtBundles
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PlugPt
theorem ties_of_tiesB_alt : ∀ (D : D7) (O : GlobalTheory.EX.OB.Obj D) (c : ℝ) (b : BdPt D O c), TiesB D O c b →
    GlobalTheory.FinalJoin2.FieldSmall D O.L → b.RealisedCondition → GlobalTheory.EX.DQ.TwAllAt D O.ex.nch O.ex.xd → b.CompatibilityConditions := by
  intro D O c b h hF hR htw
  obtain ⟨hc, hpb, -, hL, hD⟩ := GlobalTheory.T.pathCoreConditions_of_intrinsicConditions D O c b h hF
  obtain ⟨hT, hRay⟩ := h
  exact
    { real := hR, core := hc, pb := hpb, types := hT.types, series := hT.series, level := hL, data := hD,
      psiVal := hT.psiVal, ray := hT.small.ray, roots := hT.small.roots, rayQ := hRay, twist := htw }
end GlobalTheory.PlugPt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem pt_realised_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : b.pt.RealisedCondition :=
  ⟨b.R, b.S, b.B, b.pins, b.Rr, b.recPins, rfl⟩
theorem pt_T_pb_eq_R_pb {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : b.pt.T.pb = b.pt.R.C.P.pb :=
  GlobalTheory.PinsFixHalf.pb_eq_of_pins b.pt.T b.pt.R.toRealDat b.pt.κ b.pt.v₀ b.pt.O b.pt.charW.base.lev b.pt.fw.laws b.pt.pins
theorem pt_realised_and_pb_eq : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), b.pt.RealisedCondition ∧ b.pt.T.pb = b.pt.R.C.P.pb :=
  fun _ _ _ b => ⟨_root_.GlobalTheory.Fc.Ind.pt_realised_alt b, _root_.GlobalTheory.Fc.Ind.pt_T_pb_eq_R_pb b⟩
end GlobalTheory.Fc.Ind
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GeoTies
set_option maxHeartbeats 1000000 in
theorem linked_ties_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDivisorCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => Row Q L (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∀ t : b.Comparison₂, _root_.GlobalTheory.Fc.Ind.IotaPointSummands D O c (b.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) := by
  intro hRF hL N S Γ hN hDiv
  have hE : _root_.GlobalTheory.PlugPt.HasExponent' N := (_root_.GlobalTheory.ExpTiesOfLayer.hasExp_of_layer_alt hL).2 N fun K B f T w Z Wt p0 t nch n xd c h =>
    (hN K B f T w Z Wt p0 t nch n xd c h).map Prod.fst
  let ν := _root_.GlobalTheory.PlugPt.ExtensionReading.of RX hE (SXE S) (OX Γ)
  have hRow := _root_.GlobalTheory.PlugPt.rowE_part_ties_alt hRF hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s ν (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (GlobalTheory.Plug.coreCondition_RX _ rfl)
  have hlink : ∀ (K : Ctx) (β : BPt K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition β.D β.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) K β c b → ∀ t : b.Comparison₂,
      linkOf (𝒮 := (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (Bd := _root_.GlobalTheory.Fc.Ind.PointSummands) (fun K q c b => _root_.GlobalTheory.PlugPt.pinnedPointOfReading ν K q c b.pt) K β c (b.part t) := by
    intro K β c b hl t
    obtain ⟨q, b', ⟨w⟩, e⟩ := hl
    have key : ∀ (x y : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c), x = y → ∀ t : x.2.2.Comparison₂, ∃ t' : y.2.2.Comparison₂,
        (⟨x.1, x.2.1, x.2.2.part t⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.Ind.PointSummands D O c) = ⟨y.1, y.2.1, y.2.2.part t'⟩ := by
      rintro x _ rfl t
      exact ⟨t, rfl⟩
    obtain ⟨t', e'⟩ := key ⟨β.D, β.O, b⟩ _ e t
    exact ⟨q, b'.part t', _root_.GlobalTheory.T.exponent_reading_of_hasExp_bundle hL N S Γ hE K q c b' w t', e'⟩
  have hB : RowE (sAnd (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) GlobalTheory.PlugPt.RayPosition) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ))
      (fun _ D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∀ t : b.Comparison₂, GlobalTheory.PlugPt.TiesB D O c (b.part t).pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧
        GlobalTheory.BigOn.More (b.part t).pt) :=
    EvP.mono (fun _ K _ H β hq c b hl t => H β hq c (b.part t) (hlink K β c b hl t)) hRow
  have hR2 : _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => Row Q L (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∀ t : b.Comparison₂,
      GlobalTheory.PlugPt.TiesB D O c (b.part t).pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) :=
    ⟨GlobalTheory.PlugPt.RayPosition, GlobalTheory.Plug.largeBaseProperty_rayProperty hRF KPx _, RowE.row hB⟩
  obtain ⟨R, hR, hrow⟩ := RowL.and (KP := KPx) (Q := IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (Q' := IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s)
    (Lk := _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ)) (H := AtAll _root_.GlobalTheory.Fc.R1.DivisorBundleCondition) hDiv hR2
  refine ⟨R, hR, hrow.imp fun 𝒜 σ s H => ?_⟩
  intro eps Fm hc x hx i
  obtain ⟨κ, -, -, hs⟩ := s Fm hc
  refine Built.ind (R := fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => _root_.GlobalTheory.Fc.R1.DivisorBundleCondition D O c b → (∀ t : b.Comparison₂,
      GlobalTheory.PlugPt.TiesB D O c (b.part t).pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) → ∀ t : b.Comparison₂,
      _root_.GlobalTheory.Fc.Ind.IotaPointSummands D O c (b.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied D O.L ∧
        GlobalTheory.BigOn.More (b.part t).pt) ?_ (hs x hx i).1 (H.1 Fm hc x hx i) (H.2 Fm hc x hx i)
  intro K β c b _ _ hl hdv hT
  have htw : DQ.TwAllAt β.D β.O.ex.nch β.O.ex.xd := twAll_pt β
  obtain ⟨q, b', ⟨w⟩, e⟩ := hl
  have key : ∀ y : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c, y = ⟨q.w.D q.Z, q.O, b'⟩ →
      DQ.TwAllAt y.1 y.2.1.ex.nch y.2.1.ex.xd → _root_.GlobalTheory.Fc.R1.DivisorBundleCondition y.1 y.2.1 c y.2.2 → (∀ t : y.2.2.Comparison₂,
        GlobalTheory.PlugPt.TiesB y.1 y.2.1 c (y.2.2.part t).pt ∧ GlobalTheory.CovTop.RecTied y.1 y.2.1.L ∧ GlobalTheory.BigOn.More (y.2.2.part t).pt) →
      ∀ t : y.2.2.Comparison₂, _root_.GlobalTheory.Fc.Ind.IotaPointSummands y.1 y.2.1 c (y.2.2.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (y.2.2.part t).pt ∧
        (y.2.2.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied y.1 y.2.1.L ∧ GlobalTheory.BigOn.More (y.2.2.part t).pt := by
    rintro _ rfl htw hdv hT t
    obtain ⟨hTB, hRec, hMore⟩ := hT t
    have hcs := _root_.GlobalTheory.T.class_sum_divisibility_of_extensionWithLaw hL N S Γ hN K q c b' w t
    refine ⟨hcs.1, hcs.2 (_root_.GlobalTheory.Fc.FourBoundsAtBundles.p_div_of_div3g _ hdv), ?_, hRec, hMore⟩
    exact _root_.GlobalTheory.PlugPt.ties_of_tiesB_alt _ _ c _ hTB hRec.1 (_root_.GlobalTheory.Fc.Ind.pt_realised_and_pb_eq _ _ c _).1 htw
  exact key ⟨β.D, β.O, b⟩ e htw hdv hT
end GlobalTheory.GeoTies
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_sum_divisor_all_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDivisorCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => Row Q L (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∀ t : b.Comparison₂, _root_.GlobalTheory.Fc.Ind.IotaPointSummands D O c (b.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) := by
  atlas_forward_decl _root_.GlobalTheory.GeoTies.linked_ties_alt
end
end
