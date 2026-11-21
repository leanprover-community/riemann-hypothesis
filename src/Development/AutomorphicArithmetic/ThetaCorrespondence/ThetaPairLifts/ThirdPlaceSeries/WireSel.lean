import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WireSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefiniteRealisationChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieTwRecOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FiniteTOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseRankEqOfRealisation
import Formalism.LocalToGlobal.Wire4F
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GammaSizeOfParameters
import Formalism.LocalToGlobal.InpAtOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtKOfReal

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.L2.RowDataTransport
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
theorem inpAt_of_alt [IsTotallyComplex D.what₂.LL] {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {X : Formalism.L2.Col.Fields}
    {e : X.Tau → (X.E →+* D.what₂.LL)} {c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs}
    {Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)} {Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P c.face Sp Zsc S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT P c.face Sp Zsc) Q.sEE (hkCan P.A3) Cl CHl) (hI : PassIn3 Q.Rl (faceT P c.face Sp Zsc) Cl CHl)
    (Del h0 : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : P.A3.fam3.base3.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1)
    (Ce : ℝ) (hDIV : ∀ j ∈ SizeData₂.lifts D, Formalism.MainNotions.DIVinN_at L j Ce)
    (hTw : TieTwRec L (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.Tw)
    (hD : D.what₂.D0 = (P.A3.A.fam.R P.A3.A.fam.μ0).dZ (P.A3.A.fam.lvl P.P0 P.ψ0)
      ((_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs.Z P.A3.A.fam.μ0))
    (h11 : LiftExponentAtTwisted P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs)
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.μ (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.Tw
      (Zsc (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).J0)
    (hdgA : ∃ dg : ℕ, 0 < dg ∧ (∀ j t, (P.A3.A.fam.L j t).DG (P.A3.A.fam.lvlA P.P0 P.ψ0) ∣ dg) ∧
      ∀ u, ArithAt P.A3 s P.P0 P.ψ0 P.Ps P.ψs c.face Sp Zsc _ Cl CHl (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI)
        (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u))
        (fun _ => divSize L Ce) dg)
    (what₂ : ∀ (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).a w) → D.what₂.LL))
      (I : DivisionCompatibilityDataThreeSided D P.A3 P.P0 P.ψ0 P.Ps P.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.toIndefData (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.toIndefData ex.p0
        (c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs)),
      DivTied3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.toIndefData (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.toIndefData ex.p0
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.col NuC I →
      HEq I P.I → ∀ u, RowsU c (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI)
        (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u))
        (I.wU u) (Cons.nuOf L u (I.eNu u))) :
    _root_.Formalism.L2.RowDataTransport.InpAtAlt c Q hOk hsep Cl CHl hP hI Del h0 lam0 C0 ce Ch Sw C1 eJ H := by
  intro NuC I hT hI'
  obtain ⟨dg, hdg, hdvd, hA⟩ := hdgA
  have hN := inEta3_num (G := P.Gp) L P.A3 (P0 := P.P0) (ψ0 := P.ψ0) (Zs := (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs)
    (S0 := (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.toIndefData) (tup := I.tup) Ce hDIV rfl hT.num hTw hD
  have hr := what₂ NuC I hT hI'
  choose ch T hF hrest using hr
  choose X0 hX0 hn hnP cb hrest2 using hrest
  refine ⟨fun u => ((DivisionInputsWithoutNorm.ofRows (hrest2 u).2.2.2 (Formalism.L2.DIV.Cons.sgRec_fin L u) (hrest2 u).2.1 (hrest2 u).2.2.1
      (X0 u) (hX0 u) (ch u) (hn u) (hnP u) (cb u) (hrest2 u).1 h11 dg hdg hdvd (hA u)).toDef hN).toDivInputs0R hOk hsep,
    fun u => T u, fun u => hF u⟩
end Formalism.L2.RowDataTransport
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S
namespace Formalism.L2.Top4Wire2
variable {𝒜 : FamClass} {sel : _root_.Formalism.L2.TwistSelection 𝒜} {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel}
  {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP} {selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel}
theorem wire4F_alt [∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (i : Fm.Ix x), IsTotallyComplex (Fm.D x i).what₂.LL]
    (selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK) (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel selI)
    (OneMapRow : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop)
    (Cabs : ℝ) (hCabs : 1 ≤ Cabs)
    (hTw : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      TieTwRec (Fm.L x i) (selP Fm hc x hx h i).1.S0.Tw)
    (hD0 : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      (Fm.D x i).what₂.D0 = ((selP Fm hc x hx h i).1.A3.A.fam.R (selP Fm hc x hx h i).1.A3.A.fam.μ0).dZ ((selP Fm hc x hx h i).1.A3.A.fam.lvl (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0)
        ((selP Fm hc x hx h i).1.Zs.Z (selP Fm hc x hx h i).1.A3.A.fam.μ0))
    (hPt : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      RowsHoldDcPt3 (selP Fm hc x hx h i).1)
    (hR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      DivRows3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps (selP Fm hc x hx h i).1.ψs (selP Fm hc x hx h i).1.Zs (selP Fm hc x hx h i).1.S0 (selP Fm hc x hx h i).1.S1 (Fm.ex x hx i).p0 (selP Fm hc x hx h i).1.C (selP Fm hc x hx h i).1.NuC (selP Fm hc x hx h i).1.I)
    :
    _root_.Formalism.L2.Top4.Wire4Alt sel selS selP selDH selC selK selI hPA (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt selI Fm hc x hx h i C CH)
      OneMapRow Cabs := by
  intro eps Fm hc CH hCsz hDG hRows hOne _hBu hN
  obtain ⟨Ce, x3, hCe⟩ := id hN
  obtain ⟨Cd, x4, hFDG⟩ := hDG
  obtain ⟨C, hC, x1, hr⟩ := hRows
  obtain ⟨x2, ho⟩ := hOne
  refine ⟨max 0 (max (50 * c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct + 10)
      (60 * ceF C Ce (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct))),
    max (max x1 x2) (max (max x3 x4)
      (x0F eps Fm.Ct Fm.Cc CH (ceF C Ce (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct)))),
    fun x hx0 hx h i => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0
  have hx3 : x3 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx0
  have hx4 : x4 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx0
  have hx5 : x0F eps Fm.Ct Fm.Cc CH (ceF C Ce (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct)) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx0
  obtain ⟨ra, hd⟩ := hr x hx h hx1 i
  obtain ⟨prows, hsep⟩ := hPA Fm (d3_a hc) x hx h i
  have hok1 := (selC Fm (d3_a hc) x hx h i).ok1
  have hP : CovolumeOntoIsometryConditions (selI Fm (d3_a hc) x hx h i).Rl (selI Fm (d3_a hc) x hx h i).F (selI Fm (d3_a hc) x hx h i).sEE (hkCan (selP Fm (d3_a hc) x hx h i).1.A3) C CH :=
    { toPrimRows3 := prows, w1 := ra.w1, covol := ra.covol, onto := ra.onto hN, lamLow := ra.lamLow (ho x hx h hx2 i),
      seeIso := ra.seeIso, miStar := ra.miStar, fun0 := ra.fun0 hN }
  have hZs : (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).Zs = (selP Fm (d3_a hc) x hx h i).1.Zs := (selI Fm (d3_a hc) x hx h i).zs
  have hS0 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).core.base.toIndefData (selP Fm (d3_a hc) x hx h i).1.S0 := (selI Fm (d3_a hc) x hx h i).s0
  have hS := Fm.sizes x hx i
  have hFD : FactDGam (Fm.D x i) (max Cd 0) := J.factDGam_mono (hFDG x hx4 i) (le_max_left _ _)
  have hDGp := _root_.Formalism.L2.DIV.Cons.gamma_size_of_sizeData_alt (selP Fm (d3_a hc) x hx h i).2 (_root_.Formalism.L2.Top4Wire2.finite_T_of_squareIntegrableColumns (selC Fm (d3_a hc) x hx h i))
    hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hS.2.2.2.2.2.1 (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2 (Fm.L x i).Nc (cloudConstant_nonneg (Fm.L x i))
    (max Cd 0) (le_max_right _ _) hFD
  have eCc : (Fm.L x i).Cc = Fm.Cc := Fm.Cc_eq x i
  have eCt : (Fm.L x i).Ct = Fm.Ct := Fm.Ct_eq x i
  have eCY : (Fm.params x hx i).CYL = Fm.CYL := Fm.params_CYL x hx i
  have hxL : x0F (Fm.L x i).sc.eps (Fm.L x i).Ct (Fm.L x i).Cc CH
      (ceF C Ce (2 + 9 * max Cd 0) (c0F Fm.Csz (Fm.L x i).Cc (Fm.params x hx i).CYL (Fm.L x i).Ct)) ≤ (Fm.L x i).sc.x := by
    rw [Fm.L_eps x i, eCt, eCc, eCY, Fm.L_x x i hx]
    exact hx5
  obtain ⟨lam0, Sw, C1, H, dg, hdg, hdvd, hA⟩ := arithClause_rec (Fm.L x i) (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2 hS (selDH Fm (d3_a hc) x hx h i).2.1 (selDH Fm (d3_a hc) x hx h i).2.2 (Fm.params x hx i) (Fm.ex x hx i).fdef
    (Fm.ex x hx i).kap_def (selP Fm (d3_a hc) x hx h i).1.A3 (selP Fm (d3_a hc) x hx h i).1.tied.div.grp.card (selP Fm (d3_a hc) x hx h i).1.P0 (selP Fm (d3_a hc) x hx h i).1.ψ0 (selP Fm (d3_a hc) x hx h i).1.Ps (selP Fm (d3_a hc) x hx h i).1.ψs (selC Fm (d3_a hc) x hx h i).c.face (selC Fm (d3_a hc) x hx h i).Sp _ C CH Fm.Csz Ce
    (2 + 9 * max Cd 0) (_root_.Formalism.L2.Top4Wire2.finite_T_of_squareIntegrableColumns (selC Fm (d3_a hc) x hx h i)) hDGp hC hCsz hxL (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass)
  have e0 : c0F Fm.Csz (Fm.L x i).Cc (Fm.params x hx i).CYL (Fm.L x i).Ct = c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct := by
    rw [eCc, eCY, eCt]
  exact _root_.Formalism.L2.RowDataTransport.ptK_of_real_alt ((sel Fm (d3_a hc)).2 x hx h i) ((_root_.Formalism.L2.Top4.RankOfDivisionKernel sel selS selP selDH selC selK selI hPA Fm hc).2 x hx h i) rfl
    (selP Fm (d3_a hc) x hx h i).2 ra.kap (hPt Fm (d3_a hc) x hx h i) (hR Fm (d3_a hc) x hx h i)
    (selS Fm (d3_a hc) x hx h i) (selI Fm (d3_a hc) x hx h i) hsep C CH hP ra.pass _ Cabs (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2
    (selDH Fm (d3_a hc) x hx h i).2.1 (selDH Fm (d3_a hc) x hx h i).2.2 lam0 _ _ Fm.Csz Sw C1 (Equiv.refl _) H
    (_root_.Formalism.L2.RowDataTransport.inpAt_of_alt (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2 lam0 _ _ Fm.Csz Sw C1 (Equiv.refl _) H Ce (hCe x hx3 i)
      (by rw [tw_heq hZs hS0]; exact hTw Fm (d3_a hc) x hx h i) (by rw [hZs]; exact hD0 Fm (d3_a hc) x hx h i)
      (lift_exponent_of_least (selP Fm (d3_a hc) x hx h i).1.A3.A hok1.ok2 (selP Fm (d3_a hc) x hx h i).1.P0 (selP Fm (d3_a hc) x hx h i).1.ψ0 ((selP Fm (d3_a hc) x hx h i).1.A3.fam3.toSub2 (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).Zs)
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).core.base.μ (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).core.base.Tw _ (fun _ _ _ => rfl))
      ⟨dg, hdg, hdvd, hA⟩ (fun NuC I hT hI u => hd hok1 hsep hP ra.pass lam0 _ _ Sw C1 H NuC I hT hI u))
    (Fm.nprimeDef x hx i) (fun u => Fm.h_eq x hx i u)
    (fixedScale_tied (Fm.L x i) (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2 (Fm.ex x hx i).kap_def (Fm.ex x hx i).fdef (selP Fm (d3_a hc) x hx h i).1.A3 (selP Fm (d3_a hc) x hx h i).1.P0 (selP Fm (d3_a hc) x hx h i).1.ψ0 (Equiv.refl _)
      (Fm.L x i).Nc Fm.Csz (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).Zs C CH)
    (le_max_left _ _) (by rw [e0]; exact le_trans (le_max_left _ _) (le_max_right _ _))
    (by rw [e0]; exact le_trans (le_max_right _ _) (le_max_right _ _)) hCabs
    (Formalism.MainNotions.DIV.La_nonneg (Fm.L x i) (Fm.sizes x hx i).2.2.2.2.2.2.1)
end Formalism.L2.Top4Wire2
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Top.wire_sel_alt : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hTw : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.TieTwRec (Fm.L x i) (selP Fm hc x hx h i).1.S0.Tw)
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (hDcPtG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DcPtG (selP Fm hc x hx h i).1), _root_.Formalism.L2.Top4.Wire4Alt sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) hPA (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB) 2 := by
  intro 𝒜 sel selS selP selDH selC selB hTw hPA hDivG hDcPtG
  haveI : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (i : Fm.Ix x), NumberField.IsTotallyComplex (Fm.D x i).what₂.LL :=
    fun Fm x i => (Fm.D x i).tcLL
  have hDivR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps
        (selP Fm hc x hx h i).1.ψs (selP Fm hc x hx h i).1.Zs (selP Fm hc x hx h i).1.S0 (selP Fm hc x hx h i).1.S1 (Fm.ex x hx i).p0 (selP Fm hc x hx h i).1.C (selP Fm hc x hx h i).1.NuC (selP Fm hc x hx h i).1.I :=
    fun Fm hc x hx h i => (hDivG Fm hc x hx h i).toRows (_root_.Formalism.IndefR.LevelRealisationRankEquality.tup_all_used_of_realisation (selB Fm hc x hx h i).Q)
  have hDcPt : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.Rows.RowsHoldDcPt3 (selP Fm hc x hx h i).1 :=
    fun Fm hc x hx h i => Formalism.L2.DIV.dcPt_of_G (_root_.Formalism.IndefR.LevelRealisationRankEquality.tup_all_used_of_realisation (selB Fm hc x hx h i).Q) (hDcPtG Fm hc x hx h i)
  have hD0 : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      (Fm.D x i).what₂.D0 = ((selP Fm hc x hx h i).1.A3.A.fam.R (selP Fm hc x hx h i).1.A3.A.fam.μ0).dZ
        ((selP Fm hc x hx h i).1.A3.A.fam.lvl (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0)
        ((selP Fm hc x hx h i).1.Zs.Z (selP Fm hc x hx h i).1.A3.A.fam.μ0) :=
    fun Fm hc x hx h i => _root_.Formalism.IndefR.LevelRealisationRankEquality.indefinite_realisation_base_rank_eq (selB Fm hc x hx h i).Q
  intro eps Fm hc CH
  exact _root_.Formalism.L2.Top4Wire2.wire4F_alt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) hPA (_root_.Formalism.L2.Top4.SingleMapCondition selB) 2 (by norm_num) hTw hD0 hDcPt hDivR Fm hc CH
end
end
