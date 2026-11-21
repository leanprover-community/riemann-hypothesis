import Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Hyps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefiniteSideCondition
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ShapeOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopShapeAlt
import Development.AutomorphicArithmetic.CharacterBoxes.ShapeWin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefiniteRealisationChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieTwRecOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FiniteTOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkBrest
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClosedFamilyAdmissibleTwistLink
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GServT
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelectionClosedOfWuDecay
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FinXRowOfGap
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AdmissibilityClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AdmissibleOfTransported
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WireSel
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkEx
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassOfRecordOfChoice
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ClosedRankTiesFC2S
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkEta
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkIRROfJoinEx
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SmallLevelRankEqClosedOfLevelProjectionSurjective
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseRankEqOfRealisation
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RankZeroOfLevelThree
import Formalism.LocalToGlobal.NormalizedHeckeFactors.BaseRowsEqRecordRows
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkG
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkAlt

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Fc.goal_of_shape_of_hyps (V NR : Prop) (N : FamClass → Prop) (G : Prop) (t : _root_.GlobalTheory.Fc.TopShapeAlt V NR N G) (hV : V) (hR : NR) (h : _root_.GlobalTheory.Fc.HypsAlt N _root_.GlobalTheory.Fc.DefiniteSideCondition) : G :=
  t h.𝒜 h.cT h.hEx (_root_.GlobalTheory.Fc.familySelection h.σ) h.hduty (_root_.GlobalTheory.Fc.spectralConditionOfRawSelection h.σ) (_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection h.σ) (_root_.GlobalTheory.Fc.definiteHeightOfRawSelection h.σ) (fun Fm hc x hx k i => (_root_.GlobalTheory.Fc.columnChoiceOfRawSelection h.σ Fm hc x hx k i).toS) (_root_.GlobalTheory.Fc.selectionBundleOfRawSelection h.σ) h.hRB h.hTw h.hPA h.hLamP
    (fun Fm hc x hx k i => (GlobalTheory.Cp.divRows3G_iff _).1 (h.hDivG Fm hc x hx k i)) h.hDcPtG h.hTu h.hn4 h.hLit hV h.hWu h.hRF h.hTF h.c30 h.hc30 h.sTy h.sNG h.sM h.sLp h.sO h.h30 h.hInstR h.selJ h.jOn h.hMt
    (h.rRows.imp fun Fm CH _ r hc => let ⟨C, h0, x0, r⟩ := r hc
      ⟨C, h0, x0, fun x hx k hx0 i => let ⟨a, d⟩ := r x hx k hx0 i
        ⟨⟨a.w1, a.covol, a.onto, a.lamLow, a.seeIso, a.miStar, a.fun0, a.pass, a.kap⟩, d⟩⟩)
    h.aPt0 h.aPtTw h.aPer0 h.aPerTw h.aP10 h.aAtG h.aC2 ((_root_.GlobalTheory.Cp.serv_t_iff_formalism_serv_t _ _).1 h.hServ) hR h.nRest h.cIc h.hcI h.irrC h.zL h.tie h.hU h.hG
theorem GlobalTheory.Fc.forall_goal_of_shape_of_hyps : ∀ (V NR : Prop) (N : FamClass → Prop) (G : Prop), _root_.GlobalTheory.Fc.TopShapeAlt V NR N G → V → NR → _root_.GlobalTheory.Fc.HypsAlt N _root_.GlobalTheory.Fc.DefiniteSideCondition → G :=
  fun V NR N G t hV hR h => _root_.GlobalTheory.Fc.goal_of_shape_of_hyps V NR N G t hV hR h
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Top.closed_family_admissible_twist_link_alt : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (aPt0 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u)
    (aPtTw : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPointIntegral (Fm.D x i) (Fm.ex x hx i).tw)
    (aPer0 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (Fm.D x i))
    (aPerTw : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw)
    (aP10 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT (Fm.X x i) (Fm.ex x hx i).tw u)
    (aAtG : Closed (D3 3 𝒜) fun Fm _ => ∃ C1 : ℝ, (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1)
    (hServ : _root_.Formalism.L2.G.ServT.SelectionServed (D3 3 𝒜) fun Fm hc => sel Fm (d3_a hc)), Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.LocalQuadraticParts.adm2 (Fm.D x i) (Fm.L x i) := by
  intro 𝒜 sel aPt0 aPtTw aPer0 aPerTw aP10 aAtG hServ
  have hDG : Closed (D3 3 𝒜) fun Fm _ => DGamSize Fm := Closed.of_class fun _ _ hc => hc.2.2.2
  have hA2 : Formalism.L2.G.Adm2InU.Adm2InU (D3 3 𝒜) :=
    { pt0 := aPt0, ptTw := aPtTw, per0 := aPer0, perTw := aPerTw,
      serv := _root_.Formalism.L2.G.ServT.closed_servF_of_servT_of_dGamSize (fun Fm hc => sel Fm (d3_a hc)) hDG hServ,
      p10 := aP10, dgt := Formalism.MainNotions.closed_eventually_levelPrimeCoprimeStabiliser (WithChN 𝒜) 3, atG := aAtG }
  exact (Formalism.L2.G.Adm2InU.admissible_family_of_inclusion hA2).imp fun _ _ _ a => a.1
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict Formalism.L2.SG.KerJoinS Formalism.L2.SG.KerSideCut Formalism.IndefR.Cx Formalism.L2.Indef
namespace Formalism.L2.SG.JoinSI
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Twist
variable {D : D7} (X : HidaSetting D) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} (Tr : ∀ u, Transport X u (Fm u)) (hK : X.LevelSubgroupCharacter)
  (Dt : D.what₂.Word → Set X.B.I.GA)
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  (P : CxData A) {fc : DefSub A → DefFace Bs}
  (eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH)
  (s : Bool) (σ : K →+* ℂ)
  (m : D.what₂.Word → (fc P.zs).Dc.Mem)
  (cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((fc P.zs).Dc.a (m u)) → ℂ))
  (cF : (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0)
  (eR : D.what₂.EE →ₛₗ[Formalism.IndefR.Links.cj s] P.EE)
end Twist
section At
variable {D : D7}
variable {X : HidaSetting D} {G : GoodOp X} {Y : Formalism.L2.SG.Full.Full X} {j : FinX Y → (D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)}
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} {Tr : ∀ u, Transport X u (Fm u)}
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  {P : CxData A} {fc : DefSub A → DefFace Bs}
  {eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH}
  {s : Bool} {σ : K →+* ℂ}
end At
section Ties
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : _root_.Formalism.L2.RecTAlt ex}
theorem adm13_of_transported_join (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R)
    {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
    {P' : CxData A} {fc : DefSub A → DefFace Bs}
    {eV : ∀ t, (Fin ((fc P'.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : P'.EE →ₗ⋆[ℂ] (fc P'.zs).Sp.HH} {s : Bool} {σ : K →+* ℂ}
    (hM : P'.MIstar2 eV sEE) (J : JoinAt S.X S.G S.Y (_root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S) S.tr P' fc eV sEE s σ) (hF : FinX S.Y)
    (hon : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤) : Formalism.MainNotions.LocalQuadraticParts.adm13 D :=
  adm13_of_colJoin hM J hF (S.hI hF) (_root_.Formalism.L2.SG.JoinSI.eHH_sEE_eq_conjHH_isometryOfJoin S hF) (_root_.Formalism.L2.SG.JoinSI.colJoinS_of_spectral_ties_real S hF) R.pin.buDef hon
end Ties
section Real
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
variable {R : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {P : Formalism.L2.Rows.RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks}
theorem adm13_of_kernel_join (hM : (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).MIstar2 (Q.F.eV (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs) Q.sEE) (J : _root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin R S Q) (hF : FinX S.Y)
    (hon : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤) : Formalism.MainNotions.LocalQuadraticParts.adm13 D :=
  _root_.Formalism.L2.SG.JoinSI.adm13_of_transported_join S hM J.toJoinAt hF hon
end Real
end Formalism.L2.SG.JoinSI
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Top4 Formalism.L2.SG.JoinSI Formalism.L2.SG.PackageTie2
namespace Formalism.L2.SG.JoinSISel
section At
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
def IndefiniteRealisationMultiplicityCondition {R : _root_.Formalism.L2.RecTAlt ex} {P : Formalism.L2.Rows.RowSideFamily ex}
    {Dcf : ∀ Zs : Formalism.L2.Indef.DefSub P.A3.fam3.amb3, Formalism.L2.Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs, Formalism.L2.Indef.SPer (Dcf Zs)} {Zscf : Formalism.L2.Indef.DefSub P.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) : Prop :=
  (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).MIstar2 (Q.F.eV (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs) Q.sEE
end At
variable {𝒜 : FamClass} {sel : _root_.Formalism.L2.TwistSelection 𝒜} {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel}
  {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP} {selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel} {selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK}
theorem complementFive_closed_of_image_v0 (selJ : _root_.Formalism.L2.SG.JoinSISel.IndefiniteRealisationSelection 𝒜 sel selS selP selDH selC selK selI)
    (hM : Closed 𝒜 fun Fm _ => ∀ hc : 𝒜 Fm, _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm hc fun x hx h i => _root_.Formalism.L2.SG.JoinSISel.IndefiniteRealisationMultiplicityCondition (selI Fm hc x hx h i))
    (hFX : Closed 𝒜 fun Fm _ => ∀ hc : 𝒜 Fm, _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm hc fun x hx h i => FinX (selS Fm hc x hx h i).Y)
    (hon : Closed 𝒜 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, BaseVectorImageFull (Fm.D x i)) :
    Closed 𝒜 fun Fm _ => Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm := by
  obtain ⟨ε1, hε1, H⟩ := (hM.and hFX).and hon
  refine ⟨ε1, hε1, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := H eps he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨hM', hF'⟩, ⟨y0, hY⟩⟩ := hK Fm CH hc hL
  obtain ⟨a0, hA⟩ := hM' hc
  obtain ⟨b0, hB⟩ := hF' hc
  refine ⟨max (max a0 b0) (max y0 (max (sel Fm hc).1 (Fm.x1 + 1))), fun x hxge i => ?_⟩
  have h1 : max a0 b0 ≤ x := le_trans (le_max_left _ _) hxge
  have h2 : max y0 (max (sel Fm hc).1 (Fm.x1 + 1)) ≤ x := le_trans (le_max_right _ _) hxge
  have hx : Fm.x1 < x := by
    have := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)
    linarith
  have h : (sel Fm hc).1 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h2)
  exact _root_.Formalism.L2.SG.JoinSI.adm13_of_kernel_join (hA x hx h (le_trans (le_max_left _ _) h1) i) (selJ Fm hc x hx h i)
    (hB x hx h (le_trans (le_max_right _ _) h1) i) (hY x (le_trans (le_max_left _ _) h2) i)
end Formalism.L2.SG.JoinSISel
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Top.selection_closed_of_wu_decay_alt : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hWu : Formalism.L2.SG.Pf.WuDecayOfGap)
    (hRF : Formalism.L2.SG.RowsDef.RowsFinDim)
    (selJ : _root_.Formalism.L2.SG.JoinSISel.IndefiniteRealisationSelection 𝒜 sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (jOn : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.L2.SG.JoinSISel.BaseVectorImageFull (Fm.D x i))
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH), Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm := by
  intro 𝒜 sel selS selP selDH selC selB hWu hRF selJ jOn rRows
  have jGap : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm,
      _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm (d3_a hc) fun x _ _ i => Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i) :=
    (Formalism.L2.SG.GapClosed.gapEv_closed_of (D3 3 𝒜) fun _ hc => hc.2.2.1).imp fun Fm _ _ h hc => by
      obtain ⟨y, hy⟩ := h hc
      exact ⟨y, fun x _ _ hxy i => hy x hxy i⟩
  have hM : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.EventuallyAlongSelection (fun Fm hc => sel Fm (d3_a hc)) Fm hc fun x hx h i =>
      _root_.Formalism.L2.SG.JoinSISel.IndefiniteRealisationMultiplicityCondition ((_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm (d3_a hc) x hx h i) :=
    rRows.imp fun Fm CH _ h hc => by
      obtain ⟨C, _, x0, H⟩ := h hc
      exact ⟨x0, fun x hx hs hx0 i => (H x hx hs hx0 i).1.miStar⟩
  have hFX := _root_.Formalism.L2.SG.JoinSISel.closed_finX_of_gapHyp (𝒜 := D3 3 𝒜) (sel := fun Fm hc => sel Fm (d3_a hc))
    (selS := fun Fm hc => selS Fm (d3_a hc)) (Formalism.L2.SG.Pf.finXC_of hWu hRF)
    jGap
  have hC5 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm :=
    _root_.Formalism.L2.SG.JoinSISel.complementFive_closed_of_image_v0 (𝒜 := D3 3 𝒜) (sel := fun Fm hc => sel Fm (d3_a hc))
      (selS := fun Fm hc => selS Fm (d3_a hc)) (selP := fun Fm hc => selP Fm (d3_a hc)) (selDH := fun Fm hc => selDH Fm (d3_a hc))
      (selC := fun Fm hc => selC Fm (d3_a hc)) (selK := fun Fm hc => (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) Fm (d3_a hc)) (selI := fun Fm hc => (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm (d3_a hc))
      (fun Fm hc => selJ Fm (d3_a hc)) hM hFX jOn
  exact hC5
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.Ext.Lw
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.Forms Formalism.BasicNotions
open scoped TensorProduct
theorem rankTiesF_of_C2S_alt {eps : ℝ} (Fm : FamP eps) (h : _root_.Formalism.L2.SecondChernLinkedClass Fm) : RankTiesF Fm := by
  obtain ⟨x0, h⟩ := h
  refine rank_conditions_of_lowest_space Fm ⟨max x0 (Fm.x1 + 1), fun x hx i u => ?_⟩
  have e1 : Fm.x1 < x := by
    have := (le_max_right x0 (Fm.x1 + 1)).trans hx
    linarith
  obtain ⟨T⟩ := h x e1 ((le_max_left _ _).trans hx) i
  exact mu0Tie_of_sym T.cols u
theorem second_chern_linked_closed_rank_ties : Closed _root_.Formalism.L2.SecondChernLinkedClass fun Fm _ => RankTiesF Fm :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hC _ => _root_.Formalism.MainNotions.Ext.Lw.rankTiesF_of_C2S_alt Fm hC⟩⟩
end Formalism.MainNotions.Ext.Lw
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Top.designExists_of_tuSize_aux4n_litThin : ∀ (𝒜 : FamClass)
    (cT : ℝ → ℝ → ℝ)
    (hEx : MinkDiv → DesignChoices (WithTw 𝒜) 3 cT)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm)
    (hTu : Closed (WithTw (WithSm (WithChN 𝒜))) fun {eps} Fm _ => cT eps Fm.CYL ≤ Fm.CTu → TuSize Fm)
    (hn4 : Closed (WithTw (WithSm (WithChN 𝒜))) fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
      StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev)
    (hLit : LitThin), DesignExists (WithTw (WithSm (WithChN 𝒜))) 3 := by
  intro 𝒜 cT hEx sel hduty hTu hn4 hLit
  have hC0 : (3 : ℝ) ≤ 3 := le_refl _
  have hC0' : (0 : ℝ) < 3 := by norm_num
  have hCe : Real.exp 1 ≤ 3 := le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hC0
  have hRec : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → _root_.Formalism.L2.SecondLayerFamilyClass Fm := fun Fm hc =>
    _root_.Formalism.L2.Top3.layerTwoFamilyClass_of_linked_aligned (sel Fm hc) (_root_.Formalism.L2.Top3.linkedFamiliesAligned_of_duty (sel Fm hc) (hduty Fm hc))
  have hsub : ∀ {eps : ℝ} (Fm : FamP eps), WithTw (WithSm (WithChN 𝒜)) Fm → 𝒜 Fm := fun _ hc => hc.1.1.1
  have hProv : Closed (WithTw (WithSm (WithChN 𝒜))) fun Fm _ => ChosenProviso Fm 3 :=
    (hn4.and (Pk.Closed.sub _root_.Formalism.MainNotions.Ext.Lw.second_chern_linked_closed_rank_ties fun Fm hc => (hRec Fm (hsub Fm hc)).c2s)).imp
      fun Fm _ _ h => Formalism.MainNotions.StandardLattice.HarishChandraReduction.chosenProviso_min Fm 3 hCe h.1 h.2
  have hE' : DesignExists (WithTw (WithSm (WithChN 𝒜))) 3 :=
    designExists_of_choices (designChoices_upN (hEx minkowski_bound_rat)) hTu hProv
      (chosenThin_closed (WithTw (WithSm (WithChN 𝒜))) hLit)
  exact hE'
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
theorem GlobalTheory.Top.closed_linkEta_of_duty : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm), Closed (D3 3 𝒜) fun Fm _ => LinkEta Fm := by
  intro 𝒜 sel _
  refine Closed.of_class fun Fm _ hc => ?_
  obtain ⟨x0, hx0⟩ := _root_.Formalism.L2.Top3.tied_families_of_choice_alt (sel Fm (d3_a hc))
  refine Formalism.L2.linkEta_closed Fm ⟨max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have h1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
  obtain ⟨T⟩ := hx0 x h1 ((le_max_left _ _).trans hx) i
  exact ⟨T.n.gal.mt, T.n.cover, T.n.gal.hecke⟩
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Top.Irr
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.ConcNWeight Formalism.L2.GlobalTheoryTheory.AllJoin
end
section
open Formalism.BasicNotions Formalism.MainNotions
end
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
theorem closed_linkIRR_of_join_count : GlobalTheory.GLq.Green → ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (cIc : ℝ)
    (hcI : 0 < cIc)
    (irrC : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f)), Closed (D3 3 𝒜) fun Fm _ => LinkIRR Fm := by
  intro hG 𝒜 sel cIc hcI irrC
  have irr : Closed (D3 3 𝒜) fun {eps} Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧ Formalism.MainNotions.ArithmeticCylinders.admLq (Fm.D x i) ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f) ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.SizesRec (Fm.D x i) x Fm.ez 6 :=
    closed_of_mem (irrC.imp fun Fm _ _ H hc => by
      obtain ⟨x0, H⟩ := H
      refine ⟨max (max x0 (sel Fm (d3_a hc)).1) (max (Fm.x1 + 1) 4), fun x hx i => ?_⟩
      have h1 : Fm.x1 < x := by have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx; linarith
      have hs : (sel Fm (d3_a hc)).1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
      obtain ⟨A, a, b, c⟩ := H x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx) i
      exact ⟨A, a, b, GlobalTheory.Top.Lq.admissibleLabelWeights_of_greenCuspidalParametrisation hG _ _ ((sel Fm (d3_a hc)).2 x h1 hs i).T.n.types, c,
        sizesRec_at Fm h1 (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) i le_rfl⟩)
  exact (irr.and (closed_eps_le_one _)).imp fun Fm _ he ⟨h, h1⟩ =>
      linkIRR_of_join_ex _ 6 cIc he h1 hcI Fm h
end GlobalTheory.Top.Irr
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Module
namespace Formalism.L2.N.ExtNRows3
open Formalism.L2.N.ExtNRows
open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
section Pin
variable (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (hp : _root_.Formalism.L2.Rows.RowSideDeterminedAlt T P) (hL : RowsHoldLam3 P) (h : RowsHold0_3 P)
include hp hL h in
open Classical in
theorem base_rows_eq_record_rows_alt : P.S0.D = D.what₂.D0 := by
  obtain ⟨cOf, -, -, h3⟩ := hL
  have e1 := sum_finrank P.S0.Ep (Ep_decomp P h).1 (Ep_decomp P h).2
  rw [Module.finrank_fin_fun] at e1
  have e2 : ∑ c, ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = c), D.what₂.nRows0 σ = ∑ σ, D.what₂.nRows0 σ :=
    Finset.sum_fiberwise _ _ _
  have e3 : ∑ σ, D.what₂.nRows0 σ = D.what₂.D0 := by
    unfold Rows.Data.nRows0
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv D.what₂.ft0), Fintype.card_fin]
  rw [← e1, ← e3, ← e2]
  exact Finset.sum_congr rfl fun c _ => (h3 c).symm
include hp hL h in
theorem finrank_Mj_eq_D0 : ∀ j, 1 ≤ j → j ≤ D.R.m → finrank ℂ (D.what₂.Mj j) = D.what₂.D0 := by
  intro j h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have := finrank_Mj_eq_dW P ⟨k, by omega⟩
  rw [dW_eq_D P h, _root_.Formalism.L2.N.ExtNRows3.base_rows_eq_record_rows_alt T P hp hL h] at this
  exact this
end Pin
theorem thetaT_injective_and_finrank_Zj_eq_D0_of_surjective (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (hp : _root_.Formalism.L2.Rows.RowSideDeterminedAlt T P) (hL : RowsHoldLam3 P) (h : RowsHold0_3 P)
    (hR : Formalism.L2.DIV.DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) (i : Fin D.R.m) (t : P.T)
    (hl : Function.Surjective (lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec) :
    Function.Injective (D.what₂.thetaT (P.I.tup t) ((i : ℕ) + 1)) ∧
      finrank ℂ (D.what₂.Zj (P.I.tup t) ((i : ℕ) + 1)) = D.what₂.D0 := by
  have hi : Function.Injective (D.what₂.thetaT (P.I.tup t) ((i : ℕ) + 1)) :=
    adjoint_injective _ (thetaP_surj P h hR i t hl)
  refine ⟨hi, ?_⟩
  unfold Rows.Data.Zj
  rw [LinearMap.finrank_range_of_inj hi]
  exact _root_.Formalism.L2.N.ExtNRows3.finrank_Mj_eq_D0 T P hp hL h _ (Nat.succ_le_succ (Nat.zero_le _)) i.2
end Formalism.L2.N.ExtNRows3
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.L2.N.RankZeroOfLevelThree
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Module
open Formalism.L2.N.ExtNRows3 Formalism.L2.N.ExtNRows Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
theorem rank_zero_of_row_conditions_alt {eps : ℝ} (Fm : FamP eps) (x0 : ℝ)
    (T : ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.TiedDataSKAlt (Fm.ex x hx i))
    (P : ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, RowSideFamily (Fm.ex x hx i))
    (hp : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), _root_.Formalism.L2.Rows.RowSideDeterminedAlt (T x hx h0 i) (P x hx h0 i))
    (hL : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), RowsHoldLam3 (P x hx h0 i))
    (hR : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), Formalism.L2.DIV.DivRows3 (Fm.D x i) (P x hx h0 i).A3 (P x hx h0 i).P0
      (P x hx h0 i).ψ0 (P x hx h0 i).Ps (P x hx h0 i).ψs (P x hx h0 i).Zs (P x hx h0 i).S0 (P x hx h0 i).S1 (Fm.ex x hx i).p0
      (P x hx h0 i).C (P x hx h0 i).NuC (P x hx h0 i).I)
    (h : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), RowsHold0_3 (P x hx h0 i))
    (ht : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), ∃ t : (P x hx h0 i).T,
      (P x hx h0 i).I.tup t = (Fm.D x i).what₂.mu0 ∧
      ∀ k : Fin (Fm.D x i).R.m, Function.Surjective (lPrj (Fm.D x i) (P x hx h0 i).A3.A (P x hx h0 i).P0
        (P x hx h0 i).ψ0 ((P x hx h0 i).A3.fam3.toSub2 (P x hx h0 i).Zs) k t).mulVec) :
    SmallLevelRankEq Fm := by
  refine ⟨max x0 (Fm.x1 + 1), fun x hxx i j hj => ?_⟩
  have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hxx)
  have h0 : x0 ≤ x := le_trans (le_max_left _ _) hxx
  obtain ⟨t, htup, hsurj⟩ := ht x hx1 h0 i
  have hj' := Finset.mem_Icc.1 hj
  obtain ⟨k, rfl⟩ : ∃ k : Fin (Fm.D x i).R.m, j = (k : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  have key := (_root_.Formalism.L2.N.ExtNRows3.thetaT_injective_and_finrank_Zj_eq_D0_of_surjective (T x hx1 h0 i) (P x hx1 h0 i) (hp x hx1 h0 i) (hL x hx1 h0 i) (h x hx1 h0 i) (hR x hx1 h0 i) k t (hsurj k)).2
  rw [htup] at key
  exact key
end Formalism.L2.N.RankZeroOfLevelThree
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Top.link_alt_alt_alt : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hLamP : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.Rows.RowsHoldLam3 (selP Fm hc x hx h i).1)
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (zL : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, ∃ xr : ℝ, ∀ x (hx : Fm.x1 < x) (h : (sel Fm (d3_a hc)).1 ≤ x), xr ≤ x →
      ∀ (i : Fm.Ix x) (k : Fin (Fm.D x i).R.m),
        Function.Surjective (Formalism.L2.DIV.lPrj (Fm.D x i) (selP Fm (d3_a hc) x hx h i).1.A3.A (selP Fm (d3_a hc) x hx h i).1.P0
          (selP Fm (d3_a hc) x hx h i).1.ψ0 ((selP Fm (d3_a hc) x hx h i).1.A3.fam3.toSub2 (selP Fm (d3_a hc) x hx h i).1.Zs) k
          (selP Fm (d3_a hc) x hx h i).1.A3.A.μ0).mulVec), Closed (D3 3 𝒜) fun Fm _ => SmallLevelRankEq Fm := by
  intro 𝒜 sel selS selP selDH selC selB hPA hLamP hDivG zL
  have hDivR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps
        (selP Fm hc x hx h i).1.ψs (selP Fm hc x hx h i).1.Zs (selP Fm hc x hx h i).1.S0 (selP Fm hc x hx h i).1.S1 (Fm.ex x hx i).p0 (selP Fm hc x hx h i).1.C (selP Fm hc x hx h i).1.NuC (selP Fm hc x hx h i).1.I :=
    fun Fm hc x hx h i => (hDivG Fm hc x hx h i).toRows (_root_.Formalism.IndefR.LevelRealisationRankEquality.tup_all_used_of_realisation (selB Fm hc x hx h i).Q)
  have hZ : Closed (D3 3 𝒜) fun Fm _ => SmallLevelRankEq Fm :=
    closed_of_mem (zL.imp fun Fm _ _ h hc => by
      obtain ⟨xr, h⟩ := h hc
      exact _root_.Formalism.L2.N.RankZeroOfLevelThree.rank_zero_of_row_conditions_alt Fm (max (sel Fm (d3_a hc)).1 xr)
        (fun x hx h0 i => ((sel Fm (d3_a hc)).2 x hx (le_trans (le_max_left _ _) h0) i).T)
        (fun x hx h0 i => (selP Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i).1)
        (fun x hx h0 i => (selP Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i).2)
        (fun x hx h0 i => hLamP Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i)
        (fun x hx h0 i => hDivR Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i)
        (fun x hx h0 i => _root_.Formalism.L2.Top4.selP_condition_zero_of_primAll hPA Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i)
        (fun x hx h0 i => ⟨_, (selP Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i).1.tied.div.tup.mu0,
          h x hx (le_trans (le_max_left _ _) h0) (le_trans (le_max_right _ _) h0) i⟩))
  exact hZ
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Top.closed_linkG_of_duty : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm), Closed (D3 3 𝒜) fun Fm _ => LinkG Fm := by
  intro 𝒜 sel hduty
  have hRec : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → _root_.Formalism.L2.SecondLayerFamilyClass Fm := fun Fm hc =>
    _root_.Formalism.L2.Top3.layerTwoFamilyClass_of_linked_aligned (sel Fm hc) (_root_.Formalism.L2.Top3.linkedFamiliesAligned_of_duty (sel Fm hc) (hduty Fm hc))
  have hG2 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.G.Adm2F Fm :=
    Closed.of_class fun Fm _ hc => admissible_tops_mertens Fm (topsF_of_chosenE Fm hc.2.1.choose_spec)
  have hGt : Closed (D3 3 𝒜) fun Fm _ => Formalism.L2.G.GroupCompatibilityFamily Fm :=
    Closed.of_class fun Fm _ hc => _root_.Formalism.L2.group_compatibility_of_second_layer_family Fm (hRec Fm (d3_a hc))
  have lG := Formalism.L2.G.linkG_concrete5 (D3 3 𝒜) hGt hG2
  exact lG
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Top.link_alt_alt_bis : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (hWu : Formalism.L2.SG.Pf.WuDecayOfGap)
    (hRF : Formalism.L2.SG.RowsDef.RowsFinDim)
    (hTF : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3)
    (c30 : List ℝ → Formalism.MainNotions.S.CountingConstants)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (sTy : Formalism.L2.SG.RowsPos.TypeP)
    (sNG : Formalism.L2.SG.RowsPos.RowNGP)
    (sM : Formalism.L2.SG.RowsPos.RowMainEqP)
    (sLp : Formalism.L2.SG.ThmSOwn.LoopRowS 3 (D3 3 𝒜) (fun Fm hc => ⟨(sel Fm (d3_a hc)).1, fun x hx h i => (selS Fm (d3_a hc) x hx h i).toSTies⟩))
    (sO : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, Formalism.L2.SG.ThmSOwn.TheoremSSelected Fm 3
      ⟨(sel Fm (d3_a hc)).1, fun x hx h i => (selS Fm (d3_a hc) x hx h i).toSTies⟩)
    (h30 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.S.CountE.CountAllPointsClass Formalism.L2.SG.ThmSOwn.PLevT' Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb)
    (hInstR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep (Fm.D x i) ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) ((Fm.D x i).sp.Y 0).rank), Closed (D3 3 𝒜) fun Fm _ => TuSize Fm → LinkS Fm 3 := by
  intro 𝒜 sel selS hWu hRF hTF c30 hc30 sTy sNG sM sLp sO h30 hInstR
  have hC0 : (3 : ℝ) ≤ 3 := le_refl _
  have hC0' : (0 : ℝ) < 3 := by norm_num
  have hCe : Real.exp 1 ≤ 3 := le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hC0
  have sRes : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.S.ResidEv Fm := Formalism.L2.SG.ResidEvFree.residEv_closed_free (D3 3 𝒜)
  let ssel : Formalism.L2.SG.ThmSOwn.SSel (D3 3 𝒜) :=
    fun Fm hc => ⟨(sel Fm (d3_a hc)).1, fun x hx h i => (selS Fm (d3_a hc) x hx h i).toSTies⟩
  have lS := Formalism.L2.SG.ThmSOwn.theoremS_transport_link_zero (C0 := 3) (D3 3 𝒜) ssel hWu hRF
    (fun Fm hc x hx h i => (selS Fm (d3_a hc) x hx h i).locTied)
    (fun Fm hc x hx h i => Formalism.L2.SG.ThmSOwn.instTie_of_record (selS Fm (d3_a hc) x hx h i).inst
      (Formalism.MainNotions.RT.volTie_of_realTied _ ((sel Fm (d3_a hc)).2 x hx h i).T.theta.real) (hInstR Fm (d3_a hc) x hx h i).1
      (hInstR Fm (d3_a hc) x hx h i).2 (Fm.ties x i).cdScale_tie)
    (fun Fm hc x hx h i => Formalism.L2.SG.ThmSOwn.one_le_qqI_of_inst (selS Fm (d3_a hc) x hx h i).inst)
    hTF c30 (by linarith) hc30 sRes sTy sNG sM sLp sO h30
  exact lS
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
set_option maxHeartbeats 2000000 in
theorem UpperTheory.Top.shape_closed_link_n_of_green : GlobalTheory.GLq.Green → _root_.GlobalTheory.Fc.TopShapeAlt True True (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) UpperTheory.Top.TopG := by
  intro hGreen 𝒜 cT hEx sel hduty selS selP selDH selC selB hRB hTw hPA hLamP hDivG hDcPtG hTu hn4 hLit hVC hWu hRF hTF c30 hc30 sTy sNG sM sLp sO h30 hInstR selJ jOn hMt rRows aPt0 aPtTw aPer0 aPerTw aP10 aAtG aC2 hServ nR nRest cIc hcI irrC zL tie hU hG la G hla hH hV
  have hgl := GlobalTheory.Top.link_gl 𝒜 hduty tie hU hG
  have bRest := _root_.GlobalTheory.Top.link_brest_alt 𝒜 sel selS selP selDH selC selB hRB hPA hDivG hDcPtG rRows tie
  have hCsz : Closed (D3 3 𝒜) fun Fm _ => 0 ≤ Fm.Csz := Formalism.MainNotions.DIV.closed_Csz_ge_fn (D3 3 𝒜) fun _ => 0
  have oneMap : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm (d3_a hc) ((_root_.Formalism.L2.Top4.SingleMapCondition selB) Fm (d3_a hc)) :=
    Closed.of_class fun Fm _ _ hc => ⟨0, fun x hx h _ i j => (hRB Fm (d3_a hc) x hx h i).oneMap j⟩
  have hA2 := _root_.GlobalTheory.Top.closed_family_admissible_twist_link_alt 𝒜 sel aPt0 aPtTw aPer0 aPerTw aP10 aAtG hServ
  have hC5 := _root_.GlobalTheory.Top.selection_closed_of_wu_decay_alt 𝒜 sel selS selP selDH selC selB hWu hRF selJ jOn rRows
  have hBR : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, TuSize Fm → DGamSize Fm →
      _root_.Formalism.L2.DIV.DivisionKernelConstantBounds Fm (_root_.Formalism.L2.Top4.RankOfDivisionKernel sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) hPA Fm hc) 2 CH :=
    (bRest.and ((Closed.of_class fun Fm _ hc => cut_of_stable (hMt Fm (d3_a hc))).and (rRows.and (oneMap.and (hCsz.and (hA2.and (aC2.and hC5))))))).imp
      fun Fm CH _ ⟨r, o, rr, om, cz, a, c, c5⟩ hc hT hD =>
        (r hc hT hD).toRows_alt (fun hN => _root_.GlobalTheory.Top.wire_sel_alt 𝒜 sel selS selP selDH selC selB hTw hPA hDivG hDcPtG Fm hc CH cz hD (rr hc) (om hc) (r hc hT hD).bu hN) o a (complement_two_of_items c) c5
  have hDIV := _root_.Formalism.L2.DIV.closed_linkDIVt_of_closed_bridge_kernel (D3 3 𝒜) 2 (_root_.Formalism.L2.Top4.RankOfDivisionKernel sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) hPA) hBR
  have hsub : ∀ {eps : ℝ} (Fm : FamP eps), WithTw (WithSm (WithChN fun Fm => 𝒜 Fm ∧ G.cls la Fm)) Fm →
      WithTw (WithSm (WithChN 𝒜)) Fm := fun _ hc => ⟨⟨⟨hc.1.1.1.1, hc.1.1.2⟩, hc.1.2⟩, hc.2⟩
  have hE := _root_.GlobalTheory.Top.designExists_of_tuSize_aux4n_litThin (fun Fm => 𝒜 Fm ∧ G.cls la Fm) cT (fun hM => hEx hM la G hla hH) (fun Fm hc => sel Fm hc.1)
    (fun Fm hc => hduty Fm hc.1) (Pk.Closed.sub hTu hsub) (Pk.Closed.sub hn4 hsub) hLit
  exact UpperTheory.Top.topDesWin (WithChN 𝒜) (WithChN fun Fm => 𝒜 Fm ∧ G.cls la Fm) (G.cls la) 2 3 2 0 hE
    (fun _ hc => ⟨hc.1.1, hc.2⟩) (fun _ hc => hc.1.2) hV nRest (_root_.GlobalTheory.Top.closed_linkEta_of_duty 𝒜 sel hduty)
    (_root_.GlobalTheory.Top.Irr.closed_linkIRR_of_join_count hGreen 𝒜 sel cIc hcI irrC) (_root_.GlobalTheory.Top.link_alt_alt_alt 𝒜 sel selS selP selDH selC selB hPA hLamP hDivG zL) hDIV hgl.1 (_root_.GlobalTheory.Top.closed_linkG_of_duty 𝒜 sel hduty)
    (_root_.GlobalTheory.Top.link_alt_alt_bis 𝒜 sel selS hWu hRF hTF c30 hc30 sTy sNG sM sLp sO h30 hInstR) hgl.2
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc
theorem UpperTheory.Top.zero_free_all_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
    (h : Nonempty (_root_.GlobalTheory.Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)) : Formalism.HC.ZeroFreeAll :=
  h.elim fun h => UpperTheory.Top.zeroFreeAll_of_topG (la := 3 / 2) (by norm_num)
    (_root_.GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (_root_.UpperTheory.Top.shape_closed_link_n_of_green hG) trivial trivial h) fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ)
theorem UpperTheory.Top.every_character_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
    (h : Nonempty (_root_.GlobalTheory.Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)) : UpperTheory.EveryCharacter :=
  UpperTheory.Top.imprimitive (_root_.UpperTheory.Top.zero_free_all_of_green_v_win hG hV h)
end
end
