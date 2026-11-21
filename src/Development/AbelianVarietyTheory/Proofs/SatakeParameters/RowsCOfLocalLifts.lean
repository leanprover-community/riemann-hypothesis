import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameGeneratorResidual
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaEigenspaceMapping
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaLiftOfEachRow
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.InternalDirectSumOfParts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoLocAppendSingleton
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitLiftOfPairLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentificationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitComponentsDeterminedByPointOfBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharEtaBack
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBisAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicRepEqOfEqAtAlmostAllSplitPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalStrongMultiplicityOneOfAnalytic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOneOfCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodLabelsRankPartParameterCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBisBis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBisTer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeOrthogonalityOfFormStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalPointThetaExhaustionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointOfPrvConditionsStatement

section
noncomputable section

namespace GlobalTheory.DownMemRoad

open Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceMapping GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent GlobalTheory.IndefiniteRowSideFullHecke.InternalDirectSumCriteria

theorem mem_biSup_of_orthogonal {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ι → Submodule ℂ V) (S : Set ι) (htop : ⨆ k, U k = ⊤) (horth : ∀ k k', k ≠ k' → U k ⟂ U k')
    {v : V} (hv : ∀ k ∉ S, v ∈ (U k)ᗮ) : v ∈ ⨆ k ∈ S, U k := by
  have hsup : (⨆ k ∈ S, U k) ⊔ (⨆ k ∈ Sᶜ, U k) = ⊤ := by
    rw [← htop]
    exact (iSup_split U (· ∈ S)).symm
  have ho : (⨆ k ∈ S, U k) ⟂ (⨆ k ∈ Sᶜ, U k) := by
    simp only [Submodule.isOrtho_iSup_left, Submodule.isOrtho_iSup_right]
    intro k hk k' hk'
    refine horth _ _ ?_
    rintro rfl
    exact absurd hk' hk
  have hv' : v ∈ (⨆ k ∈ Sᶜ, U k)ᗮ := by
    have h1 : (ℂ ∙ v) ⟂ (⨆ k ∈ Sᶜ, U k) := by
      simp only [Submodule.isOrtho_iSup_right]
      intro k hk
      exact (Submodule.span_singleton_le_iff_mem _ _).2 (hv k hk)
    exact h1 (Submodule.mem_span_singleton_self v)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hsup.ge (Submodule.mem_top (x := v)))
  have hb' : b ∈ (⨆ k ∈ Sᶜ, U k)ᗮ := by
    have := Submodule.sub_mem _ hv' (ho ha)
    rwa [add_sub_cancel_left] at this
  have hb0 : b = 0 := inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hb' b hb)
  rw [hb0, add_zero]
  exact ha

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem hasParamW_of_thetaOf (hL : ParamLaws N A) {i : N.Loc} (hS : SplitLift N A i)
    (hloc : LocOfPt N A i) {x : N.X i} {Sig : List (Part A.CG)} (hx : HasParamX N A i x Sig)
    {σ : what₂.FT} {P : A.AV i} (hθ : thetaOf N A i σ P) (hP : A.ptV i P = some x) :
    HasParamW N A i σ Sig := by
  obtain ⟨P', hP', h1, -, h3, h4, -⟩ := hx
  refine ⟨fun p hp => ?_, ?_, fun w hw => ?_⟩
  · have := h1 ⟨p.a, A.tw p.π A.etaTinv, p.d⟩
      (List.mem_map.mpr ⟨p, List.mem_append_left _ hp, rfl⟩)
    exact ⟨this.1, this.2.1⟩
  · have e : rankIso N A Sig + R.t = R.nV := by
      rw [← h3]
      simp [rankIso, twistIso, muPart, Function.comp_def]
    have e' : R.nV = R.r + R.t := rfl
    omega
  · have e := hloc P' P x hP' hP w hw
    rw [← h4 w hw, ParUpRoad.isoLoc_lift N A hL, hS σ P hθ w hw] at e
    exact (hL w).2.2.2.2 _ _ _ ((hL w).2.2.2.1 _ _ _ (A.locG_dim _ w) e)

theorem typeV_isOrtho_eigC {i : N.Loc} (hT : TypeOrth N A i) {x : N.X i} {P : A.AV i}
    (hP : A.ptV i P ≠ some x) : A.typeV i P ⟂ eigC N A i x := by
  unfold eigC
  simp only [Submodule.isOrtho_iSup_right]
  intro P' hP'
  refine hT P P' ?_
  rintro rfl
  exact hP hP'

theorem thetaP_mem (hθ : EachRowHasThetaLift N A) (hL : ParamLaws N A) {i : N.Loc}
    (htop : ⨆ σ, what₂.isot (N.j i) σ = ⊤) (hO : PartOrth N i) (hT : TypeOrth N A i)
    (hS : SplitLift N A i) (hloc : LocOfPt N A i) {x : N.X i} {Sig : List (Part A.CG)}
    (hx : HasParamX N A i x Sig) {F : what₂.Mt (N.mu i) (N.j i)} (hF : F ∈ eigC N A i x) :
    what₂.thetaP (N.mu i) (N.j i) F ∈ MjSig N A i Sig := by
  refine mem_biSup_of_orthogonal (what₂.isot (N.j i)) {σ | HasParamW N A i σ Sig} htop hO
    fun σ hσ => ?_
  by_cases h0 : what₂.isot (N.j i) σ = ⊥
  · rw [h0, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top
  obtain ⟨P, hP⟩ := hθ i σ h0
  have hne : A.ptV i P ≠ some x := fun h => hσ (hasParamW_of_thetaOf N A hL hS hloc hx hP h)
  rw [Submodule.mem_orthogonal]
  intro f hf
  rw [← LinearMap.adjoint_inner_left]
  exact (typeV_isOrtho_eigC N A hT hne).inner_eq (hP.2 ⟨f, hf, rfl⟩) hF

theorem main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    EachRowHasThetaLift N A → PartsSum R what₂.Mj what₂.isot → (∀ i, PartOrth N i) →
      (∀ i, TypeOrth N A i) → (∀ i, SplitLift N A i) → ParamLaws N A → (∀ i, LocOfPt N A i) →
      ThetaPMapsEigenspaceInto N A :=
  fun _ _ _ N A hθ hsum hO hT hS hL hloc i _ _ _ hx _ hF =>
    thetaP_mem N A hθ hL (hsum _ (N.j_range i).1 (N.j_range i).2).2 (hO i) (hT i) (hS i) (hloc i) hx hF

theorem downMem : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), ThetaOne N A → Rows.IsotInternal what₂ → PartOrth N i → TypeOrth N A i → ParamLaws N A →
      SplitLift N A i → LocOfPt N A i → DownMem N A i := by
  rintro R H what₂ N A i hθ hI hO hT hL hS hloc x - Sig hx _ ⟨F, hF, rfl⟩
  exact thetaP_mem N A hθ hL (hI _ (N.j_range i).1 (N.j_range i).2).submodule_iSup_eq_top hO hT hS hloc hx hF

end GlobalTheory.DownMemRoad
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem downMemRec_of_ties : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → GlobalTheory.RowCopy.ThetaOne D → Rows.IsotInternal D.what₂ → (∀ i, GlobalTheory.ThetaExh.PartOrth D.nd i) → (∀ i, GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) → ∀ i, GlobalTheory.RowCopy.DownMemRec D.nd D.naut i :=
  fun D T hθ hI hO hT hP hB hS i =>
    GlobalTheory.DownMemRoad.downMem _ _ _ D.nd D.naut i hθ hI (hO i) (hT i) (GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification _ _ _ D.nd D.naut T).1
      (splitLift_of_pairLift _ _ _ D.nd D.naut i (hP i)) (GlobalTheory.T.splitComponentsDeterminedByPoint_of_baseChange _ _ _ D.nd D.naut i (hB i) (hS i))

end GlobalTheory.RowTie
end

section
namespace GlobalTheory.Proof.GoodComponentRecursion

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem goodPartRec_of_ties : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → GlobalTheory.RowCopy.ThetaOne D →
    (∀ i, GlobalTheory.ThetaExh.LiftParam D.nd D.naut i) → (∀ i, GlobalTheory.ThetaExh.PtLocal D.nd D.naut i) →
    (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) →
    ∀ i, GlobalTheory.RowCopy.GoodPartRec D.nd D.naut i := by
  intro D hW h1 hlift hpt hbc hsp i
  exact GlobalTheory.Proof.SplitPlaceGoodSignature.goodPart_of_lifts D.nd D.naut i h1
    (GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification _ _ _ D.nd D.naut hW).1 (hlift i) (hpt i)
    (GlobalTheory.T.splitComponentsDeterminedByPoint_of_baseChange _ _ _ D.nd D.naut i (hbc i) (hsp i))

end GlobalTheory.Proof.GoodComponentRecursion
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.PtOfLocSplit

theorem eventually_splitOut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) :
    ∀ᶠ w in Filter.cofinite, IsSplitPl H w → SplitOut N i w := by
  have hl : (N.l i).Prime := Fact.out
  have hfin : (placesOver H.E (N.l i)).Finite := by
    have h0 : Ideal.span {((N.l i : ℕ) : 𝓞 H.E)} ≠ 0 := by simpa using hl.ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  filter_upwards [hfin.eventually_cofinite_notMem, (N.S i).eventually_cofinite_notMem,
    (N.Q i).eventually_cofinite_notMem] with w h1 h2 h3 hw using ⟨hw, h1, h2, h3⟩

theorem main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.PtOfLoc N A i := by
  intro R H what₂ N A i hBC hSp hRep P P' x hx hloc
  have hPP : P = P' := GlobalTheory.T.automorphicRep_eq_of_eq_at_almost_all_split_places R H what₂ N A i hBC hSp hRep P P' <| by
    filter_upwards [eventually_splitOut N i] with w hw hs using hloc w (hw hs)
  rw [hPP]; exact hx

end GlobalTheory.PtOfLocSplit
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointDeterminedBySplitComponents_of_baseChange : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.PtOfLoc N A i := by
  atlas_forward_decl GlobalTheory.PtOfLocSplit.main
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem parUpRec_of_ties : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → GlobalTheory.RowCopy.ThetaOne D →
    (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) →
    (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.RepOfLoc D.nd D.naut i) →
    ∀ i, GlobalTheory.RowCopy.ParUpRec D.nd D.naut i := by
  intro D T hθ hpair hbc hsplit hrep i x hx Sig hSig
  have h := GlobalTheory.ParUpRoad.main _ _ _ D.nd D.naut hθ (GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification _ _ _ D.nd D.naut T).1
    (fun i => splitLift_of_pairLift _ _ _ D.nd D.naut i (hpair i))
    (fun i => GlobalTheory.T.pointDeterminedBySplitComponents_of_baseChange _ _ _ D.nd D.naut i (hbc i) (hsplit i) (hrep i))
  exact (GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage.thetaTMapsIntoEig_iff_map_le D.nd D.naut).1 h i x Sig hx hSig

end GlobalTheory.RowTie
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowsCClose

theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), Join P → GlobalTheory.NRows.RowsA D →
    GlobalTheory.NRows.RowsB D → Formalism.MainNotions.SumRepresentations.adm1 D → Formalism.MainNotions.SumRepresentations.adm8 D → Formalism.MainNotions.SumRepresentations.Conclusion1 D →
    (∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i) → GlobalTheory.NRows.RowsC D := by
  intro hL D P J hA hB a1 a8 p1 hi
  obtain ⟨p41, _, p42⟩ := p1
  obtain ⟨tl, lt, io, rb⟩ := GlobalTheory.TieLabAt.main hL D P
  have iface := GlobalTheory.AdmIface.main D
  have bc : ∀ i, BCEx D.nd D.naut i := iface.1 a1
  have lift : ∀ i, GlobalTheory.ThetaExh.LiftParam D.nd D.naut i := iface.2.2.1 p42
  have isot : Rows.IsotInternal D.what₂ := iface.2.2.2.2.2.mp a8
  have rho : GlobalDatumResidualRepCondition D :=
    GlobalTheory.ParamRep.jointCond_rho D hA.tie0 hA.a2 hB.a4 hA.a5 p41 (GlobalTheory.GoodCuspPoint.main D tl)
      (GlobalTheory.XiOver.main D P.cf P.C P.tp P.chr P.val hA.tie0 hA.a2 hA.a5)
  have rp : RowRepAtG D :=
    GlobalTheory.RowRepOcc.rowRepAtG_of_rowPoint D hA.tie0 hA.a2 hA.a5 p42 rho hA.gsp (GlobalTheory.T.rowPoint_of_conditions hL D P p42 p41)
  exact
    { c4b := GlobalTheory.RowTie.tameGenerator_residual D rb io lt rp
      rho := rho
      dz := GlobalTheory.GoodDepthZero.main D hA.tie0 hB.a4 p41 hA.gsp
      parUp := GlobalTheory.RowTie.parUpRec_of_ties D P.T hB.thetaOne (fun i => (hi i).1) bc (fun i => (hi i).2.1)
        (fun i => (hi i).2.2)
      downMem := GlobalTheory.RowTie.downMemRec_of_ties D P.T hB.thetaOne isot
        (fun i => GlobalTheory.PartOrthPin.main hL D P i ⟨J.rowM i⟩) (fun i => GlobalTheory.T.type_orthogonality_of_form hL D P i (J.form i))
        (fun i => (hi i).1) bc (fun i => (hi i).2.1)
      goodPart := GlobalTheory.Proof.GoodComponentRecursion.goodPartRec_of_ties D P.T hB.thetaOne lift (fun i => GlobalTheory.T.local_point_theta_exhaustion hL D P i) bc
        (fun i => (hi i).2.1) }

end GlobalTheory.RowsCClose
end
