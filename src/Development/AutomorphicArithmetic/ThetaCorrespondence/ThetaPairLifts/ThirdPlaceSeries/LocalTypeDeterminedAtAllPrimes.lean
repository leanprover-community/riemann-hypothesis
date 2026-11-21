import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingEigenOfDepthZeroSupport
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsAOfJumpCountStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DepthZeroEigenSpanAdmissibleStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DepthZeroEigenSpanAdmissible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZlStableAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JumpsCardOfBuilt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedConditionOfLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SClose
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTerBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReadingStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisTameLabelMu
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiDeRhamWeilDeligne
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsobaricRigidOfPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabRcAtMulUnr
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameLabelDeterminant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIffStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatePlacesCompletionStatement
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ArtinTr
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Imports
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemSatisfiesLocalProperty
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaPolynomialCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaPolynomialCompatible

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.PendLayer
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem atMem_mono {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p)
    (hpq : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T w Z Wt p0 t nch n c (H kp w Z Wt p0 t nch n xd c a b d)
theorem atMem_and' {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p) (h' : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun K B f T w Z Wt p0 t nch n c => p K B f T w Z Wt p0 t nch n c ∧ q K B f T w Z Wt p0 t nch n c :=
  EvG.imp (EvG.inter h h') fun _ _ _ _ _ hK => large₂.imp (large₂.inter hK.1 hK.2) fun _ _ _ _ H kp w Z Wt p0 t nch n xd c a b d =>
    ⟨H.1 kp w Z Wt p0 t nch n xd c a b d, H.2 kp w Z Wt p0 t nch n xd c a b d⟩
theorem atMem_mono_of_colPin {q : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), w.Lt → Prop}
    (h : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), q B f T w Z) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ B f T w Z _ _ _ _ _ _ => q B f T w Z :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ T _ H kp w Z _ _ _ _ _ _ _ _ _ _ => H kp T w Z
end GlobalTheory.HeightCounting.Up.PendLayer
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ChiOneAbove
theorem character_trivial_above_place_admissible_alt (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) :
    Formalism.MainNotions.SumRepresentations.adm5 D := by
  have hrig : IsobaricRigid D.nd D.naut := _root_.GlobalTheory.NPin.isobaricRigid_of_pin_alt hPr.fin hPr.js hL D P
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hPr.cheb D
  exact (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩
end GlobalTheory.ChiOneAbove
end
section
end
end
end

section
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ChiOneAbove
theorem main_alt_alt_alt : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.IsdRW D.loc D.nbr i w hw (PairedCharacterCondition.chiGL (D := D) i) ∧
    D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (PairedCharacterCondition.chiGL (D := D) i)) w =
      D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)
        (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) := by
  intro hPr hL D P i w hw
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D := GlobalTheory.BlockCharInf.main D P.cf P.C P.tp P.chr
  have h2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D := _root_.UpperTheory.GalS.galClose_alt hPr hL D P
  have h5 := _root_.GlobalTheory.ChiOneAbove.character_trivial_above_place_admissible_alt hPr hL D P
  obtain ⟨ρ, hρc, haway, habove⟩ :=
    (_root_.UpperTheory.GalS.weak' h2 i).2.2 (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (GlobalTheory.ChiOneNoPt.sOne D)
      (GlobalTheory.ChiOneNoPt.integral D hB i)
  have hρ := GlobalTheory.ChiOneNoPt.eq_chi D h5 i w hw ρ hρc haway
  obtain ⟨hdR, hwd, -⟩ := habove w hw
  subst hρ
  refine ⟨((D.loc_tie i w hw).2.1 1 _ (GlobalTheory.JumpDictionaryFoundation.continuous_chiGL D i 1)).2.1.1 hdR, hwd⟩
end GlobalTheory.ChiOneAbove
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ChiOneAbove
end GlobalTheory.ChiOneAbove
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isdRW_chiGL_at_places_over_l : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), Br.IsdRW D.loc D.nbr i w hw (PairedCharacterCondition.chiGL (D := D) i) ∧ D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (PairedCharacterCondition.chiGL (D := D) i)) w = D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) := by
  atlas_forward_decl _root_.GlobalTheory.ChiOneAbove.main_alt_alt_alt
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LabFixed
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL
theorem lab_rcAt_ofDet_mul_eq (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (k : Fin 2) (v : D.nd.PlG k)
    (ξ η : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ →* ℂˣ) (hξ : IsSmoothChar ξ)
    (hη : IsSmoothChar η) (hu : ∀ x, Formalism.L2.Host.IsUnitAt (D.naut.plGw k v) x → η x = 1) (hξη : IsSmoothChar (ξ * η)) :
    WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 (ξ * η) hξη)) =
      WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 ξ hξ)) := by
  unfold _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  have e1 : LocLanglands.cls (Irr.ofDet 1 (ξ * η) hξη).toIrrRep = (GlobalTheory.LocGL.IrrGL.ofChar ξ hξ).tw η hη := by
    rw [GlobalTheory.LocGL.IrrGL.tw_ofChar]; rfl
  have e2 : LocLanglands.cls (Irr.ofDet 1 ξ hξ).toIrrRep = GlobalTheory.LocGL.IrrGL.ofChar ξ hξ := rfl
  rw [e1, e2, _root_.UpperTheory.One.M.LawsM.twist H _ _ _ (UpperTheory.One.M.good_ofChar ξ hξ), H.one η hη, lpChar_lpOfChar, WD.lab_lpTwist]
  intro σ
  have hd := ha.ord_eq (ineIncl _ σ)
  rw [deg_ineIncl, neg_zero] at hd
  apply hu
  have h0 : Valued.v ((a ((ineIncl _) σ) : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ) :
      HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v)) ≠ 0 := by simp
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero] at hd
  unfold Formalism.L2.Host.IsUnitAt
  rw [← WithZero.exp_log h0, hd, WithZero.exp_zero]
end GlobalTheory.LabFixed
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LabFixed
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL
theorem labLP_twist_eq_labAt_ofDet : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (s : ℝ), D.naut.items₂ k (D.naut.plGw k v) (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (D.naut.plGw k v)) s) = _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) := by
  intro hPr hL D P S hT i k v hw hχ s
  haveI := host_isCMField D.host
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, (j : ℕ) + 1 = D.nd.j i := by
    have := D.nd.j_range i
    exact ⟨⟨D.nd.j i - 1, by omega⟩, by simp only; omega⟩
  have hμ : IsComp (P.tp.tup (D.nd.mu i) j) (D.naut.plGw k v) (S i _ hw).mu := hT.mu i _ hw j hj
  have hψ : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹ := by
    rw [P.chr.tw, P.chr.muC i j hj, P.chr.etaTinv]
  have hc : IsComp (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 (D.naut.plGw k v)
      ((P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹).loc (D.naut.plGw k v)) := by
    rw [hψ]; exact ⟨ParLaws.isSmoothChar_loc _ _, fun x => rfl⟩
  rw [P.lab k v, P.T.tw, WD.lab_lpTw, _root_.GlobalTheory.RankOneComp.e_locG_eq_rcAt_ofDet_of_isComp hPr.fin hL D P _ _ _ hc, _root_.GlobalTheory.PendOf.localLabelPolynomial]
  have hηs : IsSmoothChar (P.cf.eta.loc (D.naut.plGw k v))⁻¹ := by
    have := ParLaws.isSmoothChar_loc (P.cf.eta⁻¹) (D.naut.plGw k v)
    convert this using 1
    exact MonoidHom.ext fun x => rfl
  have hu : ∀ x, Formalism.L2.Host.IsUnitAt (D.naut.plGw k v) x → (P.cf.eta.loc (D.naut.plGw k v))⁻¹ x = 1 := by
    intro x hx
    rw [MonoidHom.inv_apply, P.cf.isEta.unr _ x hx, inv_one]
  have e : (P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹).loc (D.naut.plGw k v) =
      (S i _ hw).mu * (P.cf.eta.loc (D.naut.plGw k v))⁻¹ := by
    rw [GlobalTheory.Published.ParamAboveModel.eq_loc hμ]
    rfl
  have key : ∀ (ξ' : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ →* ℂˣ) (h' : IsSmoothChar ξ'),
      ξ' = (S i _ hw).mu * (P.cf.eta.loc (D.naut.plGw k v))⁻¹ →
      WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 ξ' h')) =
        WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 (S i _ hw).mu hχ)) := by
    rintro _ h' rfl
    exact _root_.GlobalTheory.LabFixed.lab_rcAt_ofDet_mul_eq hL D k v _ _ hχ hηs hu h'
  exact key _ _ e
end GlobalTheory.LabFixed
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
theorem GlobalTheory.LocLanglands.artin_transport_m_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (c : Ω ≃+* Ω) (j : E →+* E) (i : w.adicCompletion E ≃+* w'.adicCompletion E), (∀ z, c z ∈ A' ↔ z ∈ A) → (∀ x, c (algebraMap E Ω x) = algebraMap E Ω (j x)) → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E _ (j x)) → ∀ {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}, _root_.UpperTheory.One.M.LawsM a ha ε (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h) → ∀ {a' : Weil h' →* (w'.adicCompletion E)ˣ} {ha' : IsLocalArtin h' a'} {ε' : EpsFamily A'}, _root_.UpperTheory.One.M.LawsM a' ha' ε' (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h') → ∀ (ξ : (w'.adicCompletion E)ˣ →* ℂˣ), IsSmoothChar ξ → ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, c ((σ : G E Ω) z) = (σ' : G E Ω) (c z)) → ξ (Units.map i.toRingHom.toMonoidHom (a σ)) = ξ (a' σ') := by
  intro hL E Ω _ _ _ _ _ A A' w w' h h' c j i hcA hcj hi hij a ha ε H a' ha' ε' H' ξ hξ σ σ' hσ
  set iU : (w.adicCompletion E)ˣ →* (w'.adicCompletion E)ˣ := Units.map i.toRingHom.toMonoidHom with hiU
  have hcont : Continuous iU := Units.continuous_map hi
  have hs : IsSmoothChar (ξ.comp iU) := hξ.comp iU hcont
  obtain ⟨b, b', hb, hb', -, hρ⟩ := _root_.UpperTheory.One.M.New.field hL
    (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h') c j i hcA hcj hi hij 1
    (IrrRep.det (Fin 1) (ξ.comp iU) hs) (IrrRep.det (Fin 1) ξ hξ) (LinearEquiv.refl ℂ ℂ) (by
      intro g v
      have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom g) =
          iU (Matrix.GeneralLinearGroup.det g) := by
        ext
        simp [hiU, RingHom.map_det]
      show (LinearEquiv.refl ℂ ℂ) ((ξ.comp iU (Matrix.GeneralLinearGroup.det g) : ℂ) • v) = _
      show _ = ((ξ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom g)) : ℂ) • v)
      rw [hd]
      rfl) (UpperTheory.One.M.good_ofChar _ hs)
  have e1 : WD.mk b = WD.lpOfChar h ((ξ.comp iU).comp a) (ha.smooth hs) := hb.trans (H.one _ hs)
  have e2 : WD.mk b' = WD.lpOfChar h' (ξ.comp a') (ha'.smooth hξ) := hb'.trans (H'.one _ hξ)
  have k := congrFun (congrArg (fun f : Module.End ℂ (Fin 1 → ℂ) => f (fun _ => 1)) (hρ σ σ' hσ)) 0
  simp only [b.rho_apply_of_mk_eq_lpOfChar _ _ e1, b'.rho_apply_of_mk_eq_lpOfChar _ _ e2] at k
  simp at k
  exact Units.ext (by simpa [hiU] using k)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_places_completion_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (c : Ω ≃+* Ω) (j : E →+* E) (i : w.adicCompletion E ≃+* w'.adicCompletion E), (∀ z, c z ∈ A' ↔ z ∈ A) → (∀ x, c (algebraMap E Ω x) = algebraMap E Ω (j x)) → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E _ (j x)) → ∀ {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}, _root_.UpperTheory.One.M.LawsM a ha ε (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h) → ∀ {a' : Weil h' →* (w'.adicCompletion E)ˣ} {ha' : IsLocalArtin h' a'} {ε' : EpsFamily A'}, _root_.UpperTheory.One.M.LawsM a' ha' ε' (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h') → ∀ (ξ : (w'.adicCompletion E)ˣ →* ℂˣ), IsSmoothChar ξ → ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, c ((σ : G E Ω) z) = (σ' : G E Ω) (c z)) → ξ (Units.map i.toRingHom.toMonoidHom (a σ)) = ξ (a' σ') := by
  atlas_forward_decl _root_.GlobalTheory.LocLanglands.artin_transport_m_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LabConjPlace
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
end GlobalTheory.LabConjPlace
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.LabConjPlace in
theorem GlobalTheory.LabConjPlace.locComp_of_isRc_classMapD_cenLoc : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), LabAll D P.T → ∀ (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) → ∀ (w' : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w' → ∀ s : ℝ, D.naut.items₂ k w' (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w') s) = X - C ((u⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) := by
  intro hPr hL D P hLab S hS i k v hw hχ u _ hlab w' hc s
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := hLab
  have hw'over : w' ∈ placesOver D.host.E (D.host.g k) := by
    have h0 := D.naut.plGw_over k v
    simp only [placesOver, Set.mem_setOf_eq] at h0 ⊢
    exact (hc _ _ (by simp)).1 h0
  rw [hγ3 k w' hw'over, P.T.tw, WD.lab_lpTw]
  obtain ⟨jj, hjj⟩ : ∃ jj : Fin D.R.m, jj.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp; omega⟩
  set χ := D.naut.tw (D.naut.muC i) D.naut.etaTinv with hχdef
  set μH := P.tp.tup (D.nd.mu i) jj with hμH
  have e1 : (P.chr.e1 χ).1 = μH * P.cf.eta⁻¹ := by
    rw [hχdef, P.chr.tw, P.chr.muC i jj hjj, P.chr.etaTinv]
  have hcomp' : IsComp (P.chr.e1 χ).1 w' ((P.chr.e1 χ).1.loc w') := ⟨ParLaws.isSmoothChar_loc _ w', fun x => rfl⟩
  rw [_root_.GlobalTheory.T.T_e_locG_eq_rcAt_ofDet hPr.fin hL D P χ w' _ hcomp']
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w')); obtain ⟨a', ha', ε', H'⟩ := hOpn) | obtain ⟨a', ha', ε', -, H'⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w')
  change WD.lab _ _ (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w') (GlobalTheory.LocGL.IrrGL.ofChar ((P.chr.e1 χ).1.loc w') hcomp'.1)) = _
  rw [H'.one]
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, Hw⟩ := hOpn) | obtain ⟨a, ha, ε, -, Hw⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  have hlab' : WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v)
      (WD.lpOfChar (D.nd.plOm.2 (D.naut.plGw k v)) ((S i _ hw).mu.comp a) (ha.smooth hχ)) = X - C (u : ZMod (D.host.g k)) := by
    rw [← Hw.one _ hχ]; exact hlab
  have HS : TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) := by
    by_contra hn
    rw [WD.lab_of_not hn] at hlab'
    have := congrArg natDegree hlab'
    rw [natDegree_one, natDegree_X_sub_C] at this
    exact absurd this (by norm_num)
  have hdeg : (WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v)
      (WD.lpOfChar (D.nd.plOm.2 (D.naut.plGw k v)) ((S i _ hw).mu.comp a) (ha.smooth hχ))).natDegree =
      WD.lpDim (WD.lpOfChar (D.nd.plOm.2 (D.naut.plGw k v)) ((S i _ hw).mu.comp a) (ha.smooth hχ)) := by
    rw [hlab', natDegree_X_sub_C]; simp [WD.lpOfChar]
  have htame := WD.tame_of_natDegree_lab hdeg
  rw [WD.lpOfChar] at htame
  have hwild : ∀ σ : Weil (D.nd.plOm.2 (D.naut.plGw k v)), (σ : G _ _) ∈ Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) →
      ((S i _ hw).mu.comp a) σ = 1 := by
    intro σ hσ
    have := congrFun (LinearMap.congr_fun ((WD.tame_mk _).mp htame σ hσ) fun _ => 1) 0
    exact Units.ext (by simpa using this)
  have hval := (WD.lab_lpOfChar_eq_iff HS (ha.smooth hχ) hwild u).mp hlab'
  have hμw : μH.loc (D.naut.plGw k v) = (S i _ hw).mu := by
    obtain ⟨ξ₀, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E μH (D.naut.plGw k v)
    exact (huniq _ ⟨ParLaws.isSmoothChar_loc _ _, fun x => rfl⟩).trans (huniq _ (hS.mu i _ hw jj hjj)).symm
  obtain ⟨c, hcE, hcA, hcγ⟩ := hγ2 k v w' hc
  set τc : D.host.E ≃+* D.host.E := (D.host.conj : D.host.E ≃+* D.host.E) with hτc
  have hcE' : ∀ x, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (τc x) := hcE
  have hγ' : γ k w' = GlobalTheory.ConjTransport.conjG c τc hcE' (D.ntypes.tg k v) := by
    ext y
    rw [GlobalTheory.ConjTransport.conjG_apply]
    have := hcγ (c.symm y)
    rw [RingEquiv.apply_symm_apply] at this
    exact this
  have hIne' : γ k w' ∈ Ine (F := D.host.E) (D.nd.plOm.1 w') := by
    rw [hγ']; exact GlobalTheory.ConjTransport.conjG_mem_Ine c τc hcE' hcA HS.2.1
  have HS' : TeichmullerInertiaLabelCondition (D.nd.plOm.1 w') w' (D.ntypes.teichC k) (γ k w') :=
    ⟨GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw'over, hIne', HS.2.2⟩
  have hcsd : IsCSD D.host μH := by
    rw [hμH, ← P.chr.muC i jj hjj]; exact (P.chr.csd _).1 (D.naut.muC_csd i)
  obtain ⟨ic, hic, hicE, hicμ⟩ := GlobalTheory.T.conjSelfDual_heckeChar_conjugatePlace_component_inv D.host μH hcsd _ w' hc
  have htr : ∀ (σ : Weil (D.nd.plOm.2 (D.naut.plGw k v))) (σ' : Weil (D.nd.plOm.2 w')),
      (∀ z, c ((σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) z) = (σ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (c z)) →
      μH.loc w' (a' σ') = ((S i _ hw).mu (a σ))⁻¹ := by
    intro σ σ' hσ
    rw [← _root_.GlobalTheory.T.conjugate_places_completion_alt hL (D.nd.plOm.2 (D.naut.plGw k v)) (D.nd.plOm.2 w') c τc.toRingHom ic
      (fun z => (hcA z).symm) hcE' hic hicE Hw H' (μH.loc w') (ParLaws.isSmoothChar_loc _ _) σ σ' hσ, hicμ, hμw]
  have heta : ∀ σ' : Weil (D.nd.plOm.2 w'), (σ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w') →
      P.cf.eta.loc w' (a' σ') = 1 := fun σ' hσ' => loc_artin_ine ha' _ (P.cf.isEta.unr w') σ' hσ'
  have hξ : ∀ σ', ((P.chr.e1 χ).1.loc w') (a' σ') = μH.loc w' (a' σ') * (P.cf.eta.loc w' (a' σ'))⁻¹ := by
    intro σ'; rw [e1, HChar.loc_mul, HChar.loc_inv]
  have hwild' : ∀ σ' : Weil (D.nd.plOm.2 w'), (σ' : G _ _) ∈ Wild D.host.E (D.nd.plOm.1 w') →
      (((P.chr.e1 χ).1.loc w').comp a') σ' = 1 := by
    intro σ' hσ'
    have hA' : ∀ y, y ∈ D.nd.plOm.1 w' ↔ c.symm y ∈ D.nd.plOm.1 (D.naut.plGw k v) := fun y => by
      rw [hcA, RingEquiv.apply_symm_apply]
    have hσw : GlobalTheory.ConjTransport.conjG c.symm τc.symm (GlobalTheory.ConjTransport.symm_alg c τc hcE') (σ' : G _ _) ∈
        Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) :=
      GlobalTheory.ConjTransport.conjG_mem_wild c.symm τc.symm _ hA' hσ'
    let σ : Weil (D.nd.plOm.2 (D.naut.plGw k v)) := ⟨_, Ine_le_Weil _ (Wild_le_Ine hσw)⟩
    have h1 := htr σ σ' (fun z => by
      show c (GlobalTheory.ConjTransport.conjG c.symm τc.symm _ (σ' : G _ _) z) = _
      rw [GlobalTheory.ConjTransport.conjG_apply, RingEquiv.symm_symm, RingEquiv.apply_symm_apply])
    have h2 := hwild σ hσw
    rw [MonoidHom.comp_apply] at h2
    rw [MonoidHom.comp_apply, hξ, h1, heta σ' (Wild_le_Ine hσ'), h2]
    simp
  rw [WD.lab_lpOfChar_eq_iff HS' _ hwild']
  rw [MonoidHom.comp_apply, hξ, htr ⟨D.ntypes.tg k v, Ine_le_Weil _ HS.2.1⟩ _ (fun z => (hcγ z).symm),
    heta _ hIne', inv_one, mul_one]
  have hx : algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) ≠ 0 :=
    (_root_.map_ne_zero _).2 u.ne_zero
  rw [MonoidHom.comp_apply] at hval
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, ← hval, map_inv₀]
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, inv_mul_cancel₀ hx, map_one]
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeLabel_of_conjugate_place_alt : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), LabAll D P.T → ∀ (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) → ∀ (w' : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w' → ∀ s : ℝ, D.naut.items₂ k w' (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w') s) = X - C ((u⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) := by
  first | exact @_root_.GlobalTheory.LabConjPlace.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LabConjPlace.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LabConjPlace.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TieChiPin
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → ChiTOk D P.cf → PairedCharacterCondition.tieChi (D := D) := by
  intro hPr hL D P hRow hLab hChi i k hl v
  obtain ⟨S, hS, -, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hPr.fin hL D P hRow
  have hsp : IsSplitPl D.host (D.naut.plGw k v) := GlobalTheory.T.isSplitPlace_of_over_type_prime D k _ (D.naut.plGw_over k v)
  obtain ⟨htame, hχ, u, hu, hlab⟩ := _root_.GlobalTheory.T.nonGalois_tame_label_mu_alt hPr hL D P hChi S hS i k v hsp
  refine ⟨u, hu, fun w hw => ⟨fun hw0 => ?_, fun hc => ?_⟩⟩
  · obtain ⟨hdR, hwd⟩ := _root_.GlobalTheory.T.isdRW_chiGL_at_places_over_l hPr hL D P i w hw
    refine ⟨hdR, ?_⟩
    rw [hwd, hw0]
    rw [_root_.GlobalTheory.LabFixed.labLP_twist_eq_labAt_ofDet hPr hL D P S hS i k v hsp hχ, hlab]
  · obtain ⟨hdR, hwd⟩ := _root_.GlobalTheory.T.isdRW_chiGL_at_places_over_l hPr hL D P i w hw
    refine ⟨hdR, ?_⟩
    rw [hwd]
    exact _root_.GlobalTheory.T.placeLabel_of_conjugate_place_alt hPr hL D P hLab S hS i k v hsp hχ u htame hlab w hc _
end GlobalTheory.TieChiPin
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.PendLayer
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem tieChi_of_labAll_green_chi_cen (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hS : GlobalTheory.Published.DepthZeroSupport) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (hX : GlobalTheory.NJoin.Agree X P.M P.rep) (hJ : JumpsCard D.nd D.naut)
    (hlab : GlobalTheory.PendOf.LabAll D P.T) (hgreen : GlobalTheory.PendOf.GreenLab P.ty.grp) (hchi : ChiTOk D P.cf)
    (hcen : CenLoc D P.M) (hzl : GlobalTheory.PendOf.ZLStable D) (hci : GlobalTheory.PendOf.CenInt D) (hroots : RootsLL D) :
    PairedCharacterCondition.tieChi (D := D) ∧ ∃ Q : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q := by
  have hrow : ∀ i : D.nd.Loc, Nonempty (GlobalTheory.NPin.RowMod D P.rep (D.nd.j i)) := by
    intro i
    have h1 := (D.nd.j_range i).1
    have h2 := (D.nd.j_range i).2
    obtain ⟨Y, -⟩ := _root_.GlobalTheory.RowModCanon.main_alt_alt hP.hc hP.decay hL D P X hX ⟨D.nd.j i - 1, by omega⟩ (D.nd.j i) (by simp; omega)
    exact ⟨Y⟩
  have hA := _root_.UpperTheory.GalS.a_close_main hP.what₂ hL D P hJ
  have hZ := GlobalTheory.ZetaSer.rootsOfUnity_and_seriesIdempotent_rational D hroots
  exact ⟨_root_.GlobalTheory.TieChiPin.locComp_of_isRc_classMapD_cenLoc hP.what₂ hL D P hrow hlab hchi,
    _root_.GlobalTheory.PinClose.locComp_of_isRc_classMapD_cenLoc hP.what₂ hS hL D P hrow hlab hcen hgreen hchi hA.tie0 hA.a5 hzl hci (hZ.2 P.ty.grp) hZ.1⟩
theorem locComp_of_isRc_classMapD_cenLoc : HtCard → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DepthZeroSupport → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => PairedCharacterCondition.tieChi (D := w.D Z) ∧ ∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q := by
  intro hH hP hS hL
  have h1 := _root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_and' (_root_.GlobalTheory.T.cenLoc_zlStable_cenInt_at_members hL) (_root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_and' (_root_.GlobalTheory.HeightCounting.JumpsAt.jumpsCard_at_members_of_htCard hH hL)
    (_root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_and' (_root_.GlobalTheory.HeightCounting.Up.isTied_of_layer_member_alt hP hL) (_root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_mono_of_colPin (hL := hL) GlobalTheory.HeightCounting.Up.sizes_host_at_record)))
  refine _root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_mono h1 fun K B f T w Z Wt p0 t nch n c h => ?_
  obtain ⟨⟨hcen, hzl, hci⟩, hJ, ⟨X, hpin, -⟩, -, -, hroots, -⟩ := h
  have hM : X.P.M = c.a.all.gal.mt := hpin.M_eq
  exact _root_.GlobalTheory.HeightCounting.Up.PendLayer.tieChi_of_labAll_green_chi_cen hP hS (w.D Z) X.P X.X X.agree hJ hpin.lab hpin.green hpin.chiT (hM ▸ hcen) hzl hci hroots
end GlobalTheory.HeightCounting.Up.PendLayer
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tieChi_at_mem_of_depth_zero_inputs : (HtCard → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DepthZeroSupport → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => PairedCharacterCondition.tieChi (D := w.D Z) ∧ ∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.PendLayer.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.HeightCounting.Up.PendLayer.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.HeightCounting.Up.PendLayer.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
namespace GlobalTheory.TieInePolyPin
theorem inePol_eq_wdAt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) r) w) σ = (GlobalTheory.Pst.wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w)).inePol σ := by
  intro hL D P i w hw m r hc hpst σ hσ
  have hc' : Continuous (fun g => ((GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w g : GL _ _) : Matrix (Fin m) (Fin m) (Om (D.nd.l i)))) :=
    ((hc.matrix_map (GlobalTheory.T.continuous_iotaOQ' D.nd D.naut i)).comp continuous_subtype_val)
  rw [(P.wdOf i m (mapRep (iotaOQ D.nd D.naut i) r) w).1, P.T.inePol w _ σ hσ]
  obtain ⟨LL, Bw, hj, e2⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) (mapRep (iotaOQ D.nd D.naut i) r) w hw
  rw [e2]
  refine congrArg (fun x => GlobalTheory.WeilDeligne.WD.inePol x σ) ?_
  exact GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩
    (D.naut.iotaQC i) D.host.E D.nd.Om (D.nd.plOm.1 w) w _ _ Bw (D.nbr i w hw) (D.nd.plOm.2 w) hj (D.nbr_ind i w hw) m _ hc'
    (GlobalTheory.T.isPotSemistable_independent_of_inducingEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ D.host.E D.nd.Om (D.nd.plOm.1 w) _ _
      (D.nbr i w hw) Bw (D.nbr_ind i w hw) hj m _ hc' hpst) hpst
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.Pass.TieInePoly D := by
  intro hL D P i w hw K' h hN hF hS m r hc hpot σ hσ p hp d hd
  exact GlobalTheory.T.inertiaPolynomial_kills_potentiallyCrystalline_module D i w hw K' h hN hF hS m r hc hpot σ hσ p
    (hp.trans (_root_.GlobalTheory.TieInePolyPin.inePol_eq_wdAt_alt hL D P i w hw m r hc (GlobalTheory.T.potSemistable_of_potCrystalline_decompositionGroup D i w hw K' h hN hF hS m r hc hpot) σ hσ)) d hd
end GlobalTheory.TieInePolyPin
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tieInePoly_of_characterChoice : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.Pass.TieInePoly D := by
  atlas_forward_decl _root_.GlobalTheory.TieInePolyPin.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.TypePrimesFinished
theorem locComp_of_isRc_classMapD_cenLoc : GlobalTheory.HeightCounting.HtCard → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DepthZeroSupport → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => (PairedCharacterCondition.tieChi (D := w.D Z) ∧ (∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (w.D Z) ∧ GlobalTheory.TypeLeaf.SerLoc (w.D Z)) := by
  intro hC hP hS hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.tieChi_at_mem_of_depth_zero_inputs hC hP hS hL)
      (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_character_choice_pin_at_of_third_layer hP hL) (_root_.GlobalTheory.T.serLoc_at_member_of_published_inputs hP hL))) ?_
  intro K B f T w Z Wt p0 t nch n c h
  obtain ⟨⟨h1, h2⟩, ⟨P, _⟩, h4⟩ := h
  exact ⟨h1, h2, _root_.GlobalTheory.T.tieInePoly_of_characterChoice hL (w.D Z) P, h4⟩
end GlobalTheory.TypePrimesFinished
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tieChi_at_members_of_depthZero : GlobalTheory.HeightCounting.HtCard → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DepthZeroSupport → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => (PairedCharacterCondition.tieChi (D := w.D Z) ∧ (∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (w.D Z) ∧ GlobalTheory.TypeLeaf.SerLoc (w.D Z)) := by
  first | exact @_root_.GlobalTheory.TypePrimesFinished.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.TypePrimesFinished.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.TypePrimesFinished.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end
