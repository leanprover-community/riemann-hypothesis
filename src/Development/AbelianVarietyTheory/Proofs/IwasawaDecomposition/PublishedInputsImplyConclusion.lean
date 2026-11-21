import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.PeriodIntegrals.BesselMapUniq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsBaseJointFld
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayFieldLeAndExistsBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PinsCoordPre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstructedCoreOfAllConstructionStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvLgCanonical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHalfSelectionSplitPlacesBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsOfOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelThreeToFourStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaDataTrueRowsColumnsAllCompatible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefMapEmbeddingOfPositiveAtPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrmOfPosDef
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TargetMtOfAmbTie

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KsExactCond

theorem ksCond_exact : RayField → PrincipalIdealSt → CMCurveGoodOutsidePrimeSt →
    V4.KsCond fun B f => ∃ δ : FieldDat B.toPre, B.KsExact δ f := by
  intro hR hP hA
  refine ⟨Col2.InEx.ev_of_forall fun K B₀ f₀ S₁ S₂ hO s1 s2 => ?_, fun B B' f f' e hf hS => ?_⟩
  · obtain ⟨δ⟩ := nonempty_fieldDat hR hA B₀.toPre
    obtain ⟨B₁, e₁, k⟩ := (GlobalTheory.Mem.KsBase.exists_base_listField hR hP _ f₀ δ).2
    obtain ⟨B₂, e₂, k₂, l₂⟩ := Inh.exists_fixed B₁ (S₁ B₁.KsC) (s1 _)
    obtain ⟨B, e, l₃⟩ := BaseEnl.exists_enl B₂ (S₂ B₁.KsC B₂.fixedCoefficientFieldInComplex) (s2 _ _)
    have hk : B.KsC = B₁.KsC := e.KsC_eq.trans k₂
    have e' : B.toPre = B₀.toPre := e.1.trans (e₂.trans e₁)
    have hH : Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex) := by
      rw [hk, Has₂, e.fixedCoefficientField_eq]
      exact ⟨l₂, l₃⟩
    rw [← hk] at k
    clear e e₁ e₂ hO
    generalize B₀.toPre = P₀ at *
    subst e'
    exact ⟨B, f₀, rfl, HEq.rfl, ⟨δ, k⟩, hH⟩
  · have e' := e.1
    unfold Base.KsExact at hS ⊢
    rw [e.KsC_eq]
    clear e
    generalize B.KsC = F at *
    generalize B.toPre = P at *
    subst e'
    obtain rfl := eq_of_heq hf
    exact hS

end GlobalTheory.Mem.KsExactCond
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.NT GlobalTheory.Mem.Fld

namespace GlobalTheory.Mem.Top.Bl.KPxCond

theorem exists_prePin (K : Ctx) : ∃ P : Pre, K.Over P ∧ PrePin P :=
  ⟨GlobalTheory.StdFrameObj.coordPre K.P K.Lv, ⟨_, _, _, _, _, _, rfl, GlobalTheory.StdFrameObj.diagSpaces_coordPre K.P K.Lv⟩,
    fun a b h => PinsCoord.extTo_basis _ _ a b h⟩

theorem baseCond_KPx : RayField → PrincipalIdealSt → CMCurveGoodOutsidePrimeSt → StandardLattice.SiegelMassRatioCM → BaseCond KPx := by
  intro hR hP hA h2b
  exact baseCond_of (PP := fun P _ => PrePin P) (GlobalTheory.Mem.KsExactCond.ksCond_exact hR hP hA)
    (EvG.imp (evG_of_ev (ev_preX_frame h2b)) fun K _ _ _ _ hfr => by
      obtain ⟨P, hO, hp⟩ := exists_prePin K
      obtain ⟨f⟩ := (hfr P hO).2
      exact ⟨P, f, hO, hp⟩)

end GlobalTheory.Mem.Top.Bl.KPxCond
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_half_selection_split_places_base : ∀ B : Base, ∃ (Pv : HeightOneSpectrum (𝓞 B.host.F) → HeightOneSpectrum (𝓞 B.host.E)) (d : PlacesOverCommonPrime B.host), Formalism.L2.Col.IsSel B.fields Pv ∧ (∀ v, Pv v ∈ aboveF (L := B.host.E) B.host.F v) ∧ Half B Pv ∧ (∀ v hv, Pv v = d.P v hv) ∧ ∀ v hv, Pv v = d.P' v hv := by
  first | exact @GlobalTheory.Mem.Top.Bl.exists_half_selection_split_places | exact GlobalTheory.Mem.Top.Bl.exists_half_selection_split_places | (intros; apply GlobalTheory.Mem.Top.Bl.exists_half_selection_split_places <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.PinW

theorem valsRoots (K : Ctx) : large₂ K fun B f T => ∀ (px : PreX B.toPre) (I : ColIn B px), I.Ok →
    I.S = {p | p ∈ offSet B.toPre ∧ p ≠ B.host.pde ∧ p ≠ B.host.pde'} → Set.range I.xi = T.set f →
    (∀ a P, (I.xi a).UnrAt P → ∃ z : B.LL, B.embLL z = (((I.xi a).val P : ℂˣ) : ℂ)) ∧
    ∀ a, ∀ P ∈ I.Q a, ∃ z : B.LL, IsPrimitiveRoot z (Nat.card (𝓞 B.fields.E ⧸ P.asIdeal)) := by
  classical
  choose Z hZ gZ using fun (B : Pre) (Ξ : Set (HChar B.host.E)) => GlobalTheory.Mem.Col2.InEx.exists_holds 1 Ξ
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B _ _ _ Ξ => Z B Ξ, by simp,
    fun B _ _ _ Ξ z hz => hZ B Ξ z hz, fun B f T _ hH _ _ => ?_⟩
  intro px I h hS hxi
  refine ⟨fun a P _ => ⟨_, (h.xi_reads a _).symm⟩, fun a P hP => ?_⟩
  have hm : I.xi a ∈ T.set f := hxi ▸ Set.mem_range_self a
  have ht := GlobalTheory.Mem.Col2.InEx.isTwist_of_mem_set B f T _ hm
  have hf := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1
  have hold := gZ B.toPre _ hf B.LL B.embLL (fun z hz => B.mem_LLC.1 (hH.2 z hz)) _ hm ht.1
  have ht' : Chr.IsTwist B.host I.S (I.xi a) := by rw [hS]; exact ht
  obtain ⟨P', a1, a2⟩ := GlobalTheory.Mem.Col2.InEx.exists_ram_of_mem_QE B h.sel_ok (I.tup a) ht' (h.xi_reads a) hP
  obtain ⟨ζ, hζ⟩ := (hold.2 P' a1).2
  refine ⟨ζ, ?_⟩
  rw [pow_one] at hζ
  have e : Nat.card (𝓞 B.fields.E ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [e, a2]
  exact hζ

theorem step_pinned (h2b : StandardLattice.SiegelMassRatioCM) :
    Step KPx (fun _ _ _ _ => True) (fun K B f T => ∃ w : ColW B f T, Pinned K B f T w) := by
  have e1 := evG_of_ev (ev_preX_frame h2b)
  have e2 := evG_of_ev GlobalTheory.Mem.Col2.TwIdxEx.evLg_canonical
  have e3 := evG_all fun K => (valsRoots K).inter (GlobalTheory.Mem.Col2.InEx.lg_colIn K)
  refine ((e1.inter e2).inter e3).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨hfr, h41⟩, hv⟩ := H
  refine (h41.inter hv).imp fun B f T hO G hk _ _ => ?_
  obtain ⟨H, V, Lc⟩ := G
  obtain ⟨⟨δ, hδ⟩, hp⟩ := hk
  obtain ⟨Pv, d, hsel, habove, hhalf, hd1, hd2⟩ := GlobalTheory.T.exists_half_selection_split_places_base B
  obtain ⟨X, I, hok, hpins, htw, hjets, hsel', hC, hS, hxi, hval⟩ := H hp (hfr _ hO).1 Pv hsel
  obtain ⟨hv1, hv2⟩ := V X I hok hS hxi
  subst hsel'
  exact ⟨⟨X, I, hok, hC, hS, hxi, hpins, GlobalTheory.Mem.Col2.TC.laws_of_ok I hok, StepZero.law0 I hok _, δ, hδ, Lc.2.2,
      fun C W V S N G => (hval C W V S N G).1⟩,
    ⟨⟨htw, hjets, GlobalTheory.Mem.FieldsLaws.fields_ok B, habove, hhalf, d, ⟨hd1, hd2⟩, hv1, hv2⟩⟩⟩

end GlobalTheory.Mem.Top.Bl.PinW
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem pass_step_congr {α : Type*} (g : ∀ P : Pre, Fr P → α) {P P' : Pre} {f : Fr P} {f' : Fr P'} (h : P = P') (hf : HEq f f') :
    g P f = g P' f' := by
  subst h
  rw [eq_of_heq hf]

theorem pass_step : ∀ (KP : BaseP) (Q : V4.Slot) (r r' : AtP), BaseCond KP → Pass KP Q r → Step KP r r' → Pass KP Q r' := by
  classical
  intro KP Q r r' hK hR hS
  refine (EvG.inter hS hR).imp fun K _ _ _ _ H => ?_
  obtain ⟨hs, hr⟩ := H
  have hs' : large₂ K fun B f T => KP B f → r K B f T → r' K B f T :=
    (hs.inter (lg_forced K)).imp fun _ _ _ _ G a b => G.1 a G.2 b
  obtain ⟨S₁, P₁, A₀, S₂₀, a₁, a₂, hlg⟩ := hs'
  have hb : large₂ K fun B f T => (∀ z ∈ S₁ B.toPre f B.KsC, z ∈ B.fixedCoefficientFieldInComplex) ∧ P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex ⊆ T.pl :=
    ⟨S₁, P₁, fun _ _ _ _ _ => ∅, S₂₀, a₁, a₂, fun _ _ _ _ h p _ => ⟨h.1, p⟩⟩
  refine (hr.inter hb).imp ?_
  rintro B f T hO ⟨hr, h₁, hp⟩ hKP hT C W V S N G c q hx A S₂ hS₂
  obtain ⟨B', f', T', e, hf, hpl, hAv, hS', hr'⟩ := hr hKP hT C W V S N G c q hx
    (fun l => A l ∪ A₀ B.toPre f B.KsC B.fixedCoefficientFieldInComplex l) (fun P g Ξ => S₂ P g Ξ ∪ S₂₀ P g B.KsC B.fixedCoefficientFieldInComplex Ξ)
    (fun P g Ξ z hz => (Finset.mem_union.1 hz).elim (hS₂ P g Ξ z) (a₂ P g _ _ Ξ z))
  have hP : B'.toPre = B.toPre := e.1
  have hk : B'.KsC = B.KsC := e.KsC_eq
  have hl : B'.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex := e.fixedCoefficientField_eq
  have hO' : K.Over B'.toPre := hP ▸ hO
  have hLL : ∀ z ∈ S₂₀ B'.toPre f' B'.KsC B'.fixedCoefficientFieldInComplex (T'.set f'), z ∈ B'.LLC := by
    intro z hz
    rw [hk, hl] at hz
    obtain ⟨x, rfl⟩ := hS' z (Finset.mem_union_right _ hz)
    exact ⟨x, rfl⟩
  have r'' := hlg B' f' T' hO'
    ⟨by rw [hk, hl, pass_step_congr S₁ hP hf]; exact h₁, hLL⟩
    (by rw [hk, hl, pass_step_congr P₁ hP hf, hpl]; exact hp)
    (fun w v hv hA => hAv w v hv (Finset.mem_union_right _ (by
      rw [hk, hl, pass_step_congr A₀ hP hf] at hA; exact hA)))
    (hK.enl B B' f f' e hf hKP) hr'
  exact ⟨B', f', T', e, hf, hpl, fun w v hv hA => hAv w v hv (Finset.mem_union_left _ hA),
    fun z hz => hS' z (Finset.mem_union_left _ hz), r''⟩

end GlobalTheory.Mem.Top.GroupRetwisting
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.MemberEx2

theorem step_start (h2b : StandardLattice.SiegelMassRatioCM) :
    Step KPx (fun _ B _ T => T = TwDat.untw B T.pl) (fun K B f T => ∃ w : ColW B f T, Start K B f T w) :=
  (Step.and (Step.of_all fun _ _ _ _ _ _ _ h => h)
      ((Step.of_all fun _ _ _ _ _ _ _ _ => trivial).trans (PinW.step_pinned h2b))).trans
    (Step.of_all fun _ _ _ _ _ _ _ H =>
      let ⟨w, hw⟩ := H.2
      ⟨w, hw, supp_of_untw w H.1, coh_of_untw H.1⟩)

theorem stepW_builtE {𝒮 : Slots} {p : WP} (hp : ∀ K B f T w, p K B f T w → Pinned K B f T w)
    (h4 : StepW (pinAnd (Has3 𝒮)) (Has4 𝒮)) (hc : StepW (pinAnd (Has4 𝒮)) (HasC (BuiltE 𝒮)))
    (h3 : StepW p (Has3 𝒮)) : StepW p (HasC (BuiltE 𝒮)) :=
  have q : StepW p Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => hp _ _ _ _ _ h
  (q.and ((q.and h3).trans h4)).trans hc

end GlobalTheory.Mem.Top.Bl.MemberEx2

namespace GlobalTheory.Mem.Top.Bl

theorem memberE_of_steps2 : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → StandardLattice.SiegelMassRatioCM →
    ∀ 𝒮 𝒮' : Slots, StepW Start (Has3 𝒮) → StepW (pinAnd (Has3 𝒮)) (Has4 𝒮) → AmbEx 𝒮 → DivEx 𝒮 → ThEx 𝒮 →
      ExportF KPx (IsBuiltE 𝒮) →
      Pass KPx (IsBuiltE 𝒮) (fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 𝒮' K B f T w) →
      StepW (pinAnd (Has3 𝒮')) (Has4 𝒮') → AmbEx 𝒮' → DivEx 𝒮' → ThEx 𝒮' →
      (∀ K B f T w Z c, BuiltE 𝒮' K B f T w Z c → GoodE 𝒮 K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd) → MemberE 𝒮 := by
  intro hR hP hC h2b 𝒮 𝒮' h3 h4 hA hD hT hE hPass h4' hA' hD' hT' hL
  have hB : BaseCond KPx := KPxCond.baseCond_KPx hR hP hC h2b
  have h1 : FirstG KPx (IsBuiltE 𝒮) :=
    step_hasCore (MemberEx2.step_start h2b)
      (MemberEx2.stepW_builtE (fun _ _ _ _ _ h => h.1) h4 (GlobalTheory.T.exists_constructedCore_of_all_construction_stages h2b 𝒮 hA hD hT) h3)
  have hW : StepW (fun K B f T w => Start K B f T w ∧ Has3 𝒮' K B f T w)
      (HasC fun K B f T w Z c => GoodE 𝒮 K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd) :=
    (MemberEx2.stepW_builtE (fun _ _ _ _ _ h => h.1.1) h4' (GlobalTheory.T.exists_constructedCore_of_all_construction_stages h2b 𝒮' hA' hD' hT')
      (StepW.of_all fun _ _ _ _ _ _ _ h => h.2)).trans
      (StepW.of_all fun _ _ _ _ _ _ _ H => let ⟨Z, c, hc⟩ := H; ⟨Z, c, hL _ _ _ _ _ _ _ hc⟩)
  have hS := step_hasCore (admitted := fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 𝒮' K B f T w)
    (Step.of_all fun _ _ _ _ _ _ _ h => h) hW
  have h2 : SecondG KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) :=
    GlobalTheory.Mem.Top.GroupRetwisting.pass_step KPx _ _ _ hB hPass (hS.trans (Step.of_all fun _ _ _ _ _ _ _ H =>
      let ⟨C, W, V, S, N, G, c, hc⟩ := H
      ⟨C, W, V, S, N, G, c, positionOf_ind (R := fun K X f T c => IsBuiltE 𝒮 K X f T c ∧ DQ.TwAllAt X.toD7 c.O.nch c.O.xd ∧
        IsGoodE 𝒮 K X f T c) (fun _ _ _ _ _ _ _ h => ⟨positionOf_intro h.1.1, h.2, positionOf_intro h.1⟩) hc⟩))
  exact ⟨hB, h1, hE, h2⟩

end GlobalTheory.Mem.Top.Bl

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_member_of_construction_steps_secondPass : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → StandardLattice.SiegelMassRatioCM → ∀ 𝒮 𝒮' : Slots, StepW Start (Has3 𝒮) → StepW (pinAnd (Has3 𝒮)) (Has4 𝒮) → AmbEx 𝒮 → DivEx 𝒮 → ThEx 𝒮 → ExportF KPx (IsBuiltE 𝒮) → Pass KPx (IsBuiltE 𝒮) (fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 𝒮' K B f T w) → StepW (pinAnd (Has3 𝒮')) (Has4 𝒮') → AmbEx 𝒮' → DivEx 𝒮' → ThEx 𝒮' → (∀ K B f T w Z c, BuiltE 𝒮' K B f T w Z c → GoodE 𝒮 K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd) → MemberE 𝒮 := by
  atlas_forward_decl GlobalTheory.Mem.Top.Bl.memberE_of_steps2
end

section
section
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem oLatTie_fg_span_top : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (σ : K →+* ℂ) {O : Type} [CommRing O] {φO : O →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] (M : Formalism.BasicNotions.Rows.OLat O φO W) (j : (Fin n → K) →ₛₗ[σ] W) (N : Submodule (𝓞 K) (Fin n → K)), (LinearIndependent ℂ fun i => j (Pi.single i 1)) → Formalism.L2.DIV.OLatTie σ M j N → N.FG ∧ Submodule.span K (N : Set (Fin n → K)) = ⊤ := by
  intro K _ _ _ n σ O _ φO W _ _ M j N hli hT
  classical
  obtain ⟨hgen, hmem⟩ := hT
  have hj : ∀ x, j x = ∑ i, σ (x i) • j (Pi.single i 1) := by
    intro x
    conv_lhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ]
    simp
  have hinj : Function.Injective j := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hj] at hx
    have h0 := Fintype.linearIndependent_iff.1 hli _ hx
    funext i
    exact σ.injective (by simpa using h0 i)
  have hgen' : ∀ v, ∃ x, v ∈ M.gen → j x = v := by
    intro v
    by_cases hv : v ∈ M.gen
    · obtain ⟨x, hx⟩ := hgen v hv
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose pre hpre using hgen'
  have hN : N = Submodule.span (𝓞 K) (pre '' (M.gen : Set W)) := by
    ext x
    rw [hmem, Submodule.mem_span_image_finset_iff_exists_fun']
    refine exists_congr fun a => ?_
    have : ∑ v ∈ M.gen, σ ((a v : 𝓞 K) : K) • v = j (∑ v ∈ M.gen, a v • pre v) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← algebraMap_smul K (a v) (pre v), map_smulₛₗ, hpre v hv]
    rw [this]
    exact ⟨fun h => (hinj h).symm, fun h => congrArg j h.symm⟩
  refine ⟨hN ▸ Submodule.fg_span ((M.gen.finite_toSet).image pre), ?_⟩
  rw [hN]
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  let B := Module.Basis.span hli
  let F0 := B.constr ℂ (fun i => σ (f (Pi.single i 1)))
  obtain ⟨F, hFF⟩ := LinearMap.exists_extend F0
  have hFe : ∀ i, F (j (Pi.single i 1)) = σ (f (Pi.single i 1)) := by
    intro i
    have h1 : (B i : W) = j (Pi.single i 1) := by simp [B, Module.Basis.span_apply hli i]
    rw [← h1]
    have h2 := LinearMap.congr_fun hFF (B i)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h2]
    simp [F0]
  have hF : ∀ x, F (j x) = σ (f x) := by
    intro x
    rw [hj, map_sum]
    conv_rhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hFe]
    simp
  have hF0 : F = 0 := by
    apply LinearMap.ext_on M.span_top
    intro v hv
    rw [← hpre v hv, hF]
    have : f (pre v) ∈ (⊥ : Submodule K K) := by
      rw [← hf]
      exact Submodule.mem_map_of_mem
        (Submodule.subset_span (Submodule.subset_span ⟨v, hv, rfl⟩))
    rw [(Submodule.mem_bot K).1 this]
    simp
  apply hf0
  refine LinearMap.ext fun x => σ.injective ?_
  rw [← hF, hF0]
  simp

end GlobalTheory
end

open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fg_span_top_of_lattice_compatible_semilinear : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (σ : K →+* ℂ) {O : Type} [CommRing O] {φO : O →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] (M : Formalism.BasicNotions.Rows.OLat O φO W) (j : (Fin n → K) →ₛₗ[σ] W) (N : Submodule (𝓞 K) (Fin n → K)), (LinearIndependent ℂ fun i => j (Pi.single i 1)) → Formalism.L2.DIV.OLatTie σ M j N → N.FG ∧ Submodule.span K (N : Set (Fin n → K)) = ⊤ := by
  atlas_forward_decl GlobalTheory.oLatTie_fg_span_top
end

section
section
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory.AmbNormTie

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hform_eq_sum {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H x y = ∑ i, ∑ j, star (x i) * H i j * y j := by
  simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem j_eq_sum {σ : K →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (x : Fin n → K) :
    j x = ∑ i, σ (x i) • j (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (x i) : Fin n → K) = x i • Pi.single i 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, LinearMap.map_smulₛₗ]

theorem j_ne_zero {σ : K →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    {x : Fin n → K} (hx : x ≠ 0) : j x ≠ 0 := by
  intro h0
  apply hx
  funext i
  rw [j_eq_sum] at h0
  have := Fintype.linearIndependent_iff.mp hli (fun i => σ (x i)) h0 i
  simpa using this

theorem normAt_sq {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι K V) (Xf : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b Xf v x ^ 2 = (Formalism.HermitianLatticesTheory.majAt b Xf v x x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.majAt
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem hAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H : Matrix (Fin n) (Fin n) K)
    (hin : ∀ x y, inner ℂ (j x) (j y) = σ (Formalism.DivisionValues.hform H x y)) :
    (∀ x y, hAt H (InfinitePlace.mk σ) x y = inner ℂ (j x) (j y)) ∨
      (∀ x y, hAt H (InfinitePlace.mk σ) x y = star (inner ℂ (j x) (j y))) := by
  rcases InfinitePlace.embedding_mk_eq σ with he | he
  · left
    intro x y
    rw [hin, hform_eq_sum, hAt, he]
    simp only [map_sum, map_mul, hσ]
    rfl
  · right
    intro x y
    rw [hin, hform_eq_sum, hAt, he]
    simp only [map_sum, map_mul, hσ, star_sum, star_mul', ComplexEmbedding.conjugate_coe_eq, Complex.star_def]

theorem posAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K)
    (op : W →ₗ[ℂ] W) (hT : FormsTie σ j H E op) :
    PosAt H (InfinitePlace.mk σ) ∧ ∀ x, hAt H (InfinitePlace.mk σ) x x = ((‖j x‖ ^ 2 : ℝ) : ℂ) := by
  have hd : ∀ x, hAt H (InfinitePlace.mk σ) x x = ((‖j x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rcases hAt_mk hσ j H hT.inner with h | h
    · rw [h, inner_self_eq_norm_sq_to_K]; push_cast; rfl
    · rw [h, inner_self_eq_norm_sq_to_K]; push_cast; simp [Complex.star_def]
  refine ⟨⟨fun x y => ?_, fun x hx => ?_⟩, hd⟩
  · rcases hAt_mk hσ j H hT.inner with h | h
    · rw [h, h]; exact (inner_conj_symm (j y) (j x)).symm
    · rw [h, h, star_star]; exact inner_conj_symm (j x) (j y)
  · rw [hd, Complex.ofReal_re]
    exact pow_pos (norm_pos_iff.mpr (j_ne_zero j hT.li hx)) 2

end GlobalTheory.AmbNormTie

open GlobalTheory.AmbNormTie in

theorem GlobalTheory.AmbNormTie.normAt_frm_mk : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (σ : K →+* ℂ), (∀ a, σ (star a) = starRingEnd ℂ (σ a)) → ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W), Formalism.L2.DIV.FormsTie σ j H E op → ∀ x : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x = ‖j x‖ := by
  intro K _ _ _ _ σ hσ W _ _ n j H E op hT x
  obtain ⟨hP, hd⟩ := posAt_mk hσ j H E op hT
  have hPD := GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace H (InfinitePlace.mk σ) hP
  have hmaj : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x x =
      hAt H (InfinitePlace.mk σ) x x := by
    rw [Formalism.L2.DIV.majAt_eq, GlobalTheory.AmbCrd.frm_of_posDef H _ hPD, (Formalism.L2.DIV.frameOfSpec _ _ hPD).2,
      GlobalTheory.Core.AmbTieStep.hAt_eq_dot]
  have h2 := normAt_sq (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x
  rw [hmaj, hd, Complex.ofReal_re] at h2
  have h0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x :=
    Real.sqrt_nonneg _
  exact (pow_left_inj₀ h0 (norm_nonneg _) two_ne_zero).mp h2
end

open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normAt_standardFrame_eq_norm_complexForm : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (σ : K →+* ℂ), (∀ a, σ (star a) = starRingEnd ℂ (σ a)) → ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W), Formalism.L2.DIV.FormsTie σ j H E op → ∀ x : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x = ‖j x‖ := by
  atlas_forward_decl GlobalTheory.AmbNormTie.normAt_frm_mk
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AmbCrd

open Formalism.L2.DIV Formalism.L2.Rows

theorem majAt_frm {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (h : PosAt H v) (x y : Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (frm H) v x y = hAt H v x y := by
  have hp := GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace H v h
  rw [majAt_eq, frm_of_posDef H v hp, (frameOfSpec _ _ hp).2]
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

section Level

variable (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ} (A : FamIn D.what₂.LL G Pl0 T m)
  (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)

theorem rNab_rdx {t1 t2 : T} (e : t1 = t2) (h : rDim D A P ψ t2 = rDim D A P ψ t1) :
    rNab D A P ψ t2 = (rNab D A P ψ t1).map ((rdx h).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  subst e
  ext x
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, rdx_refl]
  exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, e⟩ => e ▸ hy⟩

theorem majAt_rdx {t1 t2 : T} (e : t1 = t2) (h : rDim D A P ψ t2 = rDim D A P ψ t1) (v : InfinitePlace D.what₂.LL)
    (hp : PosAt (rH D A P ψ t1) v) (x y : Fin (rDim D A P ψ t1) → D.what₂.LL) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (frm (rH D A P ψ t2)) v (rdx h x) (rdx h y) =
      hAt (rH D A P ψ t1) v x y := by
  subst e
  have := D.tcLL
  rw [rdx_refl, rdx_refl]
  exact majAt_frm _ v hp x y

end Level

theorem tie_level (D : D7) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) {G : Type} [Group G] [Fintype G] {Pl0 T T' : Type} {m : ℕ} (A : FamIn D.what₂.LL G Pl0 T m)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (tp : D.what₂.Tup → T)
    (j : ∀ μ, (Fin (rDim D A P ψ (tp μ)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] S.Amb μ)
    (E : ∀ μ, Matrix (Fin (rDim D A P ψ (tp μ))) (Fin (rDim D A P ψ (tp μ))) D.what₂.LL)
    (op : ∀ μ, S.Amb μ →ₗ[ℂ] S.Amb μ)
    (hF : ∀ μ, FormsTie D.what₂.embLL (j μ) (rH D A P ψ (tp μ)) (E μ) (op μ))
    (hL : ∀ μ, OLatTie D.what₂.embLL (S.Mtilde μ) (j μ) (rNab D A P ψ (tp μ)))
    (f : T' → T) (μ0' : T') (tup : T' → D.what₂.Tup) (hf : ∀ s, f s = tp (tup s))
    (j' : ∀ s, (Fin (rDim D (A.comap f μ0') P ψ s) → D.what₂.LL) →ₛₗ[D.what₂.embLL] S.Amb (tup s))
    (hs : ∀ s, SameOn (j (tup s)) (j' s)) :
    ∃ (Fm : AmbForm D S) (J : AmbIds D (A.comap f μ0') S Fm P ψ tup), AmbTie D (A.comap f μ0') S Fm P ψ tup j' J := by
  have := D.tcLL
  let Fm : AmbForm D S :=
    { MtH := fun μ => toHLat (frm (rH D A P ψ (tp μ))) (rNab D A P ψ (tp μ))
      jAmb := j
      MtH_good := fun μ _ => ⟨frm_det _, GlobalTheory.T.fg_span_top_of_lattice_compatible_semilinear D.what₂.embLL (S.Mtilde μ) (j μ) _ (hF μ).li (hL μ)⟩
      jAmb_basis := fun μ _ => by
        show LinearIndependent ℂ (fun i => j μ (Pi.basisFun D.what₂.LL _ i)) ∧
          Submodule.span ℂ (Set.range (fun i => j μ (Pi.basisFun D.what₂.LL _ i))) = ⊤
        simp only [Pi.basisFun_apply]
        exact ⟨(hF μ).li, (hF μ).span⟩
      jAmb_lat := fun μ _ x => (hL μ).2 x
      jAmb_gen := fun μ _ => (hL μ).1
      jAmb_norm := fun μ _ x => GlobalTheory.T.normAt_standardFrame_eq_norm_complexForm D.what₂.embLL D.starLL_cx (j μ) _ _ _ (hF μ) x }
  let J : AmbIds D (A.comap f μ0') S Fm P ψ tup := ⟨fun s _ => rdx (hs s).1⟩
  refine ⟨Fm, J, ⟨fun s _ x => ?_, fun s _ => ?_, fun s _ v hv x y => ?_⟩⟩
  · refine (hs s).2 _ x fun a a' e => ?_
    show x (Fin.cast (hs s).1 a) = x a'
    congr 1
    exact Fin.ext e
  · exact rNab_rdx D A P ψ (hf s) _
  · exact majAt_rdx D A P ψ (hf s) _ v hv x y

set_option maxHeartbeats 3000000 in

theorem ambEx_of_rx : ∀ 𝒮 : Slots, 𝒮.Rx = RX → AmbEx 𝒮 := by
  rintro ⟨Rx, Nx, Sx, Ox⟩ h
  dsimp only at h
  subst h
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro Z l
  have x : RXs l.what₂ := l.rx
  have hsub : R3.tuOf w.I (R3.usedOf w.I T l.Wt) ⊆ R3.tuOf w.I Set.univ := fun τ hτ => by
    obtain ⟨a, -, e⟩ := (R3.mem_tuOf w.I).1 hτ
    exact (R3.mem_tuOf w.I).2 ⟨a, Set.mem_univ _, e⟩
  have hf : ∀ s, TupF.incl hsub s = tAll w.I (l.what₂.r.Y.tup s) := fun s => by
    apply Subtype.ext
    show s.1 = w.I.tup (l.what₂.r.Y.tup s)
    have e : l.what₂.r.Y.tup s = R3.ixOf w.I _ s := l.what₂.r.tup_ix s
    rw [e, R3.tup_ixOf]
  obtain ⟨a, J, hJ⟩ := tie_level (w.st Z).toD7 (RowSide.sharp _) (famAll l.what₂) (R3.lev1 w.I) (R3.chr1 w.I) (tAll w.I)
    x.all.jA _ _ x.all.formsA x.all.latA (TupF.incl hsub) (mu0F _) l.what₂.r.Y.tup hf l.what₂.r.Y.jA x.jA_use
  obtain ⟨a0, J0, hJ0⟩ := tie_level (w.st Z).toD7 l.p0.s (famAll l.what₂) (R3.lev0 w.I) (R3.chr0 w.I) (tAll w.I)
    x.all.jA0 _ _ x.all.formsAtBottomLevel x.all.latA0 (TupF.incl hsub) (mu0F _) l.what₂.r.Y.tup hf l.what₂.r.Y.jA0 x.movedReadingSameMaps_baseReading_agrees
  exact ⟨a, a0, ⟨J, hJ⟩, ⟨J0, hJ0⟩⟩

end GlobalTheory.AmbCrd

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw GlobalTheory.ShFam
open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Mem.Th

namespace GlobalTheory.Mem.Top.Closing

theorem divEx_geoCl (h1 : GlobalTheory.NT.RayField) (h2 : GlobalTheory.Published.PrincipalIdealSt) (h3 : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt)
    (R : RPosition) (N : NCondition) (S : SPosition) : DivEx ⟨R, N, S, OX (geoCl anyGeometry)⟩ := by
  have h := GlobalTheory.Mem.Top.DivRec.divEx_of_ox h1 h2 h3 ⟨R, N, S, OX anyGeometry⟩ rfl
  refine GlobalTheory.Mem.Top.Bl.StepW.trans h (GlobalTheory.Mem.Top.Bl.StepW.of_all ?_)
  intro K B f T w _ _ hw Z l
  obtain ⟨Y, hY1, hY2, hY3, hY4⟩ := hw Z
    { g := l.g, coh := l.coh, Wt := l.Wt, p0 := l.p0, what₂ := l.what₂, rx := l.rx, nch := l.nch, n := l.n, xd := l.xd,
      chiT := l.chiT, nx := l.nx, col := l.col, real := l.real, dsig_eq := l.dsig_eq, del := l.del, sx := l.sx }
  refine ⟨Y, hY1, hY2, hY3, fun O t e1 e2 e3 => ?_⟩
  obtain ⟨o⟩ := hY4 O t e1 e2 e3
  exact ⟨⟨geoCl_of o.geo, o.lam⟩⟩

theorem goodE_of_builtE (hL : GlobalTheory.Published.LocalLanglandsGL) (N Ng : NExt hL) (S : SExt) (Γ : GeoP)
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, Ng K B f T w Z Wt p0 t nch n xd c →
      Nonempty (N K B f T w Z Wt p0 t nch n xd c) ∧ GoodO (w.D Z) nch xd) :
    ∀ K B f T w Z c, BuiltE (prmR Ng S Γ).s K B f T w Z c →
      GoodE (prmR N S Γ).s K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd := by
  intro K B f T w Z c hc
  obtain ⟨b, hb⟩ := hc
  obtain ⟨⟨nx⟩, hg⟩ := hN _ _ _ _ _ _ _ _ _ _ _ _ _ b.nx.2
  have ch : GlobalTheory.HeightCounting.ChoiceC (w.D Z) c.O.nch := b.nx.1.a.all.choice
  refine ⟨⟨⟨{ b with nx := ⟨b.nx.1, nx⟩ }, hb⟩, hg⟩, fun v hv => ⟨ch.conj v hv, ch.sd_conj v hv⟩, ?_⟩
  obtain ⟨I, hI, hI1, -⟩ := hg.tw
  refine ⟨I.N0, I.S, ?_⟩
  rcases I with ⟨E, N0, S'⟩
  dsimp only at hI
  subst hI
  exact hI1

theorem io_zero (𝒮 : Slots) (h : 𝒮.Rx = RX) : ∀ K B f T (w : ColW B f T) (Z : w.Lt) Wt p0 (t : RowsT K w Z Wt p0),
    𝒮.Rx K B f T w Z Wt p0 t → ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0 := by
  intro K B f T w Z Wt p0 t r μ hμ j _
  rw [h] at r
  exact (RXs.io r μ j hμ).1

theorem memberE_closing : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.BesselMapUniq.BesselMapUniq → Vol.DiscreteSeriesExist → Vol.FormalDegreeFormula₂ → StandardLattice.SiegelMassRatioCM → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N Ng : NExt hL), StepW Start (Has3 (prmR N SExt.none (geoCl anyGeometry)).s) → LevelThreeCondition (prmR N SExt.none (geoCl anyGeometry)).s → LevelThreeCondition (prmR Ng SExt.none (geoCl anyGeometry)).s → ExportF KPx (IsBuiltE (prmR N SExt.none (geoCl anyGeometry)).s) → Pass KPx (IsBuiltE (prmR N SExt.none (geoCl anyGeometry)).s) (fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 (prmR Ng SExt.none (geoCl anyGeometry)).s K B f T w) → (∀ K B f T w Z Wt p0 t nch n xd c, Ng K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c) ∧ GoodO (w.D Z) nch xd) → MemberE (prmR N SExt.none (geoCl anyGeometry)).s := by
  intro p1 p2 p3 s1 s2 s3 s4 s5 s6 s7 s8 s9 pv t1 t2 t3 t4 t5 t6 t7 hL N Ng h3 mv mv' ex ps hN
  exact GlobalTheory.T.exists_member_of_construction_steps_secondPass p1 p2 p3 pv (prmR N SExt.none (geoCl anyGeometry)).s (prmR Ng SExt.none (geoCl anyGeometry)).s h3
    (GlobalTheory.T.level_three_to_four s1 s2 s3 s4 s5 s6 s7 s8 s9 pv hL (prmR N SExt.none (geoCl anyGeometry)) rfl mv)
    (GlobalTheory.AmbCrd.ambEx_of_rx _ rfl) (divEx_geoCl p1 p2 p3 _ _ _)
    (GlobalTheory.T.exists_thetaData_trueRowsColumns_allCompatible t1 t2 t3 t4 t5 t6 t7 _ (io_zero _ rfl)) ex ps
    (GlobalTheory.T.level_three_to_four s1 s2 s3 s4 s5 s6 s7 s8 s9 pv hL (prmR Ng SExt.none (geoCl anyGeometry)) rfl mv')
    (GlobalTheory.AmbCrd.ambEx_of_rx _ rfl) (divEx_geoCl p1 p2 p3 _ _ _)
    (GlobalTheory.T.exists_thetaData_trueRowsColumns_allCompatible t1 t2 t3 t4 t5 t6 t7 _ (io_zero _ rfl))
    (goodE_of_builtE hL N Ng SExt.none (geoCl anyGeometry) hN)

end GlobalTheory.Mem.Top.Closing
end
