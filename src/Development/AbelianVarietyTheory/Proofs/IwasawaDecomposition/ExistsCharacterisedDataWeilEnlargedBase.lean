module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealDatumPrerequisitesUpdateModels
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCopiesReferenceObjectsOverEnlargedBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharacterEqProductResidualCharactersEStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormGroupsModelsActionsMeasuresBasesCharacterise
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoefficientsAgreeEnlargedBaseStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBaseStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandraStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalDefiniteFormsLargerFieldCombinationSmall
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleHilbertModelDefiniteFormsEnlarged
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleRationalFormLiftsAlgebraicEnlarged
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleWeilDatumVectorPolynomialMapEnlarg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBaseStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinersAndLiftsExistAtChoices
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.WeilExt

theorem stepW_host_rank (p : WP) :
    StepW p fun _ B _ _ _ => ∀ X : Stages, X.B.toPre = B.toPre →
      HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV :=
  Step.of_evG (((evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).inter (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)).imp
    fun _ _ _ _ _ H _ _ _ hO _ _ _ _ _ X e => ⟨(H.2 X (e ▸ hO)).1, (H.1 X (e ▸ hO)).2⟩)

theorem isIdG_of_heq (X : Stages) {px : PreX X.B.toPre} {Pg Pg' : Finset (Pl X.toD7.host.E)} (e : Gc X.B px ≃* G0 Pg X.toD7.R.r)
    (e' : Gc X.B px ≃* G0 Pg' X.toD7.R.r) (hP : Pg = Pg') (h : HEq e e') (h' : IsPlacewiseIdentity X (px := px) e') : IsPlacewiseIdentity X (px := px) e := by
  subst hP
  obtain rfl := eq_of_heq h
  exact h'

theorem trans_eq_of_heq (X : Stages) {px : PreX X.B.toPre} {Pg Pg' : Finset (Pl X.toD7.host.E)} (e : Gc X.B px ≃* G0 Pg X.toD7.R.r)
    (e' : Gc X.B px ≃* G0 Pg' X.toD7.R.r) (c : G0 Pg X.toD7.R.r ≃* G0g X.toD7.nd) (c' : G0 Pg' X.toD7.R.r ≃* G0g X.toD7.nd)
    (hP : Pg = Pg') (h : HEq e e') (hc : HEq c c') : e.trans c = e'.trans c' := by
  subst hP
  obtain rfl := eq_of_heq h
  obtain rfl := eq_of_heq hc
  rfl

private theorem updM_preserves_invariants {D : D7} {G : Type} [Group G] [Fintype G]
    {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) {F : Face D A3.A} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    (hPre : R.toRealDat.Pre0 F) (hIn : R.IsInert) (hTup : R.IsTup)
    (hKeep : Keep (A3 := A3) R.toRealDat F cG)
    (HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG) :
    let R' : RealDat3 D A3 Ks :=
      ⟨updM R.toRealDat HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG,
        R.plI, R.SF, R.phs, R.lam3⟩
    R'.toRealDat.Pre0 F ∧ R'.IsInert ∧ R'.IsTup ∧ Keep (A3 := A3) R'.toRealDat F cG := by
  exact ⟨realDatum_prerequisites_update_models hPre HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG,
    ⟨hIn.tie, hIn.onto, hIn.hR, hIn.hL, hIn.SF⟩,
    ⟨hTup.mu_off, hTup.mu_used, hTup.mu_ne, hTup.mu_conj, hTup.mu_on⟩,
    ⟨hKeep.std, hKeep.signs, hKeep.frames, hKeep.beta, hKeep.prX, hKeep.grp, hKeep.psi, hKeep.guard,
      hKeep.valKs, hKeep.frameKs, hKeep.levKs⟩⟩

section

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL]
  {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}

theorem m_eq (hE : Enl0 B B') : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m :=
  show B'.toPre.R.m = B.toPre.R.m from congrArg (fun P => P.R.m) hE.1



theorem exists_rSide (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) (hE : Enl0 B B') (h : RSideW z Wt' R₀) :
    ∃ HV νV fdV ωP vP thF thG, RSide z Wt' (⟨updM R₀.toRealDat R₀.HX HV R₀.HE R₀.gE R₀.jX (fun _ _ => 0) R₀.νY R₀.fdY R₀.ν0 R₀.fd0
      R₀.νX R₀.fdX νV fdV ωP vP thF thG, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ :
      RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) := by
  have key := fun i' : Fin (w'.st Z').toD7.R.m => GlobalTheory.T.exists_copies_reference_objects_over_enlarged_base z Wt' R₀ hE h (Fin.cast (m_eq hE) i') i' rfl
  choose ω v H th g ν fd k using key
  refine ⟨fun i _ => H i, fun i _ => ν i, fun i _ => fd i, fun i _ => ω i, fun i _ => v i, fun i _ => th i, fun i _ => g i, ?_, ?_⟩
  · delta RSideW at h ⊢
    with_unfolding_all exact (h :)
  · intro i i' e
    have e' : i = Fin.cast (m_eq hE) i' := Fin.ext e
    subst e'
    exact (by with_unfolding_all exact (k i' :))

end



theorem exists_pins_rSide : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat ∧
        RSideW z {v | B'.places.resChar v ∈ T'.pl} R₀ →
        ∃ (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) cG' ∧
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R'.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R'.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R'.eG.trans cG') Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R'.mu R'.twPl ∧
        BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr R'.toRealDat ∧ R'.toRealDat.ExAt ∧ RSide z {v | B'.places.resChar v ∈ T'.pl} R') := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine (stepW_host_rank Pinned).trans (StepW.of_all ?_)
  intro K B' f' T' w' _ _ H B f T w hE hf _ hpx Z hX Wt z hG _ hFine hHolds Z' hX' hG' _ _ core' alg' _ _ _ _ _ _ _ _
  intro Xg tr₀ R₀ cG hyp
  obtain ⟨hLev, hId, hGood, hMu, hIdem, hPre, hIn, hTup, hAll, hKeep, hBrg, hSide⟩ := hyp
  letI := alg'
  generalize {v | B'.places.resChar v ∈ T'.pl} = Wt' at *
  have hHH := (H (w'.st Z') rfl).1
  have hn := (H (w.st Z) hE.1.symm).2
  obtain ⟨HV, νV, fdV, ωP, vP, thF, thG, hS⟩ := exists_rSide z Wt' R₀ hE hSide
  generalize hR₁ : (⟨updM R₀.toRealDat R₀.HX HV R₀.HE R₀.gE R₀.jX (fun _ _ => 0) R₀.νY R₀.fdY R₀.ν0 R₀.fd0
      R₀.νX R₀.fdX νV fdV ωP vP thF thG, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ :
      RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr₀) core'.Q.c.F) = R₁ at hS
  have move : ∃ cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd,
      LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R₁.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₁.eG ∧
      GoodSet (w'.st Z') (px := w'.px) (R₁.eG.trans cG₁) Xg ∧ MuOf (w'.st Z') w'.I T' Wt' R₁.mu R₁.twPl ∧
      R₁.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr₀).lv2 ∧ R₁.IsInert ∧ R₁.IsTup ∧ R₁.AllPlaces ∧
      Keep R₁.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr₀).lv2 cG₁ ∧
      BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr₀ R₁.toRealDat := by
    subst hR₁
    have hUpd := updM_preserves_invariants R₀ hPre hIn hTup hKeep R₀.HX HV R₀.HE R₀.gE
      R₀.jX (fun _ _ => 0) R₀.νY R₀.fdY R₀.ν0 R₀.fd0 R₀.νX R₀.fdX νV fdV ωP vP thF thG
    refine ⟨cG, ?_, ?_, ?_, ?_, hUpd.1, hUpd.2.1, hUpd.2.2.1, ?_, hUpd.2.2.2, ?_⟩
    · exact hLev
    · exact hId
    · exact hGood
    · exact hMu
    · exact hAll
    · delta BrgStd at hBrg ⊢
      exact hBrg
  clear hR₁ hLev hId hGood hMu hPre hIn hTup hAll hKeep hBrg hSide
  obtain ⟨cG₁, hLev, hId, hGood, hMu, hPre, hIn, hTup, hAll, hKeep, hBrg⟩ := move
  have hSide₁ := hS.1
  have hL := GlobalTheory.T.liftCharacters_agree_over_enlarged_base z Wt' R₁ hE hf hpx hLev
  have hI := GlobalTheory.T.goodIdempotent_coefficients_agree_enlarged_base z Wt' R₁ hE hf hpx hG hG' hSide₁ cG₁ hKeep
  have hz := ratAt_of_geo z.R z.F z.pins.char hFine.1 hn z.geo hFine.2.1 hHolds.unif
  obtain ⟨tr, R, cG', hPins, hEx, hLevEq, hEG, hCG, hmu, htw, hBrg', hS', hSame⟩ :=
    charW_keep (w'.st Z') w'.px w'.I hX' (usedOf w'.I T' Wt') Xg tr₀ core'.Q.c.F R₁ cG₁ (GlobalTheory.T.linksAnalyticHypotheses_of_weilRep_harishChandra h5 h6 h7 h3 _) hIdem
      (fun R hP hc ht => GlobalTheory.ExAtAssembly.exAt_holds h1 h2 h3 h4 _ _ _ _ _ _ R hP.1.lev hP.1.fam hP.2 hP.1.record hHH hc ht)
      (fun R => RSideW z Wt' (⟨R, R₁.plI, R₁.SF, R₁.phs, R₁.lam3⟩ :
        RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr₀) core'.Q.c.F))
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s => by
        delta RSideW at s ⊢
        with_unfolding_all exact (s :))
      (fun _ _ _ _ _ _ _ _ _ _ _ _ s => by
        delta RSideW at s ⊢
        with_unfolding_all exact (s :))
      (fun _ _ _ s => by
        delta RSideW at s ⊢
        with_unfolding_all exact (s :))
      (by with_unfolding_all exact (hSide₁ :)) hPre hIn hTup hAll hKeep hBrg
      (GlobalTheory.T.finiteGroupCharacter_eq_product_residualCharacters_enlarged z Wt' R₁ hE hpx hSide₁ hL) (GlobalTheory.T.modW_of_rSideW z Wt' R₁ hE hpx hSide₁) (GlobalTheory.T.referenceTuple_weilDatum_vector_polynomialMap_enlarged z Wt' R₁ hE hFine.1 hS hL)
      (GlobalTheory.T.referenceTuple_hilbertModel_definiteForms_enlarged z Wt' R₁ hE hPre hS hL) (GlobalTheory.T.thetaLift_at_reference_tuple_over_enlarged_base z Wt' R₁ hE hpx hFine.1 hS hI)
      (GlobalTheory.T.referenceTuple_rationalForm_lifts_algebraic_enlarged z Wt' R₁ hE hS (GlobalTheory.T.rationalDefiniteForms_largerField_combination_smallerField z Wt' R₁ hE hf hpx hSide₁) hz)
  have hPg : R.Pg = R₁.Pg := congrArg LevCh.Pg hLevEq
  refine ⟨tr, R, cG', hPins, hLevEq ▸ hLev, isIdG_of_heq _ R.eG R₁.eG hPg hEG hId, ?_, ?_, hBrg', hEx, ?_, fun i i' e => ?_⟩
  · rw [trans_eq_of_heq _ R.eG R₁.eG cG' cG₁ hPg hEG hCG]; exact hGood
  · rw [hmu, htw]; exact hMu
  · delta RSideW at hS' ⊢
    with_unfolding_all exact (hS' :)
  · -- Project the conjuncts directly to avoid large eliminators in this dependent goal.
    have hRef := hS.2 i i' e
    have hSameAt := hSame i'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (heq_of_eq hSameAt.1).trans hRef.1
    · exact (heq_of_eq hSameAt.2.1).trans hRef.2.1
    · exact hSameAt.2.2.1.trans hRef.2.2.1
    · exact hSameAt.2.2.2.1.trans hRef.2.2.2.1
    · exact hSameAt.2.2.2.2.1.trans hRef.2.2.2.2.1
    · exact (heq_of_eq hSameAt.2.2.2.2.2.1).trans hRef.2.2.2.2.2.1
    · exact (heq_of_eq hSameAt.2.2.2.2.2.2).trans hRef.2.2.2.2.2.2

end GlobalTheory.Mem.R3.Rw.WeilExt

end
