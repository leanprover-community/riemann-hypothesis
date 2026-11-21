import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeightSetResidueCharacteristic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberBuiltLinkedGeometricStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultQ
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HypN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AllStagesAtMemberOfSpecializations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteLevelAndSecondStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteLevelAndSecond
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MinimalKtypeOfLocalComponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StatementAOfPointCompat
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RayPrimeHostIntegral
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowDepthOfPrimitive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclOfGrpStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultiplicityBoundOfLocalComponents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelComparisonChoicesExistAtAllPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValPosIffMemExample
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RawPackEqPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberBuiltLinkedGeometric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Lv3StageMovesSpectralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Lv3StageMovesSpectral
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerUpStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SlotStageMovesGeometricStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PositionStageMovesGeometric
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutomorphyOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsSPackIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelThreeToFourStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelThreeToFour
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PublishedInputsImplyConclusion
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExBLIsLinkedPrmRStatement

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick avoidPlaces subset_avoidPlaces)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.Up
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
theorem sFino_of_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cDep : ℝ} (h : _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep) : _root_.GlobalTheory.HeightCounting.Up.SpectralFiniteness hL cDep := by
  refine StepW.trans h (StepW.of_all fun K B f T w _ _ H P x l S Γ hl => ?_)
  obtain ⟨Z, v, h1, h2⟩ := H P x l S Γ hl.1
  exact ⟨Z, { g := v.g, coh := v.coh, Wt := v.Wt, p0 := v.p0, what₂ := v.what₂, rx := v.rx, nch := v.nch, n := v.n, xd := v.xd,
              chiT := v.chiT, nx := ⟨v.nx.1, v.nx.2, ⟨P, x, l, hl, h1, h2⟩⟩ }, h1, h2⟩
theorem exists_pre_point_with_henselian_level {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cDep : ℝ} {S : SExt} {Γ : GeoP} {Z : w.Lt} {c : V4.Core K (w.st Z) f T}
    (b : Built (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s K w Z c) (e : ExportAt (w.st Z).toD7 c.O.nch c.O.xd) :
    ∃ (P : Pre2 K w) (x : St P) (_ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x), (ListSt cDep x ∧ SatU P) ∧ ∀ A, Nonempty (Seed (Dof x) A) := by
  obtain ⟨P, x, l, hl, hW, hk⟩ := b.nx.2.2.down
  have key := (TupTieW.tupTied_of_muIsW (w.st Z) f T c.Wt c.xi c.mu).1
  refine ⟨P, x, l, hl, GlobalTheory.HeightCounting.Up.nonempty_seed_of_kept (Dof x) (w.st Z).toD7 l.c.ch c.O.nch c.O.xd hk rfl (fun v v₀ hv ht => ?_) l.c.side.nct
    l.c.side.choice.twI_conj ?_ B.coeffGaloisSubfield_isGalois (twistedPlaceIndex_mem_firstPair_of_compatibleChoice (w.st Z).toD7 c.O.nch c.nch_tie B.coeffGaloisSubfield_isGalois) e b.nx.2.1.1.1.xd⟩
  · obtain rfl : v = v₀ := eq_of_heq hv
    exact (key v).2 (hW ▸ (twisted_st x v).1 ht)
  · exact (TupTieW.tupTied_of_muIsW (w.st x.o.Z) f T P.Wt w.I.xi (muIsW_st x)).2.1.subset fun v hv => (twisted_st x v).1 hv
end GlobalTheory.HeightCounting.Up
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Bare
open GlobalTheory.MemN GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.Mem.TypePl Polynomial
attribute [local instance] GlobalTheory.Mem.Top.factType
variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
end GlobalTheory.Mem.R3.Rw.Bare
namespace GlobalTheory.HeightCounting.Up
open Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice GlobalTheory.Mem.R3.Rw.Bare
set_option maxHeartbeats 4000000 in
theorem minimal_ktype_of_local_components_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DiscreteSeriesExists → BareK := by
  intro hP hD
  refine StepW.of_all fun K B' f' T' w' hO _ _ P' X f hB hf hg => ?_
  obtain ⟨B₀, C₀, W₀, V₀, S₀, N₀, G₀⟩ := X
  cases B'
  cases B₀
  dsimp only at hB
  subst hB
  obtain rfl := eq_of_heq hf
  obtain ⟨N, hE, hN, hN', hL, h1, h2, h3, h4, h5, h6⟩ := exists_bare_over P' N₀.nd N₀.naut hg.pl N₀.toLocStage
  obtain ⟨V, hV, -, -, hη, -, hB⟩ := exists_divStage_of_pk _ w'.C (Gc _ w'.px) P'.q.p P'.q.e P'.q.W₀ P'.q.n
    (fun _ _ => 0) (fun _ _ => le_rfl) (frames_unit P'.q.t) (fun u => ((w'.C.fm u).lat 0).L) (fun _ => 0)
    (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨S, -⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K _ w'.C (P'.q.W (fun _ _ => 0) fun _ _ => le_rfl) P'.Z₀.G.cd hO
    (GlobalTheory.Mem.Df.cols_pos w'.I w'.ok w'.pins w'.l P'.hX) (rows_le P'.q.t)
  obtain ⟨x, hx⟩ := GlobalTheory.T.fittingLaterStages_row_is_constructionState GlobalTheory.weilRepresentationUnitaryPair hD hP.hc hP.decay K _ _ T' w' P' ⟨_, _, V, S, N, P'.Z₀.G⟩
    ⟨hV, hN, (hN' V S P'.Z₀.G).1, (hN' V S P'.Z₀.G).2⟩ rfl hη (fun hr => hB hr)
  have hDx : Dof x = (w'.st (RowPk.Over.Z (q := P'.q) ⟨_, _, V, S, N, P'.Z₀.G⟩)).toD7 := by
    unfold Dof
    rw [hx]
  have hE' : IsEmpty x.o.N.nd.Loc := by
    rw [hx]
    exact hE
  refine ⟨x, hE', ?_⟩
  rw [hDx]
  exact ⟨⟨rfl, HEq.rfl, congrArg LocStage.loc hL.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm⟩, h6.symm⟩
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bareK_of_discreteSeriesExists : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DiscreteSeriesExists → BareK := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.minimal_ktype_of_local_components_alt | exact _root_.GlobalTheory.HeightCounting.Up.minimal_ktype_of_local_components_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.minimal_ktype_of_local_components_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
noncomputable section
namespace GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
theorem satake_parameter_of_prime_to_level_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → PhtCmp → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.FirstStageExists hL := by
  intro hP hC hL
  have hE := _root_.GlobalTheory.T.isRayPrime_g_and_integral_range hP
  have hR := _root_.GlobalTheory.T.depth_of_repOf_of_inputs hP
  have hA := _root_.GlobalTheory.T.types_true_of_ray_class_alt hL hP.what₂.fin hP.what₂.berger hP.greenC hP.what₂.art hP.ray hP.what₂.cheb
  unfold _root_.GlobalTheory.HeightCounting.Up.FirstStageExists AllSt
  refine StepW.trans (StepW.and hE hR) (StepW.of_all ?_)
  intro K B f T w _ _ hq P x hLoc
  obtain ⟨hEl, hRw⟩ := hq
  obtain ⟨hElem, -, -, h, jE, hfr, hray⟩ := hEl P x
  have e1 : (cfOf x).P = f.P := by
    show w.I.C.P = f.P
    rw [w.C_eq]
  have e2 : (cfOf x).W = f.W := by
    show w.I.C.W = f.W
    rw [w.C_eq]
  have hTy : TypesTrue (Dof x).ntypes (cfOf x).P (cfOf x).W := by
    rw [e1, e2]
    exact x.fits.grp
  obtain ⟨L, hZ, hη, A, hcg, hau, hrow, hTT, hPlG, hplGw, hcA, hcM, hζ, hloc, hO1, hO2, hO3, hO4, hlab⟩ :=
    hA (Dof x) hLoc (cfOf x) jE (repOf x.r.Y) hElem.int hTy (hRw P x) hray
  have hG : GrpTrue (nOfLay x L hZ hη) f := by
    show TypesTrue L.ntypes f.P f.W
    rw [← e1, ← e2]
    exact hTT
  obtain ⟨hGA, hCen⟩ := GlobalTheory.T.heckeGaloisStage_fits_of_same_centre_actions x (nOfLay x L hZ hη) hG hPlG hplGw hcA hcM
  obtain ⟨x', hx', hrep⟩ := GlobalTheory.T.exists_transported_state_heckeGaloisStage x (nOfLay x L hZ hη) hG hGA hCen
  obtain ⟨Pq, hPq1, hPq2⟩ := exists_pq_sel B w.I w.ok
  have hEl' := hEl P x'
  have hRw' := hRw P x'
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at hx'
  subst hx'
  obtain ⟨fr, hfrj⟩ := omFrame_exists_with_jE (setK (Dof x) L hZ hη) jE
  obtain ⟨Wd, hWd⟩ := PhtExt.exists_phtOn_all hC (setK (Dof x) L hZ hη) fr A.wdT A.wd
  let A' : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding (setK (Dof x) L hZ hη) (cfK L hZ hη (cfOf x)) jE := { A with wd := Wd }
  have e := eq_of_heq hrep
  obtain ⟨cg⟩ := hcg
  refine ⟨⟨⟨x.o.η, x.o.hη, x.o.V, x.o.S, nOfLay x L hZ hη, x.o.G⟩, fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩, ⟨⟨⟨⟨h.fr, h.jLL, h.embLL⟩, jE, hfr, A', cg, hau, ?_, fr, hfrj, hWd, hRw', hEl'.1, hEl'.2.1, hlab, hζ, hEl'.2.2.1⟩,
    Pq, hPq1, hPq2⟩⟩, ⟨⟨rfl, HEq.rfl, hloc.symm, hO1.symm, hO2.symm, hO3.symm, hO4.symm, heq_of_eq hPlG.symm⟩, hplGw.symm⟩⟩
  rw [e]
  exact hrow
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stageAExists_of_inputs_phtCmp : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → PhtCmp → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.FirstStageExists hL := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.satake_parameter_of_prime_to_level_alt | exact _root_.GlobalTheory.HeightCounting.Up.satake_parameter_of_prime_to_level_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.satake_parameter_of_prime_to_level_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.Top.TwChar
theorem exists_twisted_cohomology_class_lift_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (X : Stages) (f : Fr X.B.toPre) (pl : Finset ℕ) (A : X.toD7.ntw.Tw → Finset (PlE X.toD7.host)) (σ : Seed X.toD7 A) (Av : ℕ → Finset ℕ), (∀ v, TwistedAt X.toD7 v → X.B.places.resChar v ∈ pl) → (∀ v v', OverOne X.toD7 v v' → TwistedAt X.toD7 v → TwistedAt X.toD7 v') → (∀ i (p : ℕ), p ∈ offSet X.B.toPre ∨ p ∈ Av (X.toD7.ntw.l i) → p.Prime → placesOver X.toD7.host.E p ⊆ ↑(A i)) → ∀ S₂ : ∀ P : Pre, Fr P → Set (HChar P.host.E) → Finset ℂ, (∀ P g Ξ, ∀ z ∈ S₂ P g Ξ, IsAlgebraic ℚ z) → ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B') (h : Enl X.B B'), HEq f' f ∧ T'.pl = pl ∧ T'.Avoids Av ∧ (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧ Coh B' T' ∧ TwFrom X σ h T' := by
  intro hP X f pl A σ Av hpl hsat hA S₂ h₂
  obtain ⟨art, ha⟩ := hP.what₂.art X.toD7.host.E X.toD7.nd.Om
  obtain ⟨h1, T₁, e1, hav, hT, hT', hS⟩ := exists_twDat_stagesOn X f pl {v | TwistedAt X.toD7 v} hpl
    (twistedAt_conj X.toD7) σ.s (fun w => let ⟨_, hb⟩ := σ.reads w; hb.l_eq) (fun w _ => σ.conj w) art ha A σ.Q σ.k σ.ψ
    (fun i => rootIsoAt X.toD7 i (σ.k i)) Av hA (fun w hw => σ.psiOk hw)
  obtain ⟨B', h, a, b, e⟩ := hS (S₂ X.B.toPre f (T₁.set f)) (h₂ _ _ _)
  have e2 : ∀ (P : Pre) (_ : P = X.B.toPre) (g : Fr P) (Ξ : Set (HChar P.host.E)), HEq g f → HEq Ξ (T₁.set f) →
      S₂ P g Ξ = S₂ X.B.toPre f (T₁.set f) := by
    intro P eP g Ξ h1 h2
    subst eP
    rw [eq_of_heq h1, eq_of_heq h2]
  refine ⟨B', tr h.1 Fr f, pull h T₁, h, tr_heq _ _ _, e1, avoids_pull h hav, ?_, ⟨fun v v' hv => ?_, fun v => ?_⟩,
    b, fun v => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · rw [e2 _ h.1 _ _ (tr_heq _ _ _) e]
    exact a
  · have ho := overOne_plUnder X h v v' hv
    have key : T₁.psi (plUnder h v) = T₁.psi (plUnder h v') ∧ T₁.Q (plUnder h v) = T₁.Q (plUnder h v') ∧
        T₁.k (plUnder h v) = T₁.k (plUnder h v') := by
      by_cases hw : TwistedAt X.toD7 (plUnder h v)
      · have hw' := hsat _ _ ho hw
        obtain ⟨x, y, z⟩ := hT _ hw
        obtain ⟨x', y', z'⟩ := hT _ hw'
        rw [σ.same _ _ hw hw' ho] at x' y' z'
        exact ⟨x.trans x'.symm, y.trans y'.symm, z.trans z'.symm⟩
      · have hw' : ¬ TwistedAt X.toD7 (plUnder h v') := fun h' => hw (hsat _ _ (fun x => (ho x).symm) h')
        obtain ⟨x, y, z⟩ := hT' _ hw
        obtain ⟨x', y', z'⟩ := hT' _ hw'
        exact ⟨x.trans x'.symm, y.trans y'.symm, z.trans z'.symm⟩
    exact ⟨congrArg (tr h.1 (fun P => Finset (HeightOneSpectrum (𝓞 P.host.E)))) key.2.1, key.2.2,
      congrArg (tr h.1 (fun P => HChar P.host.E)) key.1⟩
  · have hn : B'.places.resChar v ^ (pull h T₁).k v ≠ 0 := pow_ne_zero _ (B'.places.resChar_prime v).ne_zero
    have hz := Complex.isPrimitiveRoot_exp _ hn
    obtain ⟨x, hx⟩ := b v _ hz.pow_eq_one
    exact ⟨x, IsPrimitiveRoot.of_map_of_injective (hx ▸ hz) B'.embLL.injective⟩
  · obtain ⟨x, y, z⟩ := hT (plUnder h v) hw
    exact ⟨(tr_heq h.1 (fun P => Finset (HeightOneSpectrum (𝓞 P.host.E))) _).trans (heq_of_eq y), z, _, _,
      (h1 _ (σ.psiOk hw)).2.1, (tr_heq h.1 (fun P => HChar P.host.E) _).trans (heq_of_eq x)⟩
  · exact (congrArg (tr h.1 (fun P => HChar P.host.E)) (hT' _ hw).1).trans (tr_one _)
end GlobalTheory.HeightCounting.Up
end
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Rigid
theorem rigid_raw_packet_eq_pow_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D₁ D₂ : D7) (p : TwPack D₁) (A : Finset (PlE D₁.host)) (ι : GlobalTheory.Mem.Top.TwChar.RootIso D₁ p.1 p.2.2.1) (χ : HChar D₁.host.E) (cf : CharFrame D₂) (C : NChoice D₂) (tp : TupTied D₂ cf C) (v : D₂.what₂.places.Pl), SameExport D₁ D₂ → BlochKatoReduction.Gen.PsiOk p.1 A p.2.1 p.2.2.1 p.2.2.2 → GlobalTheory.Mem.Top.TwChar.FrobPick p.1 p.2.1 p.2.2.1 p.2.2.2 ι χ → PsiChoiceCompatible D₂ cf C tp → TwistedAt D₂ v → HEq (C.twI v) p.1 → HEq (C.Q v) p.2.1 → C.k' v = p.2.2.1 → HEq (tp.psi v) χ → (∀ z : ℂ, z ^ D₂.what₂.places.resChar v ^ C.k' v = 1 → ∃ x : D₂.what₂.LL, D₂.what₂.embLL x = z) → ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l p.1) ∧ HEq (rawPack C v) (GlobalTheory.HeightCounting.twPackPow D₁ a p) := by
  intro hc D₁ D₂ p A ι χ cf C tp v h hO hF hT htw hi hQ hk hχ hL
  obtain ⟨ψ₂, ι₂, A₂, hO₂, hF₂, hl, hpow⟩ := transfer h p A ι χ hO hF (C.twI v) (C.Q v) (C.k' v) (tp.psi v) hi hQ hk hχ
  obtain ⟨a, ha, hψ⟩ := pow_of_tied hc.cheb cf C tp v ψ₂ ι₂ hF₂ hT htw hO₂.2.2.1 hL
  refine ⟨a, by rw [Int.natAbs_natCast, ← hl]; exact ha, ?_⟩
  have e : rawPack C v = (⟨C.twI v, C.Q v, C.k' v, ψ₂ ^ (a : ℤ)⟩ : TwPack D₂) := by
    rw [zpow_natCast, ← hψ]
    rfl
  rw [e]
  exact hpow a
end GlobalTheory.HeightCounting.Rigid
end
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick avoidPlaces subset_avoidPlaces)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.Up
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
theorem goodO_of_alt_alt (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {B' : Base} {f' : Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}
    (h : Enl B B') {P : Pre2 K w} (x : St P) {A} (σ : Seed (Dof x) A) (hA : ∀ i, avD (Dof x) (avDesign (Dof x)) i ⊆ A i)
    (hT : TwFrom (w.st x.o.Z) σ h T') {P' : Pre2 K w'} (hW : ∀ v', plUnder h v' ∈ P.Wt ↔ v' ∈ P'.Wt) {y : St P'} (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL y)
    (hc : Carried (Dof x) (Dof y)) (hs : ∀ v', HEq (l.c.ch.twI v') (σ.s (plUnder h v'))) {Z : w'.Lt}
    {C : NChoice (w'.st Z).toD7} {xd : ThData (w'.st Z).toD7} (hk : Kept l.c.ch C) (hx : XdAll xd)
    (hZ : ∀ v', TwistedAt (w'.st Z).toD7 v' → v' ∈ P'.Wt) : GoodO (w'.st Z).toD7 C xd := by
  classical
  refine GlobalTheory.T.goodTwist_of_seed_character_powers (Dof x) (Dof y) (w'.st Z).toD7 A σ l.c.ch C xd (plUnder h) hc.exp hk (avPrimes_st _ _) rfl hx hA
    fun v₂ v₃ hv ht => ?_
  obtain rfl : v₂ = v₃ := eq_of_heq hv
  have h1 := hZ v₂ ht
  have h2 : TwistedAt (Dof x) (plUnder h v₂) := (twisted_st x _).2 ((hW _).2 h1)
  have h3 : TwistedAt (Dof y) v₂ := (twisted_st y _).2 h1
  obtain ⟨hQ, hk', ι, χ, hF, hχ⟩ := (hT.2 v₂).1 h2
  have hg := (((σ.good _ h2).2 1 (by simp)).1)
  rw [zpow_one] at hg
  have e1 : l.c.ch.Q v₂ = T'.Q v₂ := (congrFun l.c.Q_eq v₂).trans (if_pos h1)
  have e2 : l.c.ch.k' v₂ = T'.k v₂ := l.c.k_eq v₂ h3
  refine ⟨h2, _root_.GlobalTheory.HeightCounting.Rigid.rigid_raw_packet_eq_pow_alt hP (Dof x) (Dof y) (σ.pack (plUnder h v₂)) _ ι χ (cfOf y) l.c.ch l.c.tp v₂ hc.exp hg hF l.c.side.psi h3
    (hs v₂) ((heq_of_eq e1).trans hQ) (e2.trans hk') ((heq_of_eq (congrFun l.c.psi_eq v₂)).trans hχ) fun z hz => ?_⟩
  rw [e2] at hz
  exact hT.1 v₂ z hz
theorem has3_of_carried_levelB2 {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cDep : ℝ} (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (S : SExt) (Γ : GeoP) {B' : Base} {f' : Fr B'.toPre}
    {T' : TwDat B'} {w' : ColW B' f' T'} (h : Enl B B') {P : Pre2 K w} (x : St P) {A} (σ : Seed (Dof x) A)
    (hA : ∀ i, avD (Dof x) (avDesign (Dof x)) i ⊆ A i) (hT : TwFrom (w.st x.o.Z) σ h T') {P' : Pre2 K w'}
    (hW : ∀ v', plUnder h v' ∈ P.Wt ↔ v' ∈ P'.Wt) {y : St P'} (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL y) (hc : Carried (Dof x) (Dof y)) (hl : ListSt cDep y ∧ SatU P')
    (ck : ∀ s : B'.places.Pl → (Dof y).ntw.Tw, (∀ v, ∃ b, ReadsAt (D := Dof y) (s v) b v) → (∀ v, s (B'.places.conj v) = s v) →
      ∃ c : _root_.GlobalTheory.HeightCounting.HeightCountingCharacterData l.mt l.b T'.k T'.psi, c.ch.twI = s)
    (fin : ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL y) (S : SExt) (Γ : GeoP), (ListSt cDep y ∧ SatU P') →
      ∃ (Z : w'.Lt) (v : Lv3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s K w' Z), v.Wt = P'.Wt ∧ Kept l.c.ch v.nch) :
    Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep) S Γ).s K B' f' T' w' := by
  have eT : (Dof x).ntw.Tw = (Dof y).ntw.Tw := (same_basic hc.exp.gal hc.exp.set hc.exp.frm).1
  obtain ⟨c, hs⟩ := ck (fun v' => cast eT (σ.s (plUnder h v')))
    (fun v' => (σ.reads (plUnder h v')).imp fun b hb =>
      GlobalTheory.HeightCounting.Up.readsAt_of_plUnder (w.st x.o.Z) (w'.st y.o.Z) h hc v' _ _ b (cast_heq eT _).symm hb)
    (fun v' => congrArg (cast eT) ((congrArg σ.s (TwChar.plUnder_conj h v')).trans (σ.conj _)))
  obtain ⟨Z, v, h1, h2⟩ := fin { toStrictHenselianAcyclic := l, c := c } S Γ hl
  have hg : GoodO (w'.st Z).toD7 v.nch v.xd :=
    _root_.GlobalTheory.HeightCounting.Up.goodO_of_alt_alt hP h x σ hA hT hW { toStrictHenselianAcyclic := l, c := c } hc (fun v' => (heq_of_eq (congrFun hs v')).trans (cast_heq eT _)) h2
      v.nx.2.1.1.1.xd fun v' hv' => h1 ▸ ((TupTieW.tupTied_of_muIsW (w'.st Z) f' T' v.Wt w'.I.xi v.what₂.mu).1 v').1 hv'
  exact ⟨Z, ⟨{ g := v.g, coh := v.coh, Wt := v.Wt, p0 := v.p0, what₂ := v.what₂, rx := v.rx, nch := v.nch, n := v.n, xd := v.xd,
               chiT := v.chiT, nx := ⟨v.nx.1, v.nx.2, ⟨hg⟩⟩ }⟩⟩
theorem secondNo_of_sMt_sRat_sCusp_sFinl (hCo : GlobalTheory.Published.DiscreteSeriesCover) (hCW : GlobalTheory.Published.CasselmanWallach) (hHM : GlobalTheory.Published.HarishChandraModules) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hS : SerN) (hD : DatExt) (hH : WeightCaseCondition) (hds : GlobalTheory.Published.DiscreteSeriesExists)
    (hc : PhtCmp) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hMt : SMt) (hRat : _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL) (hCu : _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL) {cDep : ℝ}
    (hF : _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep) : _root_.GlobalTheory.HeightCounting.Up.SecondNonvanishing hL cDep := by
  classical
  intro S Γ
  have h3 := GlobalTheory.Mem.R3.Rw.Second.exists_ext_twisted_places hP.greenC hD
  have h4 := (GlobalTheory.T.constructionStartingChoices_of_fine_adelicData GlobalTheory.weilRepresentationUnitaryPair hds hP.hc hP.decay hH).and ((_root_.GlobalTheory.T.bareK_of_discreteSeriesExists hP hds).and ((_root_.GlobalTheory.T.stageAExists_of_inputs_phtCmp hP hc hL).and
    (hMt.and (hRat.and (hCu.and ((_root_.GlobalTheory.T.moveToBase_of_inputs_serN hP hS hL).and ((_root_.GlobalTheory.T.stageCExists_of_casselmanWallach hCo hCW hHM hP hS hL).and (_root_.GlobalTheory.HeightCounting.Up.sFino_of_alt hF))))))))
  refine pass_of (p := fun _ _ _ _ => True) (Step.of_all fun _ _ _ _ _ _ _ h => h) (Step.and h3 h4)
    (EvG.imp GlobalTheory.Mem.Top.ReW.extend_pinned fun K _ _ _ _ hw2 => ?_)
  intro B f T hO hKP hT _ C W V S' N G c₀ hQ hE A S₂ hS₂
  obtain ⟨w, Z, c, ⟨b, -⟩, e⟩ := exists_of_position hQ hE
  have hSt : Start K B f T w := ⟨⟨b.pin⟩, Or.inl hT, b.coh⟩
  obtain ⟨P, x, l, hl, hσ⟩ := _root_.GlobalTheory.HeightCounting.Up.exists_pre_point_with_henselian_level b e
  obtain ⟨A₁, S₁, a₁, hw'⟩ := hw2 B f T w hO ⟨b.pin⟩
  obtain ⟨σ⟩ := hσ fun i => avD (Dof x) (avDesign (Dof x)) i ∪ avoidPlaces B.toPre (A ((Dof x).ntw.l i) ∪ A₁ ((Dof x).ntw.l i))
  obtain ⟨B', f', T', h, hf, hpl, hAv, hS', hCoh, hTw⟩ := _root_.GlobalTheory.HeightCounting.Up.exists_twisted_cohomology_class_lift_alt hP (w.st x.o.Z) f T.pl _ σ (fun p => A p ∪ A₁ p)
    (fun v hv => P.sub v ((twisted_st x v).1 hv))
    (fun v v' ho hv => (twisted_st x v').2 (hl.2 hT v v' ho ((twisted_st x v).1 hv)))
    (fun i p hp hp' v hv => Finset.mem_coe.2 (Finset.mem_union_right _ (subset_avoidPlaces B.toPre _ hp hp' hv)))
    (fun P g Ξ => S₂ P g Ξ ∪ S₁ P g Ξ) (fun P g Ξ z hz => (Finset.mem_union.1 hz).elim (hS₂ P g Ξ z) (a₁ P g Ξ z))
  obtain ⟨w', hPin, epx, esel, eJ, eδ⟩ := hw' B' f' T' h hf (fun v u hu hA => hAv v u hu (Finset.mem_union_right _ hA))
    fun z hz => hS' z (Finset.mem_union_right _ hz)
  have eP : B'.toPre = B.toPre := h.1
  refine ⟨B', f', T', h, hf, hpl, fun v u hu hA => hAv v u hu (Finset.mem_union_left _ hA),
    fun z hz => hS' z (Finset.mem_union_left _ hz), ⟨⟨w'.δ, w'.exact⟩, eP ▸ hKP.2⟩, fun hq => ?_⟩
  obtain ⟨Z', hX', z', g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hq.1 w' hPin B f T w h hf ⟨b.pin⟩ epx hpl P.Z₀ P.hX P.Wt P.z P.grp
    P.grpAt P.kap ⟨P.exAt, P.inGeo, P.core, P.std⟩ (HoldsL.of_holds P.intersectionNumber_baseChange) P.exact P.sub
    (fun Z' v' hv => (hTw.2 v').2 fun ht => hv _ (below_plUnder h P.Z₀ Z' v') ((twisted_st x _).1 ht))
  have hSt' : Start K B' f' T' w' :=
    ⟨hPin, Or.inr ⟨Z', hX', z', g1, g2, g3, g4, g5.1, g5.2.1, g5.2.2.1, g5.2.2.2, g6, g7⟩, hCoh⟩
  obtain ⟨pre, bare, sa, mt, rat, cu, mv, ck, fin⟩ := hq.2 w' hSt'
  obtain ⟨P', -, eW, g10⟩ := pre Z' hX' z' g1 g2 g3 g4 g5 g6 g7
  have hExt : Ext P.z P'.z := GlobalTheory.T.standardReading_transport_and_extension_trans.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h (enl_refl B') g8 g10
  obtain ⟨x0, hE0, s0⟩ := bare P' (w.st x.o.Z) f eP hf x.fits.grp
  obtain ⟨x1, ⟨la⟩, s1⟩ := sa P' x0 hE0
  obtain ⟨imt⟩ := mt P' x1
  obtain ⟨irat⟩ := rat P' x1 la
  obtain ⟨y, ⟨l2⟩, hcar, hlist⟩ := mv B f T w h hf hSt epx esel eJ eδ P x l.toStrictHenselianAcyclic P' hExt x1
    { toLA := la, mt := imt, rat := irat, cusp := cu P' x1 la } (s0.trans s1)
  have hWt : ∀ v', plUnder h v' ∈ P.Wt ↔ v' ∈ P'.Wt := fun v' => eW ▸ g9 _ v' (below_plUnder h P.Z₀ Z' v')
  exact ⟨w', hSt', _root_.GlobalTheory.HeightCounting.Up.has3_of_carried_levelB2 hP S Γ h x σ (fun i => Finset.subset_union_left) hTw hWt l2 hcar
    ⟨hlist cDep hl.1, fun _ v₁ v₂ ho hv => (hWt v₂).1 (hl.2 hT _ _ (overOne_plUnder_of h P.Z₀ P'.Z₀ ho) ((hWt v₁).2 hv))⟩
    (ck P' y l2) (fin P' y)⟩
theorem sFino_and_secondNo_of_rat_cusp_finl : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → DatExt → WeightCaseCondition → GlobalTheory.Published.DiscreteSeriesExists → PhtCmp →
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, SMt → _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL → _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL → ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep → _root_.GlobalTheory.HeightCounting.Up.SpectralFiniteness hL cDep ∧ _root_.GlobalTheory.HeightCounting.Up.SecondNonvanishing hL cDep :=
  fun hCo hCW hHM hP hS hD hH hds hc _ hMt hRat hCu _ hF => ⟨_root_.GlobalTheory.HeightCounting.Up.sFino_of_alt hF, _root_.GlobalTheory.HeightCounting.Up.secondNo_of_sMt_sRat_sCusp_sFinl hCo hCW hHM hP hS hD hH hds hc hMt hRat hCu hF⟩
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sFino_and_secondNo_of_sFinl' : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → DatExt → WeightCaseCondition → GlobalTheory.Published.DiscreteSeriesExists → PhtCmp → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, SMt → _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL → _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL → ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep → _root_.GlobalTheory.HeightCounting.Up.SpectralFiniteness hL cDep ∧ _root_.GlobalTheory.HeightCounting.Up.SecondNonvanishing hL cDep := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.sFino_and_secondNo_of_rat_cusp_finl | exact _root_.GlobalTheory.HeightCounting.Up.sFino_and_secondNo_of_rat_cusp_finl | (intros; apply _root_.GlobalTheory.HeightCounting.Up.sFino_and_secondNo_of_rat_cusp_finl <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.SRe
set_option maxHeartbeats 2000000
namespace GlobalTheory.Mem.Top.Bl
theorem has3_neo_of_localLanglands_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (hB : ExistsUnlocalizedSaturatedState) (hA : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevelExists hL) (hMt : SMt) (hRat : _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL)
    (hCu : _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL) (hB0 : _root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep) (hB1 : _root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep) (hB2 : _root_.GlobalTheory.HeightCounting.Up.ModuliPointsExistList' hL cDep) (hC : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL) (hFin : _root_.GlobalTheory.HeightCounting.Up.SpectralFiniteness hL cDep)
    (S : SExt) (Γ : GeoP) : StepW Start (Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s) := by
  have h := StepW.and hB (hA.and (hMt.and (hRat.and (hCu.and (hB0.and (hB1.and (hB2.and (hC.and hFin))))))))
  refine h.trans (StepW.of_all ?_)
  intro K B f T w _ _ H
  obtain ⟨⟨P, x, sat, hLoc, -⟩, a, mt, rat, cu, b0, b1, b2, c, fin⟩ := H
  obtain ⟨x1, ⟨la⟩, -⟩ := a P x hLoc
  obtain ⟨imt⟩ := mt P x1
  obtain ⟨irat⟩ := rat P x1 la
  have li : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x1 := { toLA := la, mt := imt, rat := irat, cusp := cu P x1 la }
  obtain ⟨x2, ⟨l0⟩, p2⟩ := b0 P x1 li
  obtain ⟨x3, ⟨l1⟩, p3⟩ := b1 P x2 l0
  obtain ⟨x4, ⟨l2⟩, p4⟩ := b2 P x3 l1
  obtain ⟨sc⟩ := c P x4 l2
  obtain ⟨Z, v, -, -⟩ := fin P x4 { toStrictHenselianAcyclic := l2, c := sc } S Γ ⟨p4 (p3 p2), sat⟩
  exact ⟨Z, ⟨v⟩⟩
end GlobalTheory.Mem.Top.Bl
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
namespace GlobalTheory.HeightCounting.Up
theorem org_of_kept_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cDep : ℝ} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {D D' : D7} {Wt : Set B.places.Pl} {nch : NChoice D} {nch' : NChoice D'}
    (h : _root_.GlobalTheory.HeightCounting.Up.OriginData hL cDep K w Wt nch) (hk : Kept nch nch') : _root_.GlobalTheory.HeightCounting.Up.OriginData hL cDep K w Wt nch' := by
  obtain ⟨P, x, l, h1, h2, h3⟩ := h
  exact ⟨P, x, l, h1, h2, kept_trans_layer h3 hk⟩
set_option maxHeartbeats 4000000 in
theorem lv3Mv_extensionWithOrigin_and_nEog : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (S : SExt) (Γ : GeoP), LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s ∧ LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep) S Γ).s := by
  intro hL cDep S Γ
  constructor
  · intro K B f T w Z l S' N h
    obtain ⟨p0', t', hs, hgeo, hpk, hrx⟩ := GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices K B f T w Z l.Wt l.p0 l.what₂ S' N h
    obtain ⟨nch', xd', hk, -, hn, -, hnx⟩ := _root_.GlobalTheory.T.exists_kept_choice_upper_lattice_alt hL K B f T w Z l.Wt S' N h l.nch l.xd
    obtain ⟨n'⟩ := hn l.n
    obtain ⟨rx'⟩ := hrx ⟨l.rx⟩
    obtain ⟨c, ⟨e, ⟨pin⟩⟩, ⟨org⟩⟩ := l.nx
    obtain ⟨⟨c', e'⟩⟩ := hnx l.p0 l.what₂ l.n p0' t' n' hs hgeo ⟨c, e⟩
    have pin' := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z l.Wt S' N h l.p0 l.what₂ p0' t' hs pin
    exact ⟨Lv3.mk ⟨l.g, l.coh, l.Wt, p0', t', rx'⟩ nch' n' xd'
      l.chiT ⟨c', ⟨e', ⟨pin'⟩⟩, ⟨_root_.GlobalTheory.HeightCounting.Up.org_of_kept_alt org hk⟩⟩, hpk⟩
  · intro K B f T w Z l S' N h
    obtain ⟨p0', t', hs, hgeo, hpk, hrx⟩ := GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices K B f T w Z l.Wt l.p0 l.what₂ S' N h
    obtain ⟨nch', xd', hk, -, hn, hg, hnx⟩ := _root_.GlobalTheory.T.exists_kept_choice_upper_lattice_alt hL K B f T w Z l.Wt S' N h l.nch l.xd
    obtain ⟨n'⟩ := hn l.n
    obtain ⟨rx'⟩ := hrx ⟨l.rx⟩
    obtain ⟨c, ⟨⟨e, ⟨pin⟩⟩, ⟨org⟩⟩, ⟨good⟩⟩ := l.nx
    obtain ⟨⟨c', e'⟩⟩ := hnx l.p0 l.what₂ l.n p0' t' n' hs hgeo ⟨c, e⟩
    have pin' := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z l.Wt S' N h l.p0 l.what₂ p0' t' hs pin
    exact ⟨Lv3.mk ⟨l.g, l.coh, l.Wt, p0', t', rx'⟩ nch' n' xd'
      l.chiT ⟨c', ⟨⟨e', ⟨pin'⟩⟩, ⟨_root_.GlobalTheory.HeightCounting.Up.org_of_kept_alt org hk⟩⟩, ⟨hg good⟩⟩, hpk⟩
end GlobalTheory.HeightCounting.Up
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lv3Mv_extensionWithOrigin_and_NEog : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (S : SExt) (Γ : GeoP), LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s ∧ LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep) S Γ).s := by
  atlas_forward_decl _root_.GlobalTheory.HeightCounting.Up.lv3Mv_extensionWithOrigin_and_nEog
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
noncomputable section
namespace GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 4000000
theorem movable_prmR_nel_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (Γ : GeoP), PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl Γ)).s := by
  intro hL cDep Γ
  intro K B f T w Z O x N h O' hO' col n
  obtain ⟨t', hs, hgeo, hpk, hobj, hrx⟩ := GlobalTheory.T.rows_pass_to_moved_divisionLatticesHeights K B f T w Z x.Wt O x.what₂ N h O' hO'
  obtain ⟨nch', xd', hkept, hnx, -, -, hmv⟩ := _root_.GlobalTheory.T.exists_kept_choice_upper_lattice_alt hL K B f T w Z x.Wt Z.S N h O.nch O.xd
  obtain ⟨hn1, hn2⟩ := hnx rfl
  subst hO'
  have e1 : nch' = (O.tr N h).nch := eq_of_heq hn1
  have e2 : xd' = (O.tr N h).xd := eq_of_heq hn2
  subst e1 e2
  have hlp := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z x.Wt Z.S N h O.p0 x.what₂ (O.tr N h).p0 t' hs x.nx.2.1.2.down
  obtain ⟨P, y, l, hls, hW, hk⟩ := x.nx.2.2.down
  obtain ⟨c⟩ := hmv O.p0 x.what₂ x.n (O.tr N h).p0 t' n hs hgeo ⟨x.nx.1, x.nx.2.1.1⟩
  obtain ⟨s⟩ := GlobalTheory.T.spectralStageData_transfer_lattices_heights K B f T w Z x.Wt O.p0 x.what₂ x.col.toColT N h (O.tr N h).p0 t' col.toColT hpk ⟨x.sx.1⟩
  obtain ⟨o⟩ := GlobalTheory.T.divisionGeometryScalars_transfer_setDivision Γ K B f T w Z x.Wt N h O (O.tr N h) rfl x.what₂ t' hs x.ox
  exact ⟨t', hobj x.obj, hrx ⟨x.rx⟩, ⟨⟨c.1, ⟨c.2, ⟨hlp⟩⟩, ⟨⟨P, y, l, hls, hW, kept_trans hk hkept⟩⟩⟩⟩, ⟨⟨s, PUnit.unit⟩⟩, ⟨o⟩⟩
end GlobalTheory.HeightCounting.Up
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slot_mv_extension_with_origin_geo_cl : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (Γ : GeoP), PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl Γ)).s := by
  atlas_forward_decl _root_.GlobalTheory.HeightCounting.Up.movable_prmR_nel_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Mem.SRe.UpS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms MeasureTheory NumberField IsDedekindDomain
  GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
set_option maxHeartbeats 8000000 in
theorem exists_late_level_of_gap {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (hS : p.S = SExt.none) (hM : LevelThreeCondition p.s) (hN : SatNew) (hR : RealOf)
    (hP : PackEx) (hV : ∀ D : D7, VolTieG D → StandardLattice.VolumeEqMass₂ D) (hE : ∀ D : D7, GlobalTheory.GLq.ESerTie D → IdempotentRealFixed D) (hO : K.Over B.toPre)
    (a : w.Lt) (l : Lv3 p.s K w a) (gap : GapHyp (Late.D a)) (hdel : a.S.s.Del = (Delv K.s K.cD : ℚ))
    (hs : a.S.s.cdScale = Vol.trueScale a.G.cd) (hd : ∀ τ, a.S.dsig τ = Vol.trueDsig B.R (B.hc τ))
    (loc : Formalism.L2.SG.Pf.LocCP.LocTied (Late.D a)) : ∃ b : w.Lt, Nonempty (Lv4 p.s K w b) := by
  obtain ⟨vt, -, ⟨col⟩⟩ := l.g a.W a.V a.S a.N
  have col₀ : ColT w a := col.toColT
  obtain ⟨P, hI⟩ := hP (Late.D a) (fun u => (col₀.C.forms u).to0) gap loc
  have real₀ : RealTied (Late.D a) := (by with_unfolding_all exact ((real_of hR a l.g hs hd) :))
  have dstar : (Late.D a).what₂.Dstar = StandardLattice.DstarD (Late.D a) := (sizes_eq_count K (Late.st a) hO (hV _ real₀.vol) hd).2
  have e0 : IdempotentRealFixed (Late.D a) := hE _ (l.what₂.grp.eSerTie a.V a.S a.G)
  obtain ⟨Zs, H⟩ := hN B w.C a (pkOf l.what₂) _ P gap hI loc real₀ dstar e0 (rowHyp_pkOf l.what₂)
  let b : w.Lt := upL a (reSt a Zs) (fun u => (a.V.div.Nu u).L) a.V.div.h
  obtain ⟨l', e⟩ := hM K B f T w a l (reSt a Zs) (fun u => (a.V.div.Nu u).L) a.V.div.h
  obtain ⟨-, -, ⟨col'⟩⟩ := l'.g b.W b.V b.S b.N
  have col₁ : ColumnDataSplitPrimes K w b := col'
  obtain ⟨s⟩ := sat_col a col₀ (pkOf l.what₂) Zs H _ _ col₁.toColT
  have s' : SX K B f T w b l'.Wt l'.p0 l'.what₂ col₁.toColT := by
    rw [sx_eq l'.what₂ col₁.toColT, e]
    exact s
  have x : p.S K B f T w b l'.Wt l'.p0 l'.what₂ col₁.toColT s' := by
    rw [hS]
    exact PUnit.unit
  exact ⟨b, ⟨⟨l', col₁, real_of hR b l'.g ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (hd :))), (by with_unfolding_all exact (hd :)), (by with_unfolding_all exact (hdel :)), ⟨s', x⟩⟩⟩⟩
set_option maxHeartbeats 8000000 in
theorem pin_has3_to_has4_of_sat_new {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (hS : p.S = SExt.none) (hM : LevelThreeCondition p.s) (hN : SatNew) (hR : RealOf)
    (hP : PackEx) (hV : ∀ D : D7, VolTieG D → StandardLattice.VolumeEqMass₂ D) (hE : ∀ D : D7, GlobalTheory.GLq.ESerTie D → IdempotentRealFixed D) :
    StepW (pinAnd (Has3 p.s)) (Has4 p.s) := by
  refine Step.of_evG ((evG_of_ev GlobalTheory.Mem.Top.NodeGap.ev_gapHyp).imp fun K _ _ _ _ gap B f T hO _ _ _ w => ?_)
  rintro ⟨-, Z, ⟨l⟩⟩
  obtain ⟨S, hdel, hs, hd, loc⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K B w.C Z.W Z.G.cd hO (SpectralModel.colsPos_of Z.S) (SpectralModel.rows_le_of Z.S)
  obtain ⟨l₀, -⟩ := hM K B f T w Z l S (fun u => (Z.V.div.Nu u).L) Z.V.div.h
  exact _root_.GlobalTheory.Mem.SRe.UpS.exists_late_level_of_gap p hS hM hN hR hP hV hE hO _ l₀ (gap _ hO) hdel hs hd ((by with_unfolding_all exact ((loc (upL Z S (fun u => (Z.V.div.Nu u).L) Z.V.div.h).V Z.N Z.G) :)))
end GlobalTheory.Mem.SRe.UpS
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.Mem.SRe.UpS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms MeasureTheory NumberField IsDedekindDomain
  GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
theorem has4_of_has3_of_sExt_none : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Vol.DiscreteSeriesExist → Vol.FormalDegreeFormula₂ → StandardLattice.SiegelMassRatioCM → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p.S = SExt.none → LevelThreeCondition p.s → StepW (pinAnd (Has3 p.s)) (Has4 p.s) :=
  fun h1 h2 h3 h4 h5 hW hD hF _ _ p hS hM =>
    _root_.GlobalTheory.Mem.SRe.UpS.pin_has3_to_has4_of_sat_new p hS hM (satOfDiscreteSeries h1 h2 h3 h4 h5) (realOf hD hF) (_root_.GlobalTheory.Mem.SRe.exists_sPack_integrable_alt hW h5)
      (GlobalTheory.Mem.VolMass.volumes_eq_masses_of_unfold (GlobalTheory.VolRatioFromSiegelWeil.volumeRatio hW)) goodIdempotent_real_of_harishChandra_series
end GlobalTheory.Mem.SRe.UpS
end
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.SRe
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.has4_of_has3_of_lv3Mv : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Vol.DiscreteSeriesExist → Vol.FormalDegreeFormula₂ → StandardLattice.SiegelMassRatioCM → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p.S = SExt.none → LevelThreeCondition p.s → StepW (pinAnd (Has3 p.s)) (Has4 p.s) := by
  first | exact @_root_.GlobalTheory.Mem.SRe.UpS.has4_of_has3_of_sExt_none | exact _root_.GlobalTheory.Mem.SRe.UpS.has4_of_has3_of_sExt_none | (intros; apply _root_.GlobalTheory.Mem.SRe.UpS.has4_of_has3_of_sExt_none <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw GlobalTheory.ShFam
open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Mem.Th
namespace GlobalTheory.Mem.Top.Closing
theorem goodE_of_builtE_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N Ng : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP)
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, Ng K B f T w Z Wt p0 t nch n xd c →
      Nonempty (N K B f T w Z Wt p0 t nch n xd c) ∧ GoodO (w.D Z) nch xd) :
    ∀ K B f T w Z c, BuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng S Γ).s K B f T w Z c →
      GoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd := by
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
end GlobalTheory.Mem.Top.Closing
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw GlobalTheory.ShFam
open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Mem.Th
namespace GlobalTheory.Mem.Top.Closing
theorem memberE_closing_alt_alt : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Vol.DiscreteSeriesExist → Vol.FormalDegreeFormula₂ → StandardLattice.SiegelMassRatioCM → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N Ng : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL), StepW Start (Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) → LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s → LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)).s → ExportF KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) → Pass KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) (fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)).s K B f T w) → (∀ K B f T w Z Wt p0 t nch n xd c, Ng K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c) ∧ GoodO (w.D Z) nch xd) → MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s := by
  intro p1 p2 p3 s1 s2 s3 s4 s5 s6 s8 s9 pv t1 t2 t3 t4 t5 t6 t7 hL N Ng h3 mv mv' ex ps hN
  exact GlobalTheory.T.exists_member_of_construction_steps_secondPass p1 p2 p3 pv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)).s h3
    (_root_.GlobalTheory.T.has4_of_has3_of_lv3Mv s1 s2 s3 s4 s5 s6 s8 s9 pv hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)) rfl mv)
    (GlobalTheory.AmbCrd.ambEx_of_rx _ rfl) (divEx_geoCl p1 p2 p3 _ _ _)
    (GlobalTheory.T.exists_thetaData_trueRowsColumns_allCompatible t1 t2 t3 t4 t5 t6 t7 _ (io_zero _ rfl)) ex ps
    (_root_.GlobalTheory.T.has4_of_has3_of_lv3Mv s1 s2 s3 s4 s5 s6 s8 s9 pv hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)) rfl mv')
    (GlobalTheory.AmbCrd.ambEx_of_rx _ rfl) (divEx_geoCl p1 p2 p3 _ _ _)
    (GlobalTheory.T.exists_thetaData_trueRowsColumns_allCompatible t1 t2 t3 t4 t5 t6 t7 _ (io_zero _ rfl))
    (_root_.GlobalTheory.Mem.Top.Closing.goodE_of_builtE_alt hL N Ng SExt.none (geoCl anyGeometry) hN)
end GlobalTheory.Mem.Top.Closing
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.SRe
set_option maxHeartbeats 2000000
namespace GlobalTheory.Mem.Top.Bl
theorem exists_baseLattice_of_pair_alt (hA : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt) (hE : _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis) (hH : _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hN : _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL) (N Ng : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL)
    (toB : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c))
    (toN : ∀ K B f T w Z Wt p0 t nch n xd c, Ng K B f T w Z Wt p0 t nch n xd c →
      Nonempty (N K B f T w Z Wt p0 t nch n xd c) ∧ GoodO (w.D Z) nch xd)
    (has3 : StepW Start (Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s))
    (lv : LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) (lvg : LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)).s)
    (intersection_update_fsHerm_neg_one : PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s)
    (second : Pass KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) fun K B f T =>
      ∃ w : ColW B f T, Start K B f T w ∧ Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)).s K B f T w)
    (hMQ : _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry))) :
    MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s ∧
      GlobalTheory.Fc.ExBL KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s)
        (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry))) := by
  have exp := _root_.GlobalTheory.T.automorphy_of_hypotheses_alt_alt hE.e1 hE.e2 hE.e3 hE.e4 hE.e5 hE.e6 hE.e7 hE.e8 hE.e9 hE.e10 hE.e11 hE.e12 hE.e13 hA.a6 hE.e14 hA.a22
    hE.e15 hE.e16 hE.e17 hE.e18 hE.e19 hE.e20 hE.e21 hE.e22 hE.e23 hE.e24 hE.e25 hN.pr hN.ser hL hN.parMem N
    SExt.none (geoCl anyGeometry) toB
  refine ⟨?_, ?_⟩
  · exact _root_.GlobalTheory.Mem.Top.Closing.memberE_closing_alt_alt hA.a1 hA.a2 hA.a3 hA.a11 hA.a10 hA.a6 hA.a12 hA.a13 hA.a14 hA.a16 hA.a17 hA.a18 hA.a8 hA.a6 hA.a7
      hA.a5 hA.a19 hA.a20 hA.a21 hL N Ng has3 lv lvg exp second toN
  · exact _root_.GlobalTheory.T.geometric_parameter_uniform_alt hH.h1.q12 hH.cover hA.a5 hA.a7 hA.a8 hA.a9 hA.a10 hA.a6 hA.a22 hA.a23 hA.a1 hL N (geoCl anyGeometry)
      (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)) rfl toB intersection_update_fsHerm_neg_one hMQ
theorem exists_baseLattice_of_prime_alt : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → ExistsUnlocalizedSaturatedState → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL → ∀ cDep : ℝ,
    _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)) → MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s ∧
      GlobalTheory.Fc.ExBL KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s)
        (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry))) := by
  intro hA hE hH hW hL hN cDep hMQ
  have holdsW : WeightCaseCondition := _root_.GlobalTheory.T.w_of_weight_residue_char hH.h1 hH.h3 hH.multW
  have datE : DatExt := GlobalTheory.T.fineAdelicDatum_extends_to_larger_field_of_hypotheses hH.cover hA.a5 hA.a6 hA.a7 hA.a8 hA.a9 hA.a10
  have h := _root_.GlobalTheory.T.all_stages_at_member_of_specializations_alt (by first | exact hA.a5 | exact hA.a7) (by first | exact hA.a5 | exact hA.a7)
  repeat (first | specialize h hA.a8 | specialize h hA.a9 | specialize h hA.a12 | specialize h hA.a5 | specialize h hA.a6 | specialize h hA.a7 | specialize h hA.a10 | specialize h hA.a22 | specialize h hH | specialize h hN.pr | specialize h hN.ser | specialize h hL | specialize h hN.arch | specialize h hN.pt)
  obtain ⟨sA, sMt, sRat, sCusp, -, -, -, sC, -, sl⟩ := h
  obtain ⟨fin, second⟩ := _root_.GlobalTheory.T.sFino_and_secondNo_of_sFinl' hH.cover (by first | exact hA.a5 | exact hA.a7) (by first | exact hA.a5 | exact hA.a7) hN.pr hN.ser datE holdsW hA.a9 hN.arch.pht hL sMt sRat sCusp cDep (sl cDep).2.2.2
  have has3 := _root_.GlobalTheory.Mem.Top.Bl.has3_neo_of_localLanglands_alt hL cDep hW sA sMt sRat sCusp (sl cDep).1 (sl cDep).2.1 (sl cDep).2.2.1 sC fin SExt.none (geoCl anyGeometry)
  have lv := _root_.GlobalTheory.T.lv3Mv_extensionWithOrigin_and_NEog hL cDep SExt.none (geoCl anyGeometry)
  exact _root_.GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_pair_alt hA hE hH hL hN (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨⟨h.1⟩, h.2.down⟩) has3 lv.1 lv.2 (_root_.GlobalTheory.T.slot_mv_extension_with_origin_geo_cl hL cDep anyGeometry)
    (second SExt.none (geoCl anyGeometry)) hMQ
end GlobalTheory.Mem.Top.Bl
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.member_exists_baseLattice_alt : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → ExistsUnlocalizedSaturatedState → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL → ∀ cDep : ℝ, _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)) → MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s ∧ GlobalTheory.Fc.ExBL KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry))) := by
  first | exact @_root_.GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_prime_alt | exact _root_.GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_prime_alt | (intros; apply _root_.GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_prime_alt <;> assumption)
end
end
end
