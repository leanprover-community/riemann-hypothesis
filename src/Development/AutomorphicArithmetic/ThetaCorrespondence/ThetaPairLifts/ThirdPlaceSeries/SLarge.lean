import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SEta
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaEventuallyAgrees
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FirstTermConditionHoldsAllStages
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatIntMember
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpenWithLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientBuiltLocalHypothesis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarClosedIntegralLatticeAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentIntegralAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplitAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebotarevSplitAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisRepsCuspidalAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlCGTruegalEx
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvOLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenRationalityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenRationality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenUnitary
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ContainsWithLocStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsBigOSplitStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvOTakenAllStatement

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
namespace GlobalTheory.CoefDuty
theorem latInt_member_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), MtInput D M tup C.Q → ∀ big L, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L → (∀ i, (withLoc L).nd.Q i = C.Q ((withLoc L).nd.w i)) ∧ ∀ j h1 h2 w, (withLoc L).what₂.muAt w ≠ (withLoc L).what₂.mu0 → LatInt (withLoc L) (mtL L M) (C.Q w) j h1 h2 w := by
  intro D cf jE A M C tup hM big L hB
  obtain ⟨Sp, -, -⟩ := hB
  refine ⟨fun i => ?_, fun j h1 h2 w hw => ?_⟩
  · have h : i ∈ L.X.nd.locs (L.X.nd.j i) (L.X.nd.w i) := (L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
    exact (Sp.Q_eq _ _ i h).trans (Sp.Qc_eq _ _)
  · obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have h2' : j < D.R.m := h2
    exact ⟨(hM.full w ⟨j, h2'⟩ hw).1, fun v k s ϖ hg hc hu => hM.int w ⟨j, h2'⟩ v k s ϖ hw hg hc hu⟩
end GlobalTheory.CoefDuty
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.etaJ_with_local_data_eq_alt : ∀ (hPr : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}, KPx B f → Forced K B T → Start K B f T w → ∀ (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (M : MtFam (withLoc L)) (Tn : NormalizedLocalCompatibility (withLoc L) M) (Q : (withLoc L).what₂.places.Pl → Finset (PlE (withLoc L).host)), HeckeStdTw Tn.B → (∀ i, (withLoc L).nd.Q i = Q ((withLoc L).nd.w i)) → (∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (w' : (withLoc L).what₂.places.Pl), (withLoc L).what₂.muAt w' ≠ (withLoc L).what₂.mu0 → GlobalTheory.CoefDuty.LatInt (withLoc L) M (Q w') j h1 h2 w') → HeckeTied (withLoc L) M → HeckeRational (withLoc L) M → AVTied (withLoc L) M → (∀ i, GlobalTheory.CoefDuty.ClassSum (M.loc i)) → (withLoc L).nd.EigSpan → Rows.IsotInternal (withLoc L).what₂ → SumRepresentations.Conclusion42 (withLoc L) → SumRepresentations.ConclusionZ (withLoc L) → GoodFTAll (withLoc L) → ∀ (j : ℕ) (v : B.places.Pl), 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : (withLoc L).what₂.places.Pl, HEq v' v → (withLoc L).what₂.etaJ j v' = P.q.eta j v := by
  intro hPr hL K B f T w P hK hF hS x l big L hB hO M Tn Q hstd hQ hlat hT hR hAV hCS hE hI h42 hZ hG j v h1 h2 v' hv
  obtain rfl : v' = v := eq_of_heq hv
  have hTup : Formalism.L2.DIV.TupTie (withLoc L) (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A
      ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)) x.r.Y.tup :=
    ⟨x.r.Y.tup0, x.r.Y.muAt, x.m.z.R.hv0, fun a b h => by rw [← x.r.Y.tupT_tup a, h, x.r.Y.tupT_tup]⟩
  have hTw : ∀ y, y ∈ ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)).Tw ↔
      ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)).μ y ≠
        (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A.μ0 :=
    fun y => ⟨x.m.z.pins.char.tup.mu_ne y, fun h => by_contra fun hw => h (x.m.z.pins.char.tup.mu_off y hw)⟩
  have hθ := GlobalTheory.Mem.ThRead.theta_of_noEta GlobalTheory.Mem.ThetaRead3.thetaP_read_noEta GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth_noEta
    _ _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG x.s.p0 x.r.Y x.r.Z x.m.z.pins x.m.intersectionNumber_baseChange
  have hZ0 := GlobalTheory.Mem.R3.DivisionRationalLift.rationalReadingNoCongruence_thetaComplement_spanned _ _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG x.s.p0 x.r.Y x.r.Z x.m.z.pins x.m.intersectionNumber_baseChange
  have key := GlobalTheory.T.congruenceLength_twistedPlaces_of_heckeIntegrality (withLoc L) _ _ _ _ (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A
    x.m.z.F.P0 x.m.z.F.ψ0 ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).fam3.toSub2 (zsOf x.m.z.R x.m.z.F))
    x.r.Y.tup x.r.Y.eMt 1 x.m.intersectionNumber_baseChange.ok.ok2 le_rfl
    ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)) M Tn
    hTup hTw (fun i y _ => ⟨x.r.Y.formsL i _, x.r.Y.latL i _, hZ0 i _⟩) hstd Q hQ hlat hT hR hAV hCS x.r.Z.jW rfl
    (fun i y _ x' => hθ i _ x') hE hI h42 hZ hG
  obtain ⟨i, rfl⟩ : ∃ i : Fin (Dof x).R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  refine (key i v').trans (Eq.trans ?_ (x.m.eta _ v'))
  unfold Rw.etaOf
  rw [dif_pos ⟨by omega, i.2⟩]
  split_ifs with ha hb hb
  · simp only [Nat.add_sub_cancel, Fin.eta]
    rfl
  · exact (hb ha).elim
  · exact (ha hb).elim
  · rfl
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaJ_local_compatibility_alt : ∀ (hPr : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}, KPx B f → Forced K B T → Start K B f T w → ∀ (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (M : MtFam (withLoc L)) (Tn : NormalizedLocalCompatibility (withLoc L) M) (Q : (withLoc L).what₂.places.Pl → Finset (PlE (withLoc L).host)), HeckeStdTw Tn.B → (∀ i, (withLoc L).nd.Q i = Q ((withLoc L).nd.w i)) → (∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (w' : (withLoc L).what₂.places.Pl), (withLoc L).what₂.muAt w' ≠ (withLoc L).what₂.mu0 → GlobalTheory.CoefDuty.LatInt (withLoc L) M (Q w') j h1 h2 w') → HeckeTied (withLoc L) M → HeckeRational (withLoc L) M → AVTied (withLoc L) M → (∀ i, GlobalTheory.CoefDuty.ClassSum (M.loc i)) → (withLoc L).nd.EigSpan → Rows.IsotInternal (withLoc L).what₂ → SumRepresentations.Conclusion42 (withLoc L) → SumRepresentations.ConclusionZ (withLoc L) → GoodFTAll (withLoc L) → ∀ (j : ℕ) (v : B.places.Pl), 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : (withLoc L).what₂.places.Pl, HEq v' v → (withLoc L).what₂.etaJ j v' = P.q.eta j v := by
  first | exact @_root_.GlobalTheory.etaJ_with_local_data_eq_alt | exact _root_.GlobalTheory.etaJ_with_local_data_eq_alt | (intros; apply _root_.GlobalTheory.etaJ_with_local_data_eq_alt <;> assumption)
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
namespace GlobalTheory.EtaMem
open GlobalTheory.CoefDuty GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_etaJ_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PointStatement hL → AllSt fun _ _ _ _ _ P x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → ∀ j v, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : D'.what₂.places.Pl, HEq v' v → D'.what₂.etaJ j v' = P.q.eta j v := by
  intro hPr hL hPt
  have hG := _root_.GlobalTheory.T.allSt_goodFTAll_of_levelA hPr hL
  have hI := GlobalTheory.T.twistedPlace_innerProduct_classSum_rows
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hPr.what₂.cheb
  unfold _root_.GlobalTheory.HeightCounting.Up.PointStatement at hPt
  unfold AllSt at hPt hG ⊢
  unfold OverRows at hI
  unfold StepW GroupRetwisting.Step EvLgG at hPt hG ⊢
  refine EvG.imp (EvG.inter (EvG.inter hPt hG) hI) fun K _ _ _ _ h => ?_
  refine large₂.imp (large₂.inter (large₂.inter h.1.1 h.1.2) h.2) fun B f T _ g => ?_
  intro hKP hF _ w hS P x l
  have hpin : ColPin w := hS.1.some
  obtain ⟨big, hbig⟩ := g.1.1 hKP hF trivial w hS P x l
  refine ⟨big, fun L hB hO => ?_⟩
  have hB0 := hB
  obtain ⟨hconds, hEig, hIso⟩ := hbig L hB
  obtain ⟨-, -, h42, hZ⟩ := hconds hO
  have hgood : GoodFTAll (withLoc L) := g.1.2 hKP hF trivial w hS P x l.toLA
  have hmt : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
    have h0 := l.mt.mt
    have e1 := l.c.xi_eq
    have e2 := l.c.Q_eq
    unfold TupTied.tup
    rw [e1, e2]
    exact h0
  have hlat := _root_.GlobalTheory.CoefDuty.latInt_member_alt (Dof x) (cfOf x) l.a.jE l.a.A l.mt.M l.c.ch l.c.tp.tup hmt big L hB
  have hsum : SumTw (Dof x) l.mt.M := g.2 hKP w hpin x.o.Z P.Wt P.hX x.m.z x.s.p0 x.r.Y x.m.intersectionNumber_baseChange x.m.exAt x.m.inGeo
    x.fits.grp x.fits.grpAt l.mt.M l.c.tp.tup l.c.ch.Q l.mt.ad hmt
  obtain ⟨Sp, ⟨Au⟩, hss⟩ := hB
  obtain ⟨Hk, -⟩ := _root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt (Dof x) (cfOf x) l.a.jE l.a.A (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL
    l.rat.In.eig l.rat.In.θ l.b.Bs l.mt.M l.c.ch l.c.tp l.c.side hmt l.a.elem.star l.a.elem.int l.a.elem.split
    (hcheb (Dof x)) big L Sp Au
  let cover : NormalizedLocalCompatibility (withLoc L) (mtL L l.mt.M) :=
    { B := { Sp.B with }
      Q_eq := Sp.Q_eq
      mx := Sp.mx
      mx_max := Sp.mx_max
      mx_inj := Sp.mx_inj
      mx_all := Sp.mx_all
      phO := Sp.phO
      phK := Sp.phK
      phK_alg := Sp.phK_alg
      phK_emb := Sp.phK_emb
      Psi := Sp.Psi
      Psi_inj := Sp.Psi_inj
      Psi_range := Sp.Psi_range
      Psi_pr := Sp.Psi_pr
      ptX := Sp.ptX
      ptX_hT := Sp.ptX_hT
      iotaC := Sp.iotaC
      iotaC_coh := fun j w i h z => by
        have e1 : (withLoc L).naut.iotaQ i = Sp.iq i := Au.iotaQ i
        have e2 : (withLoc L).naut.iotaQC i = qCast ((withLoc L).nd.w_l i) (l.a.A.pl.ι ((withLoc L).nd.w i)) := Au.iotaQC i
        unfold iotaOC
        rw [RingHom.comp_apply, RingHom.comp_apply, e1, e2]
        exact Sp.iotaC_coh j w i h z }
  have hstd : HeckeStdTw cover.B := heckeStdTw_of_std Sp.std
  have hcls : ∀ i, CoefDuty.ClassSum ((mtL L l.mt.M).loc i) := by
    intro i
    have hj := L.X.j_range i
    have h0 := hsum (L.X.w i) (L.X.w_tw i) (L.X.j i) hj.1 hj.2
    exact GlobalTheory.FitHecke.mt_transport l.mt.M (fun μ j m => CoefDuty.ClassSum m) (L.X.mu_w i).symm rfl hj.1 hj.2 hj.1 hj.2 h0
  exact _root_.GlobalTheory.T.etaJ_local_compatibility_alt hPr hL hKP hF hS x l big L hB0 hO (mtL L l.mt.M) cover l.c.ch.Q hstd hlat.1 hlat.2 Hk.hecke Hk.rational Hk.av hcls hEig hIso h42 hZ hgood
end GlobalTheory.EtaMem
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_etaJ_eq_eta_of_levelC : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PointStatement hL → AllSt fun _ _ _ _ _ P x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → ∀ j v, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : D'.what₂.places.Pl, HEq v' v → D'.what₂.etaJ j v' = P.q.eta j v := by
  first | exact @_root_.GlobalTheory.EtaMem.exists_etaJ_alt | exact _root_.GlobalTheory.EtaMem.exists_etaJ_alt | (intros; apply _root_.GlobalTheory.EtaMem.exists_etaJ_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem fixedField_star_stable_of_third_jump_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x =>
    ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ y : (Dof x).LL0, star (y : (Dof x).what₂.LL) ∈ (Dof x).LL0 := by
  intro _ _
  refine StepW.of_all fun K B f T w _ _ _ P x _ y => ?_
  exact (IntermediateField.normal_iff_forall_map_le.1 B.coeffGaloisSubfield_isGalois.to_normal
    (starRingEnd (Dof x).what₂.LL).toRatAlgHom) ⟨_, y.2, rfl⟩
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_mem_LL0_at_level_c : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ y : (Dof x).LL0, star (y : (Dof x).what₂.LL) ∈ (Dof x).LL0 := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.fixedField_star_stable_of_third_jump_alt | exact _root_.GlobalTheory.HeightCounting.Up.fixedField_star_stable_of_third_jump_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.fixedField_star_stable_of_third_jump_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem ramification_index_integral_of_third_jump_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ j g, ∃ z : ℤ, eExp (Dof x) j g = z := by
  intro _ _
  refine StepW.of_all fun K B f T w _ _ _ P x _ j g => ?_
  exact ((Dof x).hc ((Dof x).eTau.symm g)).e_int j
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eExp_integer_of_levelC : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ j g, ∃ z : ℤ, eExp (Dof x) j g = z := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.ramification_index_integral_of_third_jump_alt | exact _root_.GlobalTheory.HeightCounting.Up.ramification_index_integral_of_third_jump_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.ramification_index_integral_of_third_jump_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.SplitPrimeAuxiliary
open scoped Pointwise
theorem exists_auxiliary_prime_split_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ v, v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  intro _ hL
  refine StepW.of_all fun K B f T w _ _ _ P x _ v hv => ?_
  rcases hv with hv | hv
  · exact isSplitPl_of_split B.host B.host.pde_prime B.toPre.pde_split.1 v hv
  · exact isSplitPl_of_split B.host B.host.pde'_prime B.toPre.pde_split.2 v hv
end GlobalTheory.SplitPrimeAuxiliary
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.places_over_pde_isSplitPl_of_levelC : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ v, v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  first | exact @_root_.GlobalTheory.SplitPrimeAuxiliary.exists_auxiliary_prime_split_alt | exact _root_.GlobalTheory.SplitPrimeAuxiliary.exists_auxiliary_prime_split_alt | (intros; apply _root_.GlobalTheory.SplitPrimeAuxiliary.exists_auxiliary_prime_split_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up.ChebAtThird
theorem chebotarev_split_places_at_all_levels_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, GlobalTheory.RowTie.ChebSplit (Dof x).nd := by
  intro hP hL
  exact StepW.of_all fun _ _ _ _ _ _ _ _ _ _ _ => GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _
end GlobalTheory.HeightCounting.Up.ChebAtThird
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chebSplit_of_published_inputs_at_level_c : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, GlobalTheory.RowTie.ChebSplit (Dof x).nd := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.ChebAtThird.chebotarev_split_places_at_all_levels_alt | exact _root_.GlobalTheory.HeightCounting.Up.ChebAtThird.chebotarev_split_places_at_all_levels_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.ChebAtThird.chebotarev_split_places_at_all_levels_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem galoisRep_attached_to_cuspidal_all_levels_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x,
    _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => GlobalTheory.BlockComplement.GaloisRepsCusp D' := by
  intro hP hL
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  refine ⟨fun _ => ∅, fun L _ => ?_⟩
  let T' : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { l.a.A.wdT with }
  have cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL (withLoc L) T' := { l.a.cg with }
  exact galoisRepsCusp_of_galEx (cg.galEx hL hP.what₂.fin hP.what₂.gal)
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_galoisRepsCusp_of_level_c : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => GlobalTheory.BlockComplement.GaloisRepsCusp D' := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.galoisRep_attached_to_cuspidal_all_levels_alt | exact _root_.GlobalTheory.HeightCounting.Up.galoisRep_attached_to_cuspidal_all_levels_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.galoisRep_attached_to_cuspidal_all_levels_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.EigPlace
set_option maxHeartbeats 1000000 in
theorem built_finite_and_mem_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd →
    ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L →
    ∀ (i : L.X.nd.Loc) (x : L.X.nd.X i),
      (EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) (L.X.nd.j_range i).1 (L.X.nd.j_range i).2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i))).Finite ∧
      ptSys (withLoc L) i x ∈ EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) (L.X.nd.j_range i).1 (L.X.nd.j_range i).2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i)) := by
  intro hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB i x
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB
  obtain ⟨Hk, -⟩ := _root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb
    big L Sp Au
  have hQ : L.X.nd.Q i = C.Q (L.X.nd.w i) :=
    (Sp.Q_eq _ _ i ((L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
  exact finite_and_mem hstd (D := withLoc L) Hk.hecke Hk.av Hk.cover i x (C.Q (L.X.nd.w i)) hQ
end GlobalTheory.EigPlace
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_unitary_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd →
    ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L →
    ∀ (i : L.X.nd.Loc) (x : L.X.nd.X i),
      (EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) (L.X.nd.j_range i).1 (L.X.nd.j_range i).2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i))).Finite ∧
      ptSys (withLoc L) i x ∈ EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) (L.X.nd.j_range i).1 (L.X.nd.j_range i).2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i)) := by
  atlas_forward_decl _root_.GlobalTheory.EigPlace.built_finite_and_mem_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.LargeO
theorem evO_hypO_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup SumRepresentations.hypO := by
  intro hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb
  classical
  have hbig : ∀ lam (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
      (EigSet (M (D.what₂.muTw lam) j h1 h2) (D.what₂.places.resChar lam) (C.Q lam)).Finite →
      ∃ Sf, @BigOk D (D.what₂.places.resChar lam) ⟨D.what₂.places.resChar_prime lam⟩ (C.Q lam)
        (EigSet (M (D.what₂.muTw lam) j h1 h2) (D.what₂.places.resChar lam) (C.Q lam)) (A.pl.ι lam) Sf :=
    fun lam j h1 h2 hf => @exists_bigOk D _ ⟨D.what₂.places.resChar_prime lam⟩ _ _ _ hf hcheb
  let big : D.what₂.places.Pl → Finset ℂ := fun lam => (Finset.range (D.R.m + 1)).biUnion fun j =>
    if h : 1 ≤ j ∧ j ≤ D.R.m then
      if hf : (EigSet (M (D.what₂.muTw lam) j h.1 h.2) (D.what₂.places.resChar lam) (C.Q lam)).Finite then
        Classical.choose (hbig lam j h.1 h.2 hf) else ∅
    else ∅
  refine ⟨big, fun L hB => ?_⟩
  obtain ⟨Sp, ⟨Au⟩, hss⟩ := hB
  intro i x ρ hρ
  haveI : Fact (L.X.nd.l i).Prime := L.X.nd.lPrime i
  have hB' : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L := ⟨Sp, ⟨Au⟩, hss⟩
  obtain ⟨hfin, hpt⟩ := _root_.GlobalTheory.T.side_eigen_unitary_alt hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB' i x
  have hj := L.X.nd.j_range i
  have hOk : @BigOk D (D.what₂.places.resChar (L.X.nd.w i)) ⟨D.what₂.places.resChar_prime (L.X.nd.w i)⟩
      (C.Q (L.X.nd.w i)) (EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) hj.1 hj.2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i))) (A.pl.ι (L.X.nd.w i)) (big (L.X.nd.w i)) := by
    have hc := Classical.choose_spec (hbig (L.X.nd.w i) (L.X.nd.j i) hj.1 hj.2 hfin)
    refine bigOk_mono hc ?_
    intro z hz
    refine Finset.mem_biUnion.2 ⟨L.X.nd.j i, Finset.mem_range.2 (by omega), ?_⟩
    rw [dif_pos hj, dif_pos hfin]
    exact hz
  have hOk' := bigOk_cast (L.X.nd.w_l i) hOk
  obtain ⟨K, hK, -, -⟩ := GlobalTheory.T.localisation_coefField_finite_range (withLoc L).nd (withLoc L).naut i
  have hcont := (_root_.GlobalTheory.T.contains_after_localization_alt D cf jE A M C tp.tup big L hB' i).1
  have hKbig : ∀ z ∈ big (L.X.nd.w i), (qCast (L.X.nd.w_l i) (A.pl.ι (L.X.nd.w i))).symm z ∈ K := by
    intro z hz
    obtain ⟨y, hy⟩ := hcont z hz
    have hy' : L.Y.naut.iotaQC i (L.Y.naut.iotaQ i y) = z := hy
    rw [Au.iotaQC i] at hy'
    rw [← hy', RingEquiv.symm_apply_apply]
    exact (hK _).2 ⟨y, rfl⟩
  have hQ : L.X.nd.Q i = C.Q (L.X.nd.w i) :=
    (Sp.Q_eq _ _ i ((L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
  have hchar := charpoly_pt (withLoc L) i x ρ hρ
  have hchar' : ∀ v, (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E (L.X.nd.l i) ∧ v ∉ placesS D (L.X.nd.l i) ∧
      v ∉ C.Q (L.X.nd.w i)) → ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B v → IsFrob (F := D.host.E) B (normV v) σ →
      (show Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (L.X.nd.l i)) from (ρ σ).val).charpoly.map
        (qCast (L.X.nd.w_l i) (A.pl.ι (L.X.nd.w i))).toRingHom = sysPol D.R.nV (ptSys (withLoc L) i x) v := by
    intro v hv B σ hB hF
    rw [← Au.iotaQC i]
    exact hchar v ⟨hv.1, hv.2.1, hv.2.2.1, hQ ▸ hv.2.2.2⟩ B σ hB hF
  obtain ⟨P, hP⟩ := hOk' _ hpt K hKbig ρ hρ.1 hρ.2.1 hchar'
  exact model_of_conj (withLoc L).nd (withLoc L).naut i _ ρ P hρ.1 (fun g s t => (hK _).1 (hP g s t))
end GlobalTheory.LargeO
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_rationality_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup SumRepresentations.hypO := by
  atlas_forward_decl _root_.GlobalTheory.LargeO.evO_hypO_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
namespace GlobalTheory.CoefDuty
theorem large_of_large_rings_alt : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → _root_.GlobalTheory.CoefDuty.AutomorphicSideExists A M C tp.tup → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup (fun D' => (SumRepresentations.hypO D' → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D') ∧ GlobalTheory.BlockComplement.GaloisRepsCusp D') → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup Large := by
  intro hCheb D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh hEx hO
  have hStd : HeckeStdPlain := GlobalTheory.T.heckeDoubleCosetOperators_standardFacts
  have hConj := fun P₁ P₂ => (_root_.GlobalTheory.T.eventually_conjunction_mono_alt D cf jE A M C tp.tup P₁ P₂).1
  have hMono := fun P₁ P₂ => (_root_.GlobalTheory.T.eventually_conjunction_mono_alt D cf jE A M C tp.tup P₁ P₂).2.1
  have E1 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup SumRepresentations.hypO :=
    _root_.GlobalTheory.T.side_eigen_rationality_alt hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh
  have E2 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup GlobalTheory.SplitCoef.OSplit := by
    obtain ⟨big, hbig⟩ := _root_.GlobalTheory.T.side_multiplicity_cusp_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh
    refine ⟨big, fun L hB => ?_⟩
    obtain ⟨Sp, ⟨hA⟩, -⟩ := hB
    exact hbig L Sp hA
  have E3 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup (fun D' => ∀ i, ZDecomp D'.nd i) :=
    hMono _ _ (fun D' h => GlobalTheory.T.thetaLocusDecomposesOverCoefRing_of_chebotarev hCheb D' h.2) hO
  have E4 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup (fun D' => _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D') :=
    hMono _ _ (fun D' h => h.2.1 h.1) (hConj _ _ E1 hO)
  have E5 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup TakenAll :=
    _root_.GlobalTheory.T.side_eigen_hecke_match_alt hCheb hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh hEx
      (hMono _ _ (fun D' h => ⟨h.1.1, h.2.1, h.2.2⟩) (hConj _ _ E4 (hConj _ _ E2 E3)))
  have EL : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup Large :=
    hMono _ _ (fun D' h => ⟨h.1, h.2.1, h.2.2⟩) (hConj _ _ E1 (hConj _ _ E2 E5))
  exact EL
end GlobalTheory.CoefDuty
end
namespace GlobalTheory.StEta
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
theorem sEta_alt_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PointStatement hL → _root_.GlobalTheory.HeightCounting.Up.EtaStatement' hL := by
  intro hP hL hPt
  refine ((((((hPt.and (_root_.GlobalTheory.T.eventually_etaJ_eq_eta_of_levelC hP hL hPt)).and (_root_.GlobalTheory.T.star_mem_LL0_at_level_c hP hL)).and (_root_.GlobalTheory.T.eExp_integer_of_levelC hP hL)).and (_root_.GlobalTheory.T.places_over_pde_isSplitPl_of_levelC hP hL)).and (_root_.GlobalTheory.T.chebSplit_of_published_inputs_at_level_c hP hL)).and
    (_root_.GlobalTheory.T.eventually_galoisRepsCusp_of_level_c hP hL)).trans (StepW.of_all ?_)
  intro K B f T w _ _ H P x l hB
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, hst⟩, hex⟩, hsp⟩, hch⟩, h4⟩ := H
  have law := fun P₁ P₂ => _root_.GlobalTheory.CoefDuty.LargeRing.evO_laws_alt (Dof x) (cfOf x) l.a.jE l.a.A l.mt.M l.c.ch l.c.tp.tup P₁ P₂
  have hin : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
      (SumRepresentations.hypO D' → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D') ∧ GlobalTheory.BlockComplement.GaloisRepsCusp D' :=
    (law _ _).1 ((law _ _).2.1 (fun D' h hO => ⟨(h.1 hO).1, (h.1 hO).2.1⟩) (h1 P x l)) (h4 P x l)
  have hMt : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
    show MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * l.c.tp.xi μ) l.c.ch.Q
    rw [l.c.xi_eq, l.c.Q_eq]; exact l.mt.mt
  have hm := (_root_.GlobalTheory.CoefDuty.large_of_large_rings_alt hP.cheb (Dof x) (cfOf x) l.a.jE l.a.A (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig
    l.rat.In.θ l.b.Bs l.mt.M l.c.ch l.c.tp l.c.side hMt (hst P x l) (hex P x l) (hsp P x l) (hch P x l) hB hin)
  refine (law _ _).2.1 ?_ ((law _ _).1 hm (h2 P x l))
  intro D' h
  have hO : SumRepresentations.hypO D' := by have h' := h.1; unfold GlobalTheory.CoefDuty.Large at h'; exact h'.1
  exact ⟨h.1, h.2 hO⟩
end GlobalTheory.StEta
end
end
end
