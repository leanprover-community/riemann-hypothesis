import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryQuadraticTwistLevelStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryQuadraticTwistLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TruePackTwistPlacePropertyStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkFramePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistScalarStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistScalar

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_pack_twist_place_property_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E), PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t → ∀ j, j < (I.rec7 l Z).R.m → (∃ N, IsSDFrame (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) N) ∧ ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, PP'.under (𝓞 (I.rec7 l Z).host.F) ≠ PP.under (𝓞 (I.rec7 l Z).host.F) := by
  first | exact @_root_.GlobalTheory.PkFrame.pk_frame_places_alt | exact _root_.GlobalTheory.PkFrame.pk_frame_places_alt | (intros; apply _root_.GlobalTheory.PkFrame.pk_frame_places_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
noncomputable section
namespace GlobalTheory.QLevMid
set_option maxHeartbeats 2000000 in
theorem level_at_place_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (_root_.GlobalTheory.Fam.chrK_alt W t)), (a.Q PP ⟨t, hP⟩).Res E.δ ((_root_.GlobalTheory.Fam.pk_z W).xiR t PP) → ∀ (j d : ℕ) (hd : j + d = (a.Q PP ⟨t, hP⟩).s + 1), j < (I.rec7 l Z).R.m → ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin d), ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j ∈ levS (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ↔ x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J) ∧ ∀ hx : x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J, Lev.levChi (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j) = ((((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).lam ⟨x, hx⟩ : ℂ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT t PP hP E hRes j d hd hj x hxK
  obtain ⟨⟨N, hSD⟩, hPg⟩ := _root_.GlobalTheory.T.true_pack_twist_place_property_alt W hW t PP hP j hj
  obtain ⟨e, he, hmv⟩ := (a.Q PP ⟨t, hP⟩).frame j d hd
  have hloc := (a.Q PP ⟨t, hP⟩).gl_loc j d hd x
  obtain ⟨hG, hSt, hOff⟩ := GlobalTheory.T.splitPlace_conj_stabilizes_framedLattice_iff _ _ (a.Q PP ⟨t, hP⟩).q PP (a.Q PP ⟨t, hP⟩).idem _ _ _ N hSD _ _ (e.symm.trans (stdOrd _ _ j d hd)) _ hmv _ _ hloc
  have hRed := GlobalTheory.T.reduction_conjugated_eq_movedFrame_matrix _ _ (a.Q PP ⟨t, hP⟩).q PP (a.Q PP ⟨t, hP⟩).idem _ (a.Q PP ⟨t, hP⟩).compl _ _ _ N hSD _ _ (e.symm.trans (stdOrd _ _ j d hd)) _ hmv _ _ hloc
  obtain ⟨hι, hrep⟩ := GlobalTheory.T.completion_smallIntegers_in_prime_dense _ _ PP _ _ _ (a.Q PP ⟨t, hP⟩).compl (a.Q PP ⟨t, hP⟩).unif
  have hSt' := hSt.2 hxK
  have hQ : ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, PP'.under (𝓞 (I.rec7 l Z).host.F) = PP.under (𝓞 (I.rec7 l Z).host.F) → PP' = PP :=
    fun PP' hP' h => hW.pk.sel PP' PP ⟨t, hP'⟩ ⟨t, hP⟩ h
  obtain ⟨hmem, hchi⟩ := GlobalTheory.T.mem_twistPlaceLevel_single_place_character _ _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) (I.rec7 l Z).R.r (I.rec7 l Z).R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ((_root_.GlobalTheory.Fam.pk_z W).Q t) (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR t) PP hP hPg hQ _ hG hOff
  have hr : (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + ((a.Q PP ⟨t, hP⟩).s + 1) := by
    have := (a.Q PP ⟨t, hP⟩).hs
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hC1 := GlobalTheory.T.reductionBlockTriangular_iff_mem_parahoricLevel _ _ PP _ hι (I.rec7 l Z).R.k (I.rec7 l Z).R.t (a.Q PP ⟨t, hP⟩).s j d hd E.δ E.tame E.η _ e he x hxK _ (hRed hSt')
  have hC2 := GlobalTheory.T.parahoricLevelCharacter_eq_inv_blockDet _ _ PP _ hι hrep (I.rec7 l Z).R.k (I.rec7 l Z).R.t (a.Q PP ⟨t, hP⟩).s j d hd E.δ E.tame E.η ((_root_.GlobalTheory.Fam.pk_z W).xiR t PP) hRes _ e he x
  rw [← hr] at hC1 hC2
  refine ⟨hmem.trans ⟨fun h => hC1.1 h.2, fun h => ⟨hSt', hC1.2 h⟩⟩, fun hx => ?_⟩
  exact (hchi hSt').trans (congrArg Units.val (hC2 hx _ (hRed hSt') (hC1.2 hx)))
end GlobalTheory.QLevMid
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (_root_.GlobalTheory.Fam.chrK_alt W t)), (a.Q PP ⟨t, hP⟩).Res E.δ ((_root_.GlobalTheory.Fam.pk_z W).xiR t PP) → ∀ (j d : ℕ) (hd : j + d = (a.Q PP ⟨t, hP⟩).s + 1), j < (I.rec7 l Z).R.m → ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin d), ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j ∈ levS (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ↔ x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J) ∧ ∀ hx : x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J, Lev.levChi (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j) = ((((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).lam ⟨x, hx⟩ : ℂ) := by
  atlas_forward_decl _root_.GlobalTheory.QLevMid.level_at_place_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.TopLevQ.mem_levS_top_iff_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (_root_.GlobalTheory.Fam.chrK_alt W t)), ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.Ix (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.Q PP ⟨t, hP⟩).s + 1)) (Fin (I.rec7 l Z).R.t) ((a.Q PP ⟨t, hP⟩).s + 2)), ∀ g, (ofSplit (a.Q PP ⟨t, hP⟩).q).IsLoc (a.Q PP ⟨t, hP⟩).FT g x → (a.g.bT⁻¹ * g * a.g.bT ∈ levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) ↔ x ∈ ((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).levTop.J) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha1 ha2 t PP hP E x hx g hg
  have hTop : x ∈ ((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).levTop.J ↔ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k _ ∧ GlobalTheory.StepData.MaxM x.val.toBlocks₂₁ := by
    show x ∈ ((GlobalTheory.StepData.parahoric _ _ E.δ E.tame).toLevel.map (GlobalTheory.StepData.LatFrame.refl _ _).conj).J ↔ _
    rw [GlobalTheory.StepData.Level.mem_map]
    have e1 : (GlobalTheory.StepData.LatFrame.refl (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.Ix (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.Q PP ⟨t, hP⟩).s + 1)) (Fin (I.rec7 l Z).R.t) ((a.Q PP ⟨t, hP⟩).s + 2))).conj.symm x = x := by
      ext i j
      simp [GlobalTheory.StepData.LatFrame.conj, GlobalTheory.StepData.LatFrame.refl, GlobalTheory.StepData.reGL_symm_val]
      rfl
    rw [e1]
    exact GlobalTheory.StepData.mem_parahoric
  rw [hTop]
  obtain ⟨e, he, hmv⟩ := (a.Q PP ⟨t, hP⟩).frameTop
  have hmv' : GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (a.Q PP ⟨t, hP⟩).q) (I.rec7 l Z).sp.X' a.g.bT (_root_.GlobalTheory.Fam.pk_z W).βX
      ((a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm) := hmv
  have hidem : Formalism.L2.NTheta.IsIdemAt (a.Q PP ⟨t, hP⟩).q.e PP := (a.Q PP ⟨t, hP⟩).idem
  have hβX : Formalism.IndefR.Links.IsSDFrame (I.rec7 l Z).sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.Fam.pk_z W).ΛX 1 := W.Q.charW.base.lev.βX
  obtain ⟨hGfC, hStIff, hoff⟩ := GlobalTheory.T.splitPlace_conj_stabilizes_framedLattice_iff (I.rec7 l Z) (a.Q PP ⟨t, hP⟩).k (a.Q PP ⟨t, hP⟩).q PP hidem (I.rec7 l Z).sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX
    (_root_.GlobalTheory.Fam.pk_z W).ΛX 1 hβX _ (a.Q PP ⟨t, hP⟩).FT e.symm a.g.bT hmv' g x hg
  obtain ⟨hsupp, hmat⟩ := hg
  have hM : (Formalism.L2.Theta.mt _ g).map (a.Q PP ⟨t, hP⟩).q.pr * (a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm =
      (a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm * x.val.submatrix e.symm e.symm := by
    have h1 : (Formalism.L2.Theta.mt _ g).map (a.Q PP ⟨t, hP⟩).q.pr = (a.Q PP ⟨t, hP⟩).FT.β * x.val * (a.Q PP ⟨t, hP⟩).FT.γ := hmat
    rw [h1]
    exact GlobalTheory.TopLevQ.moved_mat _ _ (a.Q PP ⟨t, hP⟩).FT.γβ _ e
  have hsupp' : Formalism.L2.Theta.SuppAt (a.Q PP ⟨t, hP⟩).q.e _ (a.g.bT⁻¹ * g * a.g.bT) := GlobalTheory.TopLevQ.suppAt_conj g a.g.bT hsupp
  have hr : (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + ((a.Q PP ⟨t, hP⟩).s + 1) := by
    have := (a.Q PP ⟨t, hP⟩).hs
    unfold Ranks.r
    omega
  have hPg := (_root_.GlobalTheory.PkFrame.pk_frame_places_alt W hW t PP hP 0 (by have := (a.Q PP ⟨t, hP⟩).hs; omega)).2
  have hord := GlobalTheory.TopLevQ.blk_iff e he x.val
  rw [← hr] at hord
  rw [GlobalTheory.TopLevQ.mem_levS_iff]
  have hred := GlobalTheory.TopLevQ.red_eq_zero_iff (a.Q PP ⟨t, hP⟩).q PP hidem (I.rec7 l Z).sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX a.g.bT g _ _ hmv' hM
  constructor
  · rintro ⟨-, ⟨hSt, -, hQt⟩, -⟩
    refine ⟨hx, hord.1 fun i j hij => (hred hSt i j).1 ?_⟩
    exact (hQt PP hP) hij
  · rintro ⟨hx', hmax⟩
    have hSt : Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT) ∈ Formalism.L2.DIV.St (_root_.GlobalTheory.Fam.pk_z W).βX := hStIff.2 hx'
    have hone : ∀ PP' : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E, PP'.under (𝓞 (I.rec7 l Z).host.F) ≠ PP.under (𝓞 (I.rec7 l Z).host.F) →
        Formalism.L2.DIV.redFn (_root_.GlobalTheory.Fam.pk_z W).βX PP' (Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT)) = 1 :=
      fun PP' hne => GlobalTheory.SplitOffRed.redFn_eq_one_off (a.Q PP ⟨t, hP⟩).q hidem _ _ _ hsupp' hSt PP' hne
    refine ⟨hGfC, ⟨hSt, fun PP' hPP' => ?_, fun PP' hPP' => ?_⟩, ?_⟩
    · rw [hone PP' (hPg PP' hPP')]
      exact Subgroup.one_mem _
    · by_cases hPe : PP' = PP
      · subst hPe
        intro i j hij
        exact (hred hSt i j).2 (hord.2 hmax i j hij)
      · rw [hone PP' fun hu => hPe (hW.pk.sel PP' PP ⟨t, hPP'⟩ ⟨t, hP⟩ hu)]
        exact Subgroup.one_mem _
    · have h1 : Formalism.L2.DIV.rTup (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) (Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT)) = 1 := by
        funext PP'
        show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn (_root_.GlobalTheory.Fam.pk_z W).βX PP'.1 _) = 1
        rw [hone PP'.1 (hPg PP'.1 PP'.2)]
        exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
      rw [h1]
      exact Subgroup.one_mem _
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_scalar_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (_root_.GlobalTheory.Fam.chrK_alt W t)), ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.Ix (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.Q PP ⟨t, hP⟩).s + 1)) (Fin (I.rec7 l Z).R.t) ((a.Q PP ⟨t, hP⟩).s + 2)), ∀ g, (ofSplit (a.Q PP ⟨t, hP⟩).q).IsLoc (a.Q PP ⟨t, hP⟩).FT g x → (a.g.bT⁻¹ * g * a.g.bT ∈ levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) ↔ x ∈ ((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).levTop.J) := by
  atlas_forward_decl _root_.GlobalTheory.TopLevQ.mem_levS_top_iff_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QLevAt
theorem qLev_of_reads_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ row col (F : QFam a.v ((a.fam row col).t t)) (h : F.r = J.r), F.χ = _root_.GlobalTheory.Fam.chrK_alt W t → (∀ i, HEq (F.Q i) (J.E (Fin.cast h i)).toAt) → _root_.GlobalTheory.Fam.QLevAlt (a.fam row col) F := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT t J hJ row col F h hχ hQ
  obtain ⟨χ, r, Q, eqv⟩ := F
  dsimp only at h hχ hQ ⊢
  subst hχ
  obtain rfl : Q = fun i => (J.E (Fin.cast h i)).toAt := funext fun i => eq_of_heq (hQ i)
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨Equiv.ofBijective (fun i => ⟨J.pl (Fin.cast h i), J.mem _⟩) ⟨?_, ?_⟩, fun i => ?_⟩
    · intro i i' e
      have e' := hJ.inj (congrArg Subtype.val e)
      exact Fin.ext (by simpa using congrArg Fin.val e')
    · rintro ⟨PP, hPP⟩
      obtain ⟨i, hi⟩ := hJ.surj PP hPP
      exact ⟨Fin.cast h.symm i, Subtype.ext (by simp [hi])⟩
    · obtain ⟨ε, hε, h3⟩ := (J.G (Fin.cast h i)).q.above
      exact ⟨(J.G (Fin.cast h i)).idem,
        (GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G (Fin.cast h i)).idem hε h3).symm⟩
  · intro i j d hd hj x hx
    exact _root_.GlobalTheory.T.true_geometry_twist_value_alt W hW u a ha haT t (J.pl (Fin.cast h i)) (J.mem _) (J.E (Fin.cast h i)) (hJ.res _) j d hd hj x hx
  · intro i x hx g hg
    exact _root_.GlobalTheory.T.true_geometry_twist_scalar_alt W hW u a ha haT t (J.pl (Fin.cast h i)) (J.mem _) (J.E (Fin.cast h i)) x hx g hg
end GlobalTheory.QLevAt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_quadratic_twist_level_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ row col (F : QFam a.v ((a.fam row col).t t)) (h : F.r = J.r), F.χ = _root_.GlobalTheory.Fam.chrK_alt W t → (∀ i, HEq (F.Q i) (J.E (Fin.cast h i)).toAt) → _root_.GlobalTheory.Fam.QLevAlt (a.fam row col) F := by
  atlas_forward_decl _root_.GlobalTheory.QLevAt.qLev_of_reads_alt
end
end
