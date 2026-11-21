import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlacedBesselPointsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlacedBesselPoints
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Placed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralAdaptedElementStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralAdaptedElement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotOfPlacedBy
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralAdaptedElementValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralAdaptedElementValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralAdaptedElementPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralAdaptedElementProperty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLocalTypeDataStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedBy
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelTraceAdaptedTranslateStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelTraceAdaptedTranslate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZero

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.Core.Mi.LatMatch
noncomputable section
namespace GlobalTheory.LevZero.StabMatch
variable {D : D7}
set_option maxHeartbeats 2000000 in
theorem exists_center_stab_at_of_transport_correction : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → Framed B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∃ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧ _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a := by
  intro D L hT Gi Gl Kc Yd cX ex W hW u f B hPl hFr a₀ ha₀
  obtain ⟨k, _, _, _, _, ι, v, o, n, G, pl, hc, hv, hVT, hSh, hGP, hGR, hBT⟩ := hPl
  have hbot := _root_.GlobalTheory.LevZero.bot_of_placedBy_alt W hW u f B k ι v o n G pl ⟨hc, hv, hVT, hSh, hGP, hGR, hBT⟩
  obtain ⟨μ, lam, hμ, hl, hz', he, he'⟩ := hFr
  have hF : B.FrameAt μ lam :=
    ⟨hμ, hl, funext fun r => funext fun a => he r a, funext fun r => funext fun a => he' r a, funext fun r => hz' r⟩
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by have := D.R.rS_two; omega
  have hm : 0 < D.R.m := by omega
  have hE : GlobalTheory.Core.Mi.IdE W.S.X := hW.bot.idE
  have hLM := hW.bot.hyp.2.1 u
  have hBa := hBT.adapted
  have hψ : IsStdChar D W.Q.Rl.ψ (-1) := hc.std
  have hb : @Eq (BesAt (f.c.V 0) (f.c.X 0) D.R.rS) (f.c.bes 0 D.R.rS h0) (toBes B) := eq_toBes B _ _ (hBT.lev h0)
  have hΛ : IsSelfDualC (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) := hbot.mem.selfDual
  have hfr : Formalism.L2.DIV.IsFrame ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) := hbot.mem.frame
  obtain ⟨Lm, hLm, hmv⟩ := GlobalTheory.FinPl.GlobImage.image_moves (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) hΛ (f.g.b 0)
  have hloc : ∀ i, LocAt (G i) (pl i).1 (f.g.b 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) := fun i => by
    have := hbot.loc (pl i)
    rwa [Equiv.symm_apply_apply] at this
  have hC := facts o G h0 hc hSh (fun i => (pl i).1) (f.g.b 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) hloc ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) Lm hfr hmv
  rw [hb] at hC
  obtain ⟨M, c1, c2, c3, c4⟩ := hC
  obtain ⟨s1, s2, s3, -, -, s6⟩ := rows_shape hE hF
  obtain ⟨-, z2, -⟩ := GlobalTheory.T.besselLevelLineVector_primitive_rowLattice_norm D W.S.X W.Q.instEq u W.Q.Rl.ψ _ B μ lam hE hF
  have loc : ∀ p : GlobalTheory.FinPl.Pl D, ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) p a ∧ NormOneAt p c ∧
      SMoves (D.sp.Y 0) c (embA B.d B.o (a₀ * a)) Lm (latS D) p := by
    intro p
    by_cases hpg : p ∈ v.gP
    · obtain ⟨i, rfl⟩ := (hGP.places p).1 hpg
      have hpT : (G i).q.v ∉ v.tP := Finset.disjoint_left.1 hv.disj hpg
      obtain ⟨q⟩ : Nonempty (GlobalTheory.LatPair.Unif (G i).k) := inferInstance
      have hϖ := (GlobalTheory.SeeSaw.LevelTest.val_eq_unif (G i).q (hloc i).idem q (hbot.typ.1 (pl i).1 (pl i).2)
        (GlobalTheory.SeeSaw.LevelTest.g_notMem_sq (pl i).1)).trans (GlobalTheory.SeeSaw.LevelTest.unif_val q (G i).S.unif)
      exact loc_level hE hF hLM hBa ha₀ (G i).q (G i).unit _ (by simpa using hϖ) (fun h => hpT ((hVT.tP _).2 h))
        (c4 i).1 hLm (hBT.lat _ hpT) (c4 i).2
    · have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∉ p.asIdeal := by
        intro h
        obtain ⟨PP, ⟨h1, h2⟩, -⟩ := hbot.typ.2 p h
        exact hpg ((hVT.gP p).2 ⟨PP, h1, h2.symm⟩)
      have hpS : p ∉ (_root_.GlobalTheory.BaseChain.com_z W).S := by
        intro h
        obtain ⟨PP, h1, h2⟩ := Finset.mem_image.1 h
        exact hpg ((hVT.gP p).2 ⟨PP, h1, h2.symm⟩)
      have hN : Moves (Yc D 0) (f.g.b 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (v.N 0) (· = p) := hVT.moves 0 hm _ fun p' hp' => hp' ▸ hpg
      obtain ⟨d1, d2, d3, d4⟩ := c1 p
      suffices H : ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) p a ∧ NormOneAt p c ∧
          SMoves (D.sp.Y 0) c (embA B.d B.o (a₀ * a)) (v.N 0) (latS D) p by
        obtain ⟨a, c, h1, h2, h3⟩ := H
        exact ⟨a, c, h1, h2, sMoves_of_moves (S := D.sp.Y 0) hN (hmv _) h3⟩
      refine loc_of_core hψ hE hF hg (hv.sd 0 hm) d1 d2 d3 d4 ?_
      by_cases hpT : p ∈ v.tP
      · have hTv := (hVT.tP p).1 hpT
        obtain ⟨i, rfl⟩ := (hSh.pre.tP p).1 hpT
        obtain ⟨β₀, e1, e2⟩ := c3 i
        have hr : 3 ≤ Fintype.card (Fin (D.sp.X 0).rank) := by
          have h1 := D.R.m_add_three_le_k
          rw [Fintype.card_fin, D.sp.X_rank 0 (Nat.zero_le _), Ranks.N]
          omega
        refine GlobalTheory.T.exists_central_element_homothetic_gluedCores D k (o.p i) _ _ _ B.o B.ζ _ (o.β 0 i) β₀ M _ μ _ o.q (o.Q 0 i) a₀ hr e1 d1 s2 e2 hF.ne (s6 _) z2
          (GlobalTheory.SeeSaw.LevelTest.unifT_of _ _ hTv) fun a ha => ?_
        obtain ⟨y, hy, hU⟩ := GlobalTheory.T.columnLevel_iff_rowLattice_kept_at_place D W.S.X W.Q.instEq u W.Q.Rl.ψ (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) W.S.Y.hK B a₀ hE hLM hBa ha₀ _ hg a ha
        have c5 : (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U ↔ Moves (D.sp.Y 0) (embA B.d B.o a) (v.N 0) (v.N 0) (· = (o.p i).v) :=
          (hBT.trace a (mem_GfC_of_grpAt ha) y hy).1.trans
            ((GlobalTheory.T.mem_chainLevel_iff_carriesLattice_offLevel D (_root_.GlobalTheory.BaseChain.com_z W) 0 (_root_.GlobalTheory.LevZero.levelZeroState W).st hbot.mem _ hpS _
              (conj_mem_grpAt (S := D.sp.Y 0) (embA_mem_grpAt _ _ ha) _)).trans (moves_conj (S := D.sp.Y 0) hN _))
        exact ((GlobalTheory.T.wittCoreEmbedding_stabilises_iff_core_stabilises D _ _ _ B.d _ _ _ _ d2).symm.trans (c5.symm.trans hU)).trans
          (GlobalTheory.T.wittCoreEmbedding_stabilises_iff_core_stabilises D _ _ _ B.d _ _ _ _ (s3 _))
      · obtain ⟨LL, e1, e2⟩ := c2 p hpT
        have hTv : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ p.asIdeal := fun h => hpT ((hVT.tP p).2 h)
        exact GlobalTheory.T.orthogonalSumCores_homothetic_off_level D _ _ _ B.o B.ζ M _ (f.g.x 0).L LL μ _ p a₀ B.line e1 e2
          (rows_trace hE hF hLM hBa ha₀ p (hBT.lat p hpT))
          (GlobalTheory.T.selfDualLattice_splitsOff_unitNormLine_at_place D _ _ _ B.o B.ζ _ μ _ p B.line s2 hF.ne (s6 p) z2 hTv) hF.ne (s6 p) z2 hTv
  obtain ⟨a, haf, hac, z, hz, hmvz⟩ := GlobalTheory.T.exists_central_glue_localHomotheties D (D.sp.Y 0) (D.sp.X 0) (embA B.d B.o) (embA B.d B.o a₀) Lm
    (latS D) hLm s1 (fun v a ha => embA_mem_grpAt _ _ ha) (fun v => by simpa only [map_mul] using loc v)
  rw [← map_mul] at hmvz
  exact ⟨a, haf, hac, stab_of_frame W.S.X W.Q.instEq u ((_root_.GlobalTheory.Fam.pk_z W).βY 0) _ _ z hz
    (GlobalTheory.T.isFrame_finitePart_mul_of_carries_lattice D (D.sp.Y 0) _ ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (latS D) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (moves_trans (hmv _) hmvz) hfr)⟩
end GlobalTheory.LevZero.StabMatch
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_stab_of_transport_correction : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → Framed B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∃ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧ _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a := by
  atlas_forward_decl _root_.GlobalTheory.LevZero.StabMatch.exists_center_stab_at_of_transport_correction
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_local_type_data_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), _root_.GlobalTheory.LevZero.PlacedByLocalGroups f B v o G pl → GlobalTheory.LevZero.Bot (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) (fun PP => G (pl.symm PP)) := by
  first | exact @_root_.GlobalTheory.LevZero.bot_of_placedBy_alt | exact _root_.GlobalTheory.LevZero.bot_of_placedBy_alt | (intros; apply _root_.GlobalTheory.LevZero.bot_of_placedBy_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ColMatchFam
theorem col_level_match_fam_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.LevTraceAlt f B → B.Adapted (W.S.tr u).wt → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ x ∈ GfC (D.sp.X 0), ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o x * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * x * a₀⁻¹) * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u)) ∈ rowJ W.S.X W.Q.instEq) ∧ ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o x * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W → rowChi W.S.X W.Q.instEq (((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * x * a₀⁻¹) * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))) = _root_.GlobalTheory.MiTop.realCharacter W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o x * (show GA D (D.sp.Y 0) from f.g.b 0))) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP u f B hLev hAd a₀ hH0 b hb
  have hE : GlobalTheory.Core.Mi.IdE W.S.X := hP.bot.idE
  have hLM := hP.bot.hyp.2.1 u
  obtain ⟨y, hy⟩ := GlobalTheory.AdForm.RdVal.finM_mem (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) rfl b
  obtain ⟨hU, hchi⟩ := hLev b hb y hy.symm
  have hgf : a₀ * b * a₀⁻¹ ∈ GfC (D.sp.X 0) := mul_mem (mul_mem hH0.1 hb) (inv_mem hH0.1)
  have hRep := GlobalTheory.Core.Mi.FinFrame.repM_toH D W.S.X W.Q.instEq u W.Q.Rl.ψ B (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) hE hAd (a₀ * b * a₀⁻¹)
  have e0 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀ =
      ((W.S.tr u).h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := hH0.2
  have hh0 : (((W.S.tr u).h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) *
      ((W.S.tr u).h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  have hfa : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀⁻¹ =
      (((W.S.tr u).h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) :=
    GlobalTheory.ColMatch.unitaryAdelicPointFiniteMatrix_inv_eq_of_mul_eq_one a₀ _ (by rw [e0]; exact hh0)
  have hfg : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (a₀ * b * a₀⁻¹) =
      (((W.S.tr u).h0 * y * (W.S.tr u).h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := by
    refine (unitaryAdelicPointFiniteMatrix_base_space_mul _ _).trans ((congrArg₂ (· * ·) ((unitaryAdelicPointFiniteMatrix_base_space_mul _ _).trans (congrArg₂ (· * ·) e0 hy.symm)) hfa).trans ?_)
    simp only [Subgroup.coe_mul, Units.val_mul]
  have hRF : Formalism.L2.SG.ColDict.RepF W.S.X (W.S.tr u).wt (W.S.tr u).ιA ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf)
      ((W.S.tr u).h0 * y * (W.S.tr u).h0⁻¹) := by
    have h := hRep
    rw [hfg] at h
    exact h
  obtain ⟨hmemIff, hpsi⟩ := hLM.2 (B.toH (a₀ * b * a₀⁻¹)).2 _ hRF
  have hconj : (W.S.tr u).h0⁻¹ * ((W.S.tr u).h0 * y * (W.S.tr u).h0⁻¹) * (W.S.tr u).h0 = y := by group
  have hfinE : embA B.d B.o (a₀ * b * a₀⁻¹) ∈ GfC (D.sp.Y 0) := GlobalTheory.Core.Mi.CenAct.embA_mem_GfC B.d B.o hgf
  have hfst : (iotaX W.S.X W.Q.instEq (embA B.d B.o (a₀ * b * a₀⁻¹))).1 = 1 :=
    GlobalTheory.Core.Mi.CenAct.iotaX_fst W.Q.instEq hfinE
  have hio : iotaX W.S.X W.Q.instEq (((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * b * a₀⁻¹) *
      (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u)) =
      (1, (W.S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf) * W.S.X.xu u) := by
    rw [map_mul, map_mul, map_inv, (iotaX W.S.X W.Q.instEq).apply_symm_apply]
    ext
    · simp only [Prod.fst_mul, Prod.fst_inv, hfst, mul_one, inv_one]
    · rfl
  have hrow : ∀ k, k ∈ rowJ W.S.X W.Q.instEq ↔
      (iotaX W.S.X W.Q.instEq k).1 = 1 ∧ (iotaX W.S.X W.Q.instEq k).2 ∈ W.S.X.K2 := fun k => Iff.rfl
  have hU' : ∀ hyU : (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U,
      ((((W.S.tr u).h0⁻¹ * ((W.S.tr u).h0 * y * (W.S.tr u).h0⁻¹) * (W.S.tr u).h0 :
        Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
          GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U) := fun hyU => by rw [hconj]; exact hyU
  refine ⟨⟨fun hk => ?_, fun hr => ?_⟩, fun hk => ?_⟩
  · have hm := hmemIff.2 (hU' (hU.2 hk))
    rw [hrow, hio]
    exact ⟨rfl, hm⟩
  · rw [hrow, hio] at hr
    have h2 := hmemIff.1 hr.2
    rw [hconj] at h2
    exact hU.1 h2
  · have hyU := hU.2 hk
    have hm := hmemIff.2 (hU' hyU)
    have hp := hpsi hm (hU' hyU)
    have hc := hchi hyU
    have hchieq : (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi ⟨_, hU' hyU⟩ : ℂˣ) : ℂ) = (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi ⟨_, hyU⟩ : ℂˣ) : ℂ) := by
      have key : ∀ (z : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
          (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (hz : z.1 ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U), z = y →
          (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi ⟨_, hz⟩ : ℂˣ) : ℂ) = (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi ⟨_, hyU⟩ : ℂˣ) : ℂ) := by
        rintro z hz rfl
        rfl
      exact key _ _ hconj
    unfold rowChi
    rw [hio]
    have hpv : ((psiK W.S.X u _ ⟨_, hm⟩ : ℂˣ) : ℂ) =
        W.S.X.chi2 ((W.S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf) * W.S.X.xu u) := rfl
    have hn : ‖W.S.X.chi2 ((W.S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf) * W.S.X.xu u)‖ = 1 :=
      W.S.Y.hK.2.2.2.2 _ hm
    have h1 : W.S.X.chi2 ((W.S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf) * W.S.X.xu u) *
        _root_.GlobalTheory.MiTop.realCharacter W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o b * (show GA D (D.sp.Y 0) from f.g.b 0)) = 1 := by
      rw [← hpv, hp, hchieq]
      exact hc
    generalize W.S.X.chi2 ((W.S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf) * W.S.X.xu u) = c at hn h1 ⊢
    generalize _root_.GlobalTheory.MiTop.realCharacter W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o b * (show GA D (D.sp.Y 0) from f.g.b 0)) = L at h1 ⊢
    have hsc : star c * c = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hn]
      simp
    calc star c = star c * (c * L) := by rw [h1, mul_one]
      _ = (star c * c) * L := by ring
      _ = L := by rw [hsc, one_mul]
end GlobalTheory.ColMatchFam
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_trace_adapted_translate_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.LevTraceAlt f B → B.Adapted (W.S.tr u).wt → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ x ∈ GfC (D.sp.X 0), ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o x * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * x * a₀⁻¹) * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u)) ∈ rowJ W.S.X W.Q.instEq) ∧ ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o x * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W → rowChi W.S.X W.Q.instEq (((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * x * a₀⁻¹) * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))) = _root_.GlobalTheory.MiTop.realCharacter W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o x * (show GA D (D.sp.Y 0) from f.g.b 0))) := by
  atlas_forward_decl _root_.GlobalTheory.ColMatchFam.col_level_match_fam_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.LevZeroMem
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
set_option maxHeartbeats 1000000 in
theorem conj_mem_K_two_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) {v : VCom f.c} (G : (_root_.GlobalTheory.BaseChain.com_z W).Pg → GLoc v)
    (hBot : GlobalTheory.LevZero.Bot (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) G)
    (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hBl : B.lev = f.c.B 0 D.R.rS h0) (hAd : B.Adapted (W.S.tr u).wt) (hTr : _root_.GlobalTheory.MiTop.LevTraceAlt f B)
    (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (W.S.tr u) a₀) (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = f.g.b 0)
    (hs : s = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧
      finE (D.sp.Y 0) κ ∈ St (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0))) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset))
    (hone : ∀ k ∈ levS (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W),
      (∀ PP ∈ (_root_.GlobalTheory.BaseChain.com_z W).Pg, redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) PP (finE (D.sp.Y 0) k) = 1) →
      (iotaX W.S.X W.Q.instEq (s * k * s⁻¹)).2 ∈ W.S.X.K2) :
    ∀ k ∈ levS (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W), (iotaX W.S.X W.Q.instEq (s * k * s⁻¹)).2 ∈ W.S.X.K2 := by
  have hemb : ∀ b, embA B.d B.o b = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o b : GA D (D.sp.Y 0)) := fun b =>
    by
      have h1 := congr_arg_heq (fun L : BesLev D D.R.rS => (embA L.d L.o : GA D L.A →* GA D L.V)) hBl
      have h2 : embA B.d B.o = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o : GA D (D.sp.X 0) →* GA D (D.sp.Y 0)) :=
        eq_of_heq h1
      exact DFunLike.congr_fun h2 b
  have hfl : flagN B.d = (flagN (f.c.bes 0 D.R.rS h0).d : Subgroup (GA D (D.sp.Y 0))) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => flagN L.d) hBl)
  refine GlobalTheory.T.indexZeroLevel_generated_by_local_unipotents (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) G h0 hBot
    (fun k : GA D (D.sp.Y 0) => (iotaX W.S.X W.Q.instEq (s * k * s⁻¹)).2 ∈ W.S.X.K2) ?_ ?_ ?_ hone
  · intro (k : GA D (D.sp.Y 0)) _ (k' : GA D (D.sp.Y 0)) _ q q'
    show (iotaX W.S.X W.Q.instEq (s * (k * k') * s⁻¹)).2 ∈ W.S.X.K2
    have e : s * (k * k') * s⁻¹ = (s * k * s⁻¹) * (s * k' * s⁻¹) := by group
    rw [e, map_mul, Prod.snd_mul]
    exact W.S.Y.hK.2.1 _ q _ q'
  · intro PP (n : GA D (D.sp.Y 0)) q hn _ _ hk
    have hn' : n ∈ flagN B.d := by rw [hfl]; exact hn
    have e : s * (t⁻¹ * n * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        (embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      rw [hs]; group
    have hk' : t⁻¹ * n * t ∈ levS (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) := by rw [ht]; exact hk
    have hKs := ((hSt (s * (t⁻¹ * n * t) * s⁻¹)).1 ⟨GlobalTheory.MemMatch.conj_mem_GfC W.S.X W.Q.instEq s _ hk'.1, by
      rw [map_mul, map_mul, map_inv, GlobalTheory.FrameConj.conj_mem_St_iff]; exact parLev_St hk'.2.1⟩).2
    have hN := ((B.tieN _).1 (GlobalTheory.CharLaws.embA_conj_mem B.d B.o (a₀ * a) hn')).2
    have goal : (iotaX W.S.X W.Q.instEq (s * (t⁻¹ * n * t) * s⁻¹)).2 ∈ W.S.X.K2 := by
      rw [e] at hKs ⊢
      generalize embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹ = n' at hN hKs ⊢
      rw [map_mul, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply] at hKs ⊢
      generalize iotaX W.S.X W.Q.instEq n' = y at hN hKs ⊢
      change (W.S.X.xu u)⁻¹ * y.2 * W.S.X.xu u ∈ _ at hKs ⊢
      refine Formalism.L2.SG.Pf.unipotent_conj_mem_level hN ?_
      have := Formalism.L2.SG.Pf.unitaryCongruence.K_mul _ (Formalism.L2.SG.Pf.unitaryCongruence.K_mul _ (W.S.X.xu_K u) hKs)
        (Formalism.L2.SG.Pf.unitaryCongruence.K_inv _ (W.S.X.xu_K u))
      rwa [show W.S.X.xu u * ((W.S.X.xu u)⁻¹ * y.2 * W.S.X.xu u) * (W.S.X.xu u)⁻¹ = y.2 by group] at this
    subst ht
    exact goal
  · intro b hb hk
    rw [← hemb b] at hk
    have h1 := (_root_.GlobalTheory.T.level_trace_adapted_translate_alt W hPk u f B hTr hAd a₀ hH0 b hb).1.1 hk
    have hab : a * b * a⁻¹ = b := by rw [← Subgroup.mem_center_iff.1 hac b]; group
    have e : s * (t⁻¹ * embA B.d B.o b * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        embA B.d B.o (a₀ * b * a₀⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      have : a₀ * b * a₀⁻¹ = (a₀ * a) * b * (a₀ * a)⁻¹ := by
        conv_lhs => rw [← hab]
        group
      rw [this, map_mul _ _ (a₀ * a)⁻¹, map_mul _ (a₀ * a) b, map_inv, hs]; group
    rw [← e] at h1
    rw [← hemb b]
    subst ht
    exact h1.2
set_option maxHeartbeats 2000000 in
theorem mem_K_two_iff_of_family_character (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) {v : VCom f.c} (G : (_root_.GlobalTheory.BaseChain.com_z W).Pg → GLoc v)
    (hBot : GlobalTheory.LevZero.Bot (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) G)
    (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hBl : B.lev = f.c.B 0 D.R.rS h0) (hAd : B.Adapted (W.S.tr u).wt) (hTr : _root_.GlobalTheory.MiTop.LevTraceAlt f B)
    (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (W.S.tr u) a₀) (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = f.g.b 0)
    (hs : s = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧
      finE (D.sp.Y 0) κ ∈ St (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0))) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset))
    (κ : GA D (D.sp.Y 0)) (hκ : κ ∈ GfC (D.sp.Y 0))
    (hκS : finE (D.sp.Y 0) κ ∈ St (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0))) :
    (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.K2 ↔
      rTup (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0)) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈
        (_root_.GlobalTheory.LevZero.datZero_alt W).P.H := by
  obtain ⟨hr, ξ, hL⟩ := hBot.mem.lev
  obtain ⟨N, hN, -⟩ := hBot.mem.base
  have hrk : (D.sp.Y 0).rank = D.R.rankY 0 := hBot.mem.rank
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by rw [hrk]; simp [Formalism.BasicNotions.Ranks.rankY]
  have hr' : D.R.r ≤ (D.sp.Y 0).rank := hr
  have hLb : _root_.GlobalTheory.LevZero.datZero_alt W = (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr' (_root_.GlobalTheory.BaseChain.com_z W).Pg ∅
      (_root_.GlobalTheory.BaseChain.com_z W).P (_root_.GlobalTheory.BaseChain.com_z W).chi ξ Frm.B) := hL
  have hlift : Lev.LiftsExist (D.sp.Y 0) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) :=
    GlobalTheory.ChainOnto.FlagAct.liftsExist_stage hBot.com hBot.mem
  obtain ⟨m, hm⟩ := GlobalTheory.MemMatch.exists_read W.S.X W.Q.instEq (_root_.GlobalTheory.BaseChain.com_z W).Pg hBot.typ hBot.com.split
    (fun PP => ⟨_, (hBot.loc PP).idem⟩) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) N hN s hSt
  have hin := _root_.GlobalTheory.LevZeroMem.conj_mem_K_two_alt W hPk f B G hBot h0 hBl hAd hTr a₀ hH0 a hac t s ht hs hSt (fun k hk h1 =>
    (hm k hk.1 (parLev_St hk.2.1)).2 fun PP => by rw [h1 PP.1 PP.2, mul_one, mul_inv_cancel]; exact one_mem _)
  have hpat : ∀ g : ∀ PP : (_root_.GlobalTheory.BaseChain.com_z W).Pg, GL (Fin D.R.r) (kP PP.1),
      g ∈ (_root_.GlobalTheory.BaseChain.com_z W).P.H ↔ ∀ PP, GlobalTheory.SymRes.IsPat D.R.rS D.R.k (g PP) :=
    fun g => (hBot.grp g).trans (forall_congr' fun PP => GlobalTheory.LevZero.exists_red_iff_isPat (G PP) PP.1 (hBot.loc PP).idem (g PP))
  rw [hLb] at hlift hin ⊢
  have hlev : ∀ k ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) k ∈ St (F := D.host.F) (E := D.host.E) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) →
      (fun PP : (_root_.GlobalTheory.BaseChain.com_z W).Pg => upperLeftBlock hr' (redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) PP.1 (finE (D.sp.Y 0) k))) ∈ (_root_.GlobalTheory.BaseChain.com_z W).P.H →
      k ∈ levS (D.sp.Y 0) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr' (_root_.GlobalTheory.BaseChain.com_z W).Pg ∅
        (_root_.GlobalTheory.BaseChain.com_z W).P (_root_.GlobalTheory.BaseChain.com_z W).chi ξ Frm.B) := by
    intro k hk hS hP
    refine ⟨hk, ?_⟩
    show finE (D.sp.Y 0) k ∈ lev _ _ _ _
    rw [mem_lev, mem_parLev]
    exact ⟨⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hS, fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ hn _,
      fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, hP⟩
  obtain ⟨k₀, rfl⟩ : ∃ k₀, κ = s * k₀ * s⁻¹ := ⟨s⁻¹ * κ * s, by group⟩
  have hk₀ : k₀ ∈ GfC (D.sp.Y 0) := by
    have := GlobalTheory.MemMatch.conj_mem_GfC W.S.X W.Q.instEq s⁻¹ _ hκ
    rwa [show s⁻¹ * (s * k₀ * s⁻¹) * s⁻¹⁻¹ = k₀ by group] at this
  have hfe : finE (D.sp.Y 0) (s * k₀ * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k₀ * (finE (D.sp.Y 0) s)⁻¹ := by rw [map_mul, map_mul, map_inv]
  rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at hκS
  rw [hfe, GlobalTheory.FrameConj.rTup_conj]
  refine ⟨fun hK => ?_, fun hP => hin k₀ (hlev k₀ hk₀ hκS hP)⟩
  refine (hpat _).2 fun PP => (GlobalTheory.MemMatch.isIdentityOffFreePositions_rightBlock_iff _ _ hr' hn _).2 ?_
  haveI : Finite (kP PP.1) := Ideal.finiteQuotientOfFreeOfNeBot PP.1.asIdeal PP.1.ne_bot
  have hrr : (D.sp.Y 0).rank = D.R.k + (2 * D.R.rS + 1) := by
    have := le_antisymm hn hr'
    have h0' := h0
    unfold Ranks.r at this
    omega
  refine GlobalTheory.SymResCount.conj_pat_onto (kP PP.1) _ D.R.rS D.R.k hrr (m PP) (fun g hg => ?_) _ ((hm k₀ hk₀ hκS).1 hK PP)
  let g0 : ∀ Q : (_root_.GlobalTheory.BaseChain.com_z W).Pg, GL (Fin D.R.r) (kP Q.1) := Function.update (fun _ => 1) PP (upperLeftBlock hr' g)
  have hg0 : g0 ∈ (_root_.GlobalTheory.BaseChain.com_z W).P.H := (hpat _).2 fun Q => by
    by_cases hQ : Q = PP
    · subst hQ
      simp only [g0, Function.update_self]
      exact (GlobalTheory.MemMatch.isIdentityOffFreePositions_rightBlock_iff _ _ hr' hn _).2 hg
    · simp only [g0, Function.update_of_ne hQ]
      exact GlobalTheory.SymRes.isPat_one _ _
  obtain ⟨k, hk, hkp, hkr⟩ := hlift g0
  have hkr' : (fun PP : (_root_.GlobalTheory.BaseChain.com_z W).Pg => upperLeftBlock hr' (redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) PP.1 (finE (D.sp.Y 0) k))) = g0 := hkr
  have h1 := (hm k hk (parLev_St hkp)).1 (hin k (hlev k hk (parLev_St hkp) (hkr' ▸ hg0))) PP
  have h2 : redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) PP.1 (finE (D.sp.Y 0) k) = g :=
    GlobalTheory.MemMatch.reductionBlock_injective_of_eq hr' hn _ _ ((congrFun hkr' PP).trans (Function.update_self _ _ _))
  rwa [h2] at h1
set_option maxHeartbeats 2000000 in
theorem mem_rowJ_iff_rTup_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → (κ ∈ rowJ W.S.X W.Q.instEq ↔ Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H) := by
  intro D L hT Gi Gl Kc Yd cX ex W hPk u f B hPl a₀ hH0 a _ hac hStab κ hκ hκS
  obtain ⟨k, _, _, _, _, ι, v, o, n, G, pl, hc, hv, hvt, hsh, hpin, hread, hbt⟩ := hPl
  have hBot := _root_.GlobalTheory.T.bessel_local_type_data_alt W hPk u f B k ι v o n G pl ⟨hc, hv, hvt, hsh, hpin, hread, hbt⟩
  have h0 := h0_eq D
  have hκ1 : (iotaX W.S.X W.Q.instEq κ).1 = 1 := (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff W.S.X W.Q.instEq κ).2 hκ
  show (iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.K2 ↔ _
  exact (and_iff_right hκ1).trans (_root_.GlobalTheory.LevZeroMem.mem_K_two_iff_of_family_character W hPk f B _ hBot h0 (hbt.lev h0) hbt.adapted hbt.trace a₀ hH0 a hac _ _ rfl rfl
    hStab κ hκ hκS)
end GlobalTheory.LevZeroMem
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_adapted_element_property_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → (κ ∈ rowJ W.S.X W.Q.instEq ↔ Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H) := by
  atlas_forward_decl _root_.GlobalTheory.LevZeroMem.mem_rowJ_iff_rTup_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.LevZeroChr
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
set_option maxHeartbeats 1000000 in
theorem rowChi_conj_of_mem_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (hPl : _root_.GlobalTheory.MiTop.PlacedAlt f B) (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (W.S.tr u) a₀)
    (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = f.g.b 0)
    (hs : s = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (hβ : β = (_root_.GlobalTheory.Fam.pk_z W).βY 0)
    (Lz : Formalism.L2.DIV.LevDat D.host.E ℂ (D.sp.Y 0).rank) (hLz : Lz = _root_.GlobalTheory.LevZero.datZero_alt W)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β)) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset))
    (hmem : ∀ k ∈ levS (D.sp.Y 0) β Lz, s * k * s⁻¹ ∈ rowJ W.S.X W.Q.instEq) :
    ∀ k ∈ levS (D.sp.Y 0) β Lz, rowChi W.S.X W.Q.instEq (s * k * s⁻¹) = levChi (D.sp.Y 0) β Lz k := by
  obtain ⟨kk, i1, i2, i3, i4, ι, v, o, n, G, pl, hcis, hvis, htie, hshape, hpin, hread, hbot⟩ := hPl
  have hBot := _root_.GlobalTheory.T.bessel_local_type_data_alt W hW u f B kk ι v o n G pl ⟨hcis, hvis, htie, hshape, hpin, hread, hbot⟩
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  have hBl := hbot.lev h0
  have hE : GlobalTheory.Core.Mi.IdE W.S.X := hW.bot.idE
  have hTP : GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.BaseChain.com_z W).Pg := hBot.typ
  have hemb : ∀ b, embA B.d B.o b = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o b : GA D (f.c.V 0)) := fun b =>
    by
      have h1 := congr_arg_heq (fun L : BesLev D D.R.rS => (embA L.d L.o : GA D L.A →* GA D L.V)) hBl
      have h2 : embA B.d B.o = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o : GA D (D.sp.X 0) →* GA D (f.c.V 0)) :=
        eq_of_heq h1
      exact DFunLike.congr_fun h2 b
  have hfl : flagN B.d = (flagN (f.c.bes 0 D.R.rS h0).d : Subgroup (GA D (f.c.V 0))) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => flagN L.d) hBl)
  have hps : psiBes W.Q.Rl.ψ B.d 1 (vecB B.o B.ζ) =
      (psiBes f.c.ψ (f.c.bes 0 D.R.rS h0).d 1 (vecB (f.c.bes 0 D.R.rS h0).o (f.c.bes 0 D.R.rS h0).ζ) : GA D (f.c.V 0) → ℂ) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => psiBes W.Q.Rl.ψ L.d 1 (vecB L.o L.ζ)) hBl)
  have hred : ∀ (PP : Formalism.L2.DIV.Pl D.host.E) (k : GA D (D.sp.Y 0)),
      redFn (finE (D.sp.Y 0) s * β) PP (finE (D.sp.Y 0) (s * k * s⁻¹)) = redFn β PP (finE (D.sp.Y 0) k) := fun PP k => by
    rw [map_mul, map_mul, map_inv, GlobalTheory.FrameConj.redFn_conj]
  subst hβ hLz
  refine GlobalTheory.T.indexZeroLevel_generated_by_local_unipotents (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) (fun PP => G (pl.symm PP)) h0 hBot
    (fun k : GA D (D.sp.Y 0) => rowChi W.S.X W.Q.instEq (s * k * s⁻¹) =
      levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) k) ?_ ?_ ?_ ?_
  · intro (k : GA D (D.sp.Y 0)) hk (k' : GA D (D.sp.Y 0)) hk' q q'
    show rowChi W.S.X W.Q.instEq (s * (k * k') * s⁻¹) = levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) (k * k')
    have e : s * (k * k') * s⁻¹ = (s * k * s⁻¹) * (s * k' * s⁻¹) := by group
    have q₁ : rowChi W.S.X W.Q.instEq (s * k * s⁻¹) = levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) k := q
    have q₂ : rowChi W.S.X W.Q.instEq (s * k' * s⁻¹) = levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) k' := q'
    rw [GlobalTheory.ChrMatch.levChi_mul (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) hk hk', ← q₁, ← q₂, e, rowChi, rowChi, rowChi,
      map_mul, Prod.snd_mul, W.S.Y.hK.2.2.2.1 _ (hmem k hk).2 _ (hmem k' hk').2, star_mul']
  · intro PP (n : GA D (D.sp.Y 0)) q hn hq hl hk
    have h2 := GlobalTheory.T.indexZeroLevelCharacter_eq_besselCharacter (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) (fun PP => G (pl.symm PP)) h0 hBot
      PP n q hq hl hk
    have hn' : n ∈ flagN B.d := by rw [hfl]; exact hn
    have e : s * (t⁻¹ * n * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        (embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      rw [hs]; group
    have hj := hmem (t⁻¹ * n * t) (by rw [ht]; exact hk)
    rw [e] at hj
    have h1 := GlobalTheory.RowBesChar.rowChi_conj_eq_psiBes D W.S.X W.Q.instEq u W.Q.Rl.ψ _ B hE PP.1 (G (pl.symm PP)).q.e
      (G (pl.symm PP)).q.split (hBot.loc PP).idem (hTP.1 PP.1 PP.2) _
      (GlobalTheory.CharLaws.embA_conj_mem B.d B.o (a₀ * a) hn') (GlobalTheory.ChrMatch.suppAt_conj _ _ _ _ hl.1) hj
    subst ht
    show rowChi W.S.X W.Q.instEq
      (s * ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * n * (show GA D (D.sp.Y 0) from f.g.b 0)) * s⁻¹) = _
    refine (congrArg _ e).trans (h1.trans (Eq.trans ?_ h2.symm))
    rw [GlobalTheory.CharLaws.psiBes_conj]
    exact congrFun hps n
  · intro (b : GA D (D.sp.X 0)) hb hk
    have hk' : (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o b * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W := by
      rw [hemb b]; exact hk
    have h1 := (_root_.GlobalTheory.T.level_trace_adapted_translate_alt W hW u f B hbot.trace hbot.adapted a₀ hH0 b hb).2 hk'
    have hab : a * b * a⁻¹ = b := by rw [← Subgroup.mem_center_iff.1 hac b]; group
    have e : s * (t⁻¹ * embA B.d B.o b * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        embA B.d B.o (a₀ * b * a₀⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      have : a₀ * b * a₀⁻¹ = (a₀ * a) * b * (a₀ * a)⁻¹ := by
        conv_lhs => rw [← hab]
        group
      rw [this, map_mul _ _ (a₀ * a)⁻¹, map_mul _ (a₀ * a) b, map_inv, hs]; group
    subst ht
    have h3 := (congrArg (rowChi W.S.X W.Q.instEq) e).trans h1
    rw [hemb b] at h3
    exact h3
  · intro (k : GA D (D.sp.Y 0)) hk hr1
    show rowChi W.S.X W.Q.instEq (s * k * s⁻¹) = levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) k
    rw [GlobalTheory.PrinFrame.rowChi_eq_one D W.S.X W.Q.instEq hE (_root_.GlobalTheory.BaseChain.com_z W).Pg hTP hBot.com.split _ hSt _ (hmem k hk)
      (fun PP hPP => (hred PP k).trans (hr1 PP hPP))]
    exact (GlobalTheory.ChrMatch.levChi_of_red_one _ _ _ rfl rfl hr1).symm
set_option maxHeartbeats 1000000 in
theorem row_character_eq_extension_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H → κ ∈ rowJ W.S.X W.Q.instEq → rowChi W.S.X W.Q.instEq κ = ((Formalism.L2.DIV.ext1 (_root_.GlobalTheory.LevZero.datZero_alt W).P.H (_root_.GlobalTheory.LevZero.datZero_alt W).P.chi (Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ)) : ℂˣ) : ℂ) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW u f B hPl a₀ hH0 a ha hac hSt κ hκ hκS hP _
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by
    have := GlobalTheory.Chain.StepVac.rank_Yc (D := D) (j := 0) (Nat.zero_le _)
    exact le_of_eq (this.trans (by simp))
  have hM := _root_.GlobalTheory.T.central_adapted_element_property_alt W hW u f B hPl a₀ hH0 a ha hac hSt
  obtain ⟨β, hβ⟩ : ∃ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D), β = (_root_.GlobalTheory.Fam.pk_z W).βY 0 := ⟨_, rfl⟩
  obtain ⟨Lz, hLz⟩ : ∃ Lz : Formalism.L2.DIV.LevDat D.host.E ℂ (D.sp.Y 0).rank, Lz = _root_.GlobalTheory.LevZero.datZero_alt W := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = _root_.GlobalTheory.MiTop.translationElement f B a₀ a := ⟨_, rfl⟩
  have hfr : _root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a = finE (D.sp.Y 0) s * β := by rw [hs, hβ]; rfl
  have hSt' : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β)) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset) := by
    rw [← hfr]; exact hSt
  have key := _root_.GlobalTheory.LevZeroChr.rowChi_conj_of_mem_alt W hW u f B hPl a₀ hH0 a hac _ s rfl hs β hβ Lz hLz hSt'
  have hM' : ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β) →
      rTup (finE (D.sp.Y 0) s * β) Lz (finE (D.sp.Y 0) κ) ∈ Lz.P.H → κ ∈ rowJ W.S.X W.Q.instEq := by
    rw [← hfr, hLz]; exact fun κ h1 h2 h3 => (hM κ h1 h2).2 h3
  have hκS' : finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β) := by rw [← hfr]; exact hκS
  have hP' : rTup (finE (D.sp.Y 0) s * β) Lz (finE (D.sp.Y 0) κ) ∈ Lz.P.H := by rw [← hfr, hLz]; exact hP
  suffices hgoal : rowChi W.S.X W.Q.instEq κ =
      ((ext1 Lz.P.H Lz.P.chi (rTup (finE (D.sp.Y 0) s * β) Lz (finE (D.sp.Y 0) κ)) : ℂˣ) : ℂ) by
    rw [← hfr, hLz] at hgoal; exact hgoal
  have e1 : Lz.s = 0 := by rw [hLz]; rfl
  have e2 : Lz.Q = ∅ := by rw [hLz]; rfl
  have e3 : (D.sp.Y 0).rank ≤ Lz.r := by rw [hLz]; exact hn
  clear hκS hP hM hSt hfr hs hβ hLz
  have hfin : ∀ s k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) → s * k * s⁻¹ ∈ GfC (D.sp.Y 0) := fun s k hk => by
    rw [← GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff W.S.X W.Q.instEq] at hk ⊢
    rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, hk, mul_one, Prod.fst_inv, mul_inv_cancel]
  have hfe : ∀ k : GA D (D.sp.Y 0), finE (D.sp.Y 0) (s * k * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k * (finE (D.sp.Y 0) s)⁻¹ := fun k => by rw [map_mul, map_mul, map_inv]
  have hmem : ∀ k ∈ levS (D.sp.Y 0) β Lz, s * k * s⁻¹ ∈ rowJ W.S.X W.Q.instEq := by
    intro k hk
    obtain ⟨hf, hl⟩ := hk
    change finE (D.sp.Y 0) k ∈ lev _ _ _ _ at hl
    rw [mem_lev, mem_parLev] at hl
    have hs' : finE (D.sp.Y 0) (s * k * s⁻¹) ∈ St (finE (D.sp.Y 0) s * β) := by
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff]; exact hl.1.2.1
    refine hM' _ (hfin s k hf) hs' ?_
    rw [hfe, GlobalTheory.FrameConj.rTup_conj]
    exact hl.2
  obtain ⟨k₀, rfl⟩ : ∃ k₀, κ = s * k₀ * s⁻¹ := ⟨s⁻¹ * κ * s, by group⟩
  rw [hfe, GlobalTheory.FrameConj.rTup_conj] at hP' ⊢
  have hk₀ : k₀ ∈ levS (D.sp.Y 0) β Lz := by
    refine ⟨?_, ?_⟩
    · have := hfin s⁻¹ _ hκ
      rwa [show s⁻¹ * (s * k₀ * s⁻¹) * s⁻¹⁻¹ = k₀ by group] at this
    · show finE (D.sp.Y 0) k₀ ∈ lev _ _ _ _
      rw [mem_lev, mem_parLev]
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at hκS'
      exact ⟨⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hκS', fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ e3 _,
        fun PP hPP => absurd (e2 ▸ hPP) (Finset.notMem_empty _)⟩, hP'⟩
  refine (key hmem k₀ hk₀).trans ?_
  unfold levChi levFn
  simp only [e1, e2, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
end GlobalTheory.LevZeroChr
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_adapted_element_value_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H → κ ∈ rowJ W.S.X W.Q.instEq → rowChi W.S.X W.Q.instEq κ = ((Formalism.L2.DIV.ext1 (_root_.GlobalTheory.LevZero.datZero_alt W).P.H (_root_.GlobalTheory.LevZero.datZero_alt W).P.chi (Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ)) : ℂˣ) : ℂ) := by
  atlas_forward_decl _root_.GlobalTheory.LevZeroChr.row_character_eq_extension_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem exists_isAt_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → GlobalTheory.MiTop.Framed B → ∃ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a := by
  intro D L hT Gi Gl Kc Yd cX ex W hW u f B hP hF
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.Core.Mi.PinModel.exists_transport_adelic_correction (W.S.tr u)
  obtain ⟨a, haf, hac, hSt⟩ := _root_.GlobalTheory.T.exists_central_stab_of_transport_correction W hW u f B hP hF a₀ ha₀
  have hM := _root_.GlobalTheory.T.central_adapted_element_property_alt W hW u f B hP a₀ ha₀ a haf hac hSt
  have hC := _root_.GlobalTheory.T.central_adapted_element_value_alt W hW u f B hP a₀ ha₀ a haf hac hSt
  have hb : (show GA D (D.sp.Y 0) from f.g.b 0) ∈ GfC (D.sp.Y 0) := by
    obtain ⟨k, _, _, _, _, ι, v, o, n, G, pl, -, hv, ht, -⟩ := hP
    have h1 := hv.b 0
    rw [ht.b 0] at h1
    exact h1
  have hx : (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) ∈ GfC (D.sp.Y 0) :=
    (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff W.S.X W.Q.instEq _).1 (by simp)
  have htf : _root_.GlobalTheory.MiTop.translationElement f B a₀ a ∈ GfC (D.sp.Y 0) :=
    mul_mem (mul_mem (inv_mem hx) (GlobalTheory.Core.Mi.CenAct.embA_mem_GfC B.d B.o (mul_mem ha₀.1 haf))) hb
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by
    rw [rank_eq W.S.X W.Q.instEq, W.S.X.n_eq]
  refine ⟨a₀, a, ha₀, haf, hac, htf, fun κ => ?_⟩
  rw [inv_inv]
  have h1 := GlobalTheory.FrameConj.levS_conj_frame (D.sp.Y 0) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from _root_.GlobalTheory.LevZero.datZero_alt W) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a) htf κ
  generalize _root_.GlobalTheory.MiTop.translationElement f B a₀ a * κ * (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)⁻¹ = y at h1 ⊢
  obtain ⟨h2, h3⟩ := oneBlock_lev (D.sp.Y 0) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from _root_.GlobalTheory.LevZero.datZero_alt W) hn rfl rfl y
  have h4 : κ ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ y ∈ levS (D.sp.Y 0) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from _root_.GlobalTheory.LevZero.datZero_alt W) := h1.1
  have h5 : Lev.levChi (D.sp.Y 0) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from _root_.GlobalTheory.LevZero.datZero_alt W) y = _root_.GlobalTheory.MiTop.realCharacter W κ := h1.2
  rw [h2] at h4
  refine ⟨h4.trans ⟨fun h => (hM y h.1 h.2.1).2 h.2.2, fun h => ?_⟩, fun hk => ?_⟩
  · obtain ⟨hf, hs⟩ := (hSt y).2 ⟨h.1, h.2.1⟩
    exact ⟨hf, hs, (hM y hf hs).1 h⟩
  · obtain ⟨hf, hs, hp⟩ := h4.1 hk
    exact (hC y hf hs hp ((hM y hf hs).2 hp)).trans (h3.symm.trans h5)
end GlobalTheory.MiTop
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isAt_of_placed_framed : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → GlobalTheory.MiTop.Framed B → ∃ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a := by
  atlas_forward_decl _root_.GlobalTheory.MiTop.exists_isAt_alt
end
end
