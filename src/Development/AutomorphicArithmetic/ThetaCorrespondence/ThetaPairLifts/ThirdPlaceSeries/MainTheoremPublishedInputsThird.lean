import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MainTheoremPublishedInputsThird
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MainTheoremPublishedInputsVariant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MainTheoremPublishedResultsFinal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PackB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TruePackOfBundleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TruePackOfBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TruePack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColsStdOfBWit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealAtColsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAtOfBWitStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCastNotMemOfCoprime
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonvanishingFromTruePackStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonvanishingFromTruePack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemberSizesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueDOfTruePack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTheoremFromPublishedResultsAltAltAltAltAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsOfPublishedRepresentationTheoryStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsOfRepresentationTheoryOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FramesExOfRealisation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JoinSubspaceRealDataExistsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ToSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JoinSubspaceRealDataLattice

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.PkOf
section Heq
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef
variable {D : D7}
end Heq
end GlobalTheory.Fam.PkOf
namespace GlobalTheory.Fam
theorem pkHyp_of_real_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin W.R W.S W.Q) → (∀ u, Formalism.L2.SG.ColDict.LevelMatch W.S.X (W.S.tr u) W.S.Y.hK) → GlobalTheory.MiS.DcPtG W.P → _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx W.Q → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation W.Q → _root_.Formalism.IndefR.IndefiniteRealisationExtends W.Q → _root_.Formalism.IndefR.IndefiniteRealisationRecursion W.Q → W.Q.Rl.toRealDat.ExAt → Formalism.IndefR.Links.PrimRows3 W.Q.Rl W.Q.F → W.P.A3.fam3.TypesSep3 → (∃ s, W.P.A3.fam3.Ok3 s) → GlobalTheory.Core.Mi.IdE W.S.X → GlobalTheory.Count.GapGe W.S.X.B (100 * (B.R.r : ℝ) ^ 4) → Formalism.L2.SG.PackageTie2.FinX W.S.Y → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap (I.rec7 l Z) → _root_.GlobalTheory.Fam.ValidRealPackage W → _root_.GlobalTheory.Fam.GeometricFamilyConditions W → _root_.GlobalTheory.Fam.PackageHypotheses W := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hJ hLM hDc hFr hPins hSee hRec hEx hPrim hTS hOk3 hIdE hGap hFinX hNG hTW hTQ
  have hC3 := Formalism.IndefR.Links.RealDat3.characterisation_of_weak W.Q.charW hEx
  have hU : ∀ t : W.P.T, Formalism.IndefR.RecTie.Used0 _ (W.P.I.tup t) := by
    apply Formalism.L2.DIV.tupAllUsed_of_cover
    intro t
    have hmu : W.Q.Rl.mu = W.P.S0.μ :=
      GlobalTheory.Fam.PkOf.mu_of_heq (congrArg (fun Z => W.P.A3.side3 W.P.P0 W.P.ψ0 Z) W.Q.zs) W.Q.s0
    rcases W.Q.charW.tup.mu_used t with h | ⟨w, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨(I.rec7 l Z).plEq.symm w, ?_⟩
      show t = W.P.S0.μ ((I.rec7 l Z).plEq ((I.rec7 l Z).plEq.symm w))
      rw [← hmu, Equiv.apply_symm_apply]
      exact h.symm
  refine ⟨⟨⟨hJ, hLM, hDc, hC3, W.Q.frames hFr⟩, hPins, hSee, hU, hIdE, hGap, hFinX⟩, ?lev, hEx, hRec.hTop, hNG, ?fin, ?sel, ?aa⟩
  case lev =>
    obtain ⟨s, hs⟩ := hOk3
    have hR := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hs hTS W.Q.charW hPrim
    exact ⟨⟨s, hs⟩, hR.ratZ, _, hR.gUnit, hR.gEquiv, hR.h2P, hR.lev0, hR.lev1⟩
  case fin =>
    classical
    have h1 := W.Q.charW.tup.mu_off
    have h2 := W.Q.charW.tup.mu_used
    have : (Set.univ : Set W.P.T) ⊆ insert W.P.A3.A.μ0 (W.Q.Rl.mu '' (W.Q.Rl.twPl : Set _)) := fun t _ => by
      rcases h2 t with h | ⟨w, rfl⟩
      · exact Or.inl h
      · by_cases hw : w ∈ W.Q.Rl.twPl
        · exact Or.inr ⟨w, hw, rfl⟩
        · exact Or.inl (h1 w hw)
    exact Set.finite_univ_iff.1 ((((W.Q.Rl.twPl).finite_toSet.image _).insert _).subset this)
  case sel =>
    rintro PP PP' ⟨t, ht⟩ ⟨t', ht'⟩ hu
    have hs := hTW.ok.sel_ok
    obtain ⟨v, rfl⟩ := GlobalTheory.Fam.PkOf.exists_of_mem_QE ((hTQ.Q t PP).1 ht)
    obtain ⟨v', rfl⟩ := GlobalTheory.Fam.PkOf.exists_of_mem_QE ((hTQ.Q t' PP').1 ht')
    have e1 := congrArg HeightOneSpectrum.asIdeal hu
    have hv : v = v' := by
      apply HeightOneSpectrum.ext
      rw [← hs v, ← hs v']
      exact e1
    rw [hv]
  case aa =>
    intro PP h hmem
    have hcop := (I.rec7 l Z).host.ccK_coprime
    rcases h with ⟨t, ht⟩ | hg | ⟨u, hu⟩
    · apply hPins.qGuard.2 t PP ht
      push_cast
      exact Ideal.mul_mem_left _ _ hmem
    · obtain ⟨plg, iso, -, -, -, -⟩ := hPins.grpRecPin
      set kv := plg.symm ⟨PP, hg⟩ with hkv
      have hPP : ((plg kv : W.Q.Rl.toRealDat.Pg) : Pl (I.rec7 l Z).host.E) = PP := by
        rw [hkv, Equiv.apply_symm_apply]
      have h0 : (((I.rec7 l Z).host.g kv.1 : ℕ) : kP (plg kv).1) = 0 := by
        rw [← map_natCast (iso kv), ZMod.natCast_self, map_zero]
      have hg' : (((I.rec7 l Z).host.g kv.1 : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
        rw [← hPP]
        exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using h0)
      exact GlobalTheory.Fam.PkOf.natCast_not_mem_of_coprime PP
        (hcop _ (by simp [(I.rec7 l Z).host.g_level kv.1])) hg' hmem
    · exact GlobalTheory.Fam.PkOf.natCast_not_mem_of_coprime PP
        (hcop _ (by simp [(I.rec7 l Z).T_level u])) hu hmem
end GlobalTheory.Fam
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem truePack_of_bWit_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → _root_.GlobalTheory.Fam.BundlePointConditions b → _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt b) := by
  intro hL p K q c b hW hX hR
  obtain ⟨hOk, hPins, hTw, hStdC, hTS⟩ := _root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hW
  obtain ⟨hChr, hXi, hQ, hLev, hRec, hRP, hOk3, hIdE, hLM⟩ := _root_.GlobalTheory.T.characters_match_bundle_alt q b hW
  have hTop := _root_.GlobalTheory.T.exists_read_at_packB_of_bWit q b hW hX
  have hTW : _root_.GlobalTheory.Fam.ValidRealPackage (_root_.GlobalTheory.Fam.packB_alt b) := ⟨hOk, hPins, hTw, hStdC, hChr, ⟨1, hTop⟩⟩
  have hTQ : _root_.GlobalTheory.Fam.GeometricFamilyConditions (_root_.GlobalTheory.Fam.packB_alt b) := ⟨hXi, hQ, hTop⟩
  obtain ⟨hRec'⟩ := hRec
  have hPk : _root_.GlobalTheory.Fam.PackageHypotheses (_root_.GlobalTheory.Fam.packB_alt b) := _root_.GlobalTheory.Fam.pkHyp_of_real_alt (_root_.GlobalTheory.Fam.packB_alt b) hR.join hLM hR.dc hR.frames hRP hR.see hRec' hR.ex hR.prim.1 hR.prim.2
    hOk3 hIdE hR.gapS hR.fin hR.gap hTW hTQ
  exact _root_.GlobalTheory.Fam.TruePackAlt.mk _ ⟨hPk, hTW, hTQ, hTS, hLev, ⟨hRec'⟩⟩
end GlobalTheory.Fam
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_pack_of_bundle_witness : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → _root_.GlobalTheory.Fam.BundlePointConditions b → _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt b) := by
  atlas_forward_decl _root_.GlobalTheory.Fam.truePack_of_bWit_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.MiTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
open GlobalTheory.MiTop
namespace GlobalTheory.Fam
theorem trueD_of_truePack_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.TruePackAlt W → GlobalTheory.Core.Rk.TrueD D := by
  intro D L hT Gi Gl Kc Yd cX ex W h
  cases h with
  | mk W hA =>
    obtain ⟨hpk, htr, -, -, -, -⟩ := hA
    obtain ⟨hok, ⟨pins⟩, -, ⟨std⟩, -, -⟩ := htr
    refine ⟨_, _, _, _, _, rfl, ⟨⟨hok, pins, W.R.T.cols, std, ?_⟩⟩⟩
    exact
      { toSTies := W.S.toSTies
        hF := hpk.bot.fin
        tr := W.S.tr
        into := W.S.into
        bij := W.S.bij
        lev := W.S.lev
        colPin := W.S.colPin hpk.bot.fin
        inst := W.S.inst
        locTied := W.S.locTied
        pin := hpk.bot.idE }
end GlobalTheory.Fam
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MiTop
open GlobalTheory.Core.Rk
theorem puNZ_member_alt : GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt b)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.MiTop.PuNZ D) := by
  intro hRow hL p hTP
  have hR := fun Cg CT : ℝ => hRow Cg (1 / 4) 3 (1 / 2) CT (by norm_num) (by norm_num)
  choose Cf Af Bf hC hrow using hR
  have h1 := _root_.GlobalTheory.T.exists_constants_for_parameters_scale_bundle hL p (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
  have h2 := _root_.GlobalTheory.T.degHypL_all_linked_good_members hL p (fun C => Af (C.P.CYL + 1) C.CTu) (fun C => Bf (C.P.CYL + 1) C.CTu)
  have h3 : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p)
      (fun κ _ _ _ _ => Cf (κ.C.P.CYL + 1) κ.C.CTu + 1 ≤ κ.C.CGam) :=
    EvP.mono (fun _ _ _ h _ _ _ _ _ => h) (evP_cGam fun a b => Cf a b + 1)
  refine (((hTP.and h1).and h2).and h3).imp fun κ K β c b hk _ _ h => ?_
  obtain ⟨⟨⟨hT, -, -, -, -, -, -, -, ⟨t1, t2, -, t4, t5⟩, -, hmu, -⟩, hH⟩, hG⟩ := h
  have hD : TrueD β.D := _root_.GlobalTheory.Fam.trueD_of_truePack_alt _ hT
  have hCG : β.O.L.CGam = κ.C.CGam := by rw [← hk.1]; exact β.val.CGam_eq
  have hC1 := hC (κ.C.P.CYL + 1) κ.C.CTu
  refine puNZ_of_sDiag β.O.L hC1 (hCG ▸ hG) hD ⟨t1, t2, hH, t4, t5⟩ hmu fun u => ?_
  exact hrow _ _ _ _ (le_max_left _ _) (le_max_left _ _) β.D _ u (trueE_of_trueD hD)
    ⟨⟨β.O.L, rfl, by rw [hCG]; exact le_max_right _ _, by rw [hCG]; linarith⟩, hmu⟩ ⟨t1, t2, hH, t4, t5⟩
end GlobalTheory.MiTop
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.puNZ_of_truePack : GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt b)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.MiTop.PuNZ D) := by
  atlas_forward_decl _root_.GlobalTheory.MiTop.puNZ_member_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem miStar_row_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), (∀ (K : Ctx) (q : Bl.WPt p.s K), Nonempty (Bl.RXs q.x.what₂)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.BundlePointConditions b) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hDiag hL p hRX hPt
  have hTrue : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt b)) := by
    refine hPt.imp fun κ K β c b _ _ hl hP => ?_
    obtain ⟨q, b', ⟨w⟩, he⟩ := hl
    have key : ∀ s t : (Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c), s = t →
        (_root_.GlobalTheory.Fam.BundlePointConditions t.2.2 → _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt t.2.2)) → _root_.GlobalTheory.Fam.BundlePointConditions s.2.2 → _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt s.2.2) := by
      rintro _ _ rfl h
      exact h
    exact key ⟨β.D, β.O, b⟩ ⟨q.w.D q.Z, q.O, b'⟩ he (fun hP' => _root_.GlobalTheory.T.true_pack_of_bundle_witness q b' w (hRX K q) hP') hP
  have hPu := _root_.GlobalTheory.T.puNZ_of_truePack hDiag hL p hTrue
  refine ((hPt.and hTrue).and hPu).imp fun κ K β c b _ _ _ H => ?_
  exact _root_.GlobalTheory.T.main_theorem_from_published_results_alt_alt_alt_alt_alt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 (_root_.GlobalTheory.Fam.packB_alt b) H.1.2 H.1.1.rS H.2
end GlobalTheory.Fam
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.main_theorem_published_results_final_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), (∀ (K : Ctx) (q : Bl.WPt p.s K), Nonempty (Bl.RXs q.x.what₂)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.BundlePointConditions b) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) := by
  first | exact @_root_.GlobalTheory.Fam.miStar_row_alt_alt | exact _root_.GlobalTheory.Fam.miStar_row_alt_alt | (intros; apply _root_.GlobalTheory.Fam.miStar_row_alt_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.join_subspace_real_data_exists_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : SPack D fun u => (Rc.T.cols.forms u).to0) (S : SRest P) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc (S.toRealSpectralMatching Rc)) (c : ℝ), ∀ n : ℕ, SchurAll D → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y) → Holds x.R x.F → x.A3.fam3.Ok3 n → x.A3.fam3.TypesSep3 → HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (x.A3.indefDown (divisionPairOfAdelicFormsFaceColumnsData x).S1).RR (x.A3.indefDown (divisionPairOfAdelicFormsFaceColumnsData x).S1).XE (divisionPairOfAdelicFormsFaceColumnsData x).I.eRR → RowsHoldDcPt3 (divisionPairOfAdelicFormsFaceColumnsData x) → SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS → EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G (iotaX P.X P.inst).toMulEquiv y.tS c → RowJ x.R.toRealDat x.Y.eE P.X P.inst P.G y.tS S.j → Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin Rc (S.toRealSpectralMatching Rc) (_root_.GlobalTheory.Mem.R3.realisationOfInput y)) ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  first | exact @_root_.GlobalTheory.Mem.KJoinLat.join_subspace_real_data_lattice_alt | exact _root_.GlobalTheory.Mem.KJoinLat.join_subspace_real_data_lattice_alt | (intros; apply _root_.GlobalTheory.Mem.KJoinLat.join_subspace_real_data_lattice_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.PtRowsAt
section General
open NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult
  Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe
section Args
open GlobalTheory.Mem.Top.Bl
variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0}
end Args
set_option maxHeartbeats 1000000 in
theorem see_join_alt (h5 : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX} (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex)
    (P : SPack D fun u => (Rc.T.cols.forms u).to0) (S : SRest P) (S0 : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (hS : S0 = S.toRealSpectralMatching Rc)
    (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S0) (c : ℝ) (hH : Holds x.R x.F) (hP : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y))
    (h : Placed x.R.toRealDat x.F.lv2 x.Y.eE P S y.tS c) :
    _root_.Formalism.IndefR.IndefiniteRealisationExtends (_root_.GlobalTheory.Mem.R3.realisationOfInput y) ∧ Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin Rc S0 (_root_.GlobalTheory.Mem.R3.realisationOfInput y)) := by
  subst hS
  have hSch : SchurAll D := fun V _ S θ M J χ μ 𝓕 =>
    (GlobalTheory.MultFinite.hcFinite_and_schurMult h5.2.2.2.1 h5.2.2.2.2 D θ V S M J χ μ 𝓕).2
  have hL := (GlobalTheory.T.rowLattices_metrics_agree_of_realGroupTheorems h5 D _ _ _ _ x.A3 _ x.R x.F x.cG ex.p0 x.Y x.Z x.pins hH).1
  exact ⟨(_root_.GlobalTheory.Mem.JPin.seeEx_joinPin_alt _ _ _ _ _ _ _ _ _ x Rc P S y c hH h.1 h.2.1 h.2.2).1,
    (_root_.GlobalTheory.T.join_subspace_real_data_exists_alt _ _ _ _ _ _ _ _ _ x Rc P S y c 1 hSch hP hH hH.ok hH.sep hL
      (rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ x).2.1 h.1 h.2.1 h.2.2).1⟩
end General
section Wit
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} {q : Bl.WPt p.s K} {c : ℝ} {b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c}
theorem bundle_P_eq_divisionPair_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : b.P = R3.divisionPairOfAdelicFormsFaceColumnsData w.x := congrArg _root_.GlobalTheory.Mem.Top.Bl.RealPackage.P w.y.eq
theorem dcPtG_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : DcPtG b.P := by
  rw [_root_.GlobalTheory.Fam.PtRowsAt.bundle_P_eq_divisionPair_of_bWit w]
  exact (GlobalTheory.Mem.R3.rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ w.x).2.2.1
theorem realPins_of_bWit' (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q := (_root_.GlobalTheory.T.characters_match_bundle_alt q b w).2.2.2.2.2.1
theorem framesEx_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx b.B.Q := by
  letI := b.B.alg
  exact _root_.GlobalTheory.FramesAtReal.framesEx_of_realisation_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b.B.Q (_root_.GlobalTheory.Fam.PtRowsAt.realPins_of_bWit' w)
theorem prim_links_and_typesSep3_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : Formalism.IndefR.Links.PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3 := by
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => Formalism.IndefR.Links.PrimRows3 r.B.Q.Rl r.B.Q.F ∧ r.P.A3.fam3.TypesSep3) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) :=
    ⟨w.y.intersectionNumber_baseChange.prim, w.y.intersectionNumber_baseChange.sep⟩
  rw [← w.y.eq] at h
  exact h
theorem exAt_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : b.B.Q.Rl.toRealDat.ExAt := by
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => r.B.Q.Rl.toRealDat.ExAt) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) := exAt_of_args w.a w.x w.ax
  rw [← w.y.eq] at h
  exact h
set_option maxHeartbeats 1000000 in
theorem seeEx_and_joinSI_nonempty_of_bWit (h5 : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) :
    _root_.Formalism.IndefR.IndefiniteRealisationExtends b.B.Q ∧ Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin b.R b.S b.B.Q) := by
  obtain ⟨sP, sS, hP, hS, e⟩ := w.s
  have hpin : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => _root_.Formalism.IndefR.IndefiniteRealisationNormalisation r.B.Q) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) := _root_.GlobalTheory.Fam.PtRowsAt.realPins_of_bWit' w
  rw [w.y.eq] at hpin
  have h0 := placed_of_args w.a w.x w.ax q.saturationAtWeightedPoint.P q.saturationAtWeightedPoint.S q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c ⟨q.saturationAtWeightedPoint.see, q.saturationAtWeightedPoint.ev, q.saturationAtWeightedPoint.rowJ⟩
  have ht : w.y.y.tS = q.saturationAtWeightedPoint.t := eq_of_heq w.pt.1
  have hF : (fun u => (b.R.T.cols.forms u).to0) = fun u => (q.x.col.C.forms u).to0 :=
    congrArg (fun C : type_of% q.x.col.C => fun u => (C.forms u).to0) w.recPin.s.cols
  have h1 := Placed.of_heq hF hP hS h0
  rw [← ht] at h1
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => _root_.Formalism.IndefR.IndefiniteRealisationExtends r.B.Q ∧ Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin b.R b.S r.B.Q)) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) :=
    _root_.GlobalTheory.Fam.PtRowsAt.see_join_alt h5 w.x b.R sP sS b.S e w.y.y q.saturationAtWeightedPoint.c w.y.intersectionNumber_baseChange hpin h1
  rw [← w.y.eq] at h
  exact h
end Wit
theorem good_linked_ptR_of_cuspRapidDecay : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.BundlePointConditions b) := by
  intro h1 h2 h3 h4 h5 hL p
  obtain ⟨Cl₀, hnc⟩ := GlobalTheory.Core.Rk.HdNc.hd_nc
  refine (_root_.GlobalTheory.T.exists_constants_for_parameters_scale_bundle hL p (fun _ _ => 0) (fun _ _ => max 1801 Cl₀) (fun _ _ => 0)).imp ?_
  rintro κ K β c b - - ⟨q, b', ⟨w⟩, he⟩ ⟨C', Cl, Cg, CT, -, hCl, -, hHD, -, -, hB, hrS⟩
  have key : ∀ s t : (Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c), s = t →
      (Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin t.2.2.R t.2.2.S t.2.2.B.Q) ∧ DcPtG t.2.2.P ∧ _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx t.2.2.B.Q ∧
        _root_.Formalism.IndefR.IndefiniteRealisationExtends t.2.2.B.Q ∧ t.2.2.B.Q.Rl.toRealDat.ExAt ∧
        (Formalism.IndefR.Links.PrimRows3 t.2.2.B.Q.Rl t.2.2.B.Q.F ∧ t.2.2.P.A3.fam3.TypesSep3)) →
      (Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin s.2.2.R s.2.2.S s.2.2.B.Q) ∧ DcPtG s.2.2.P ∧ _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx s.2.2.B.Q ∧
        _root_.Formalism.IndefR.IndefiniteRealisationExtends s.2.2.B.Q ∧ s.2.2.B.Q.Rl.toRealDat.ExAt ∧
        (Formalism.IndefR.Links.PrimRows3 s.2.2.B.Q.Rl s.2.2.B.Q.F ∧ s.2.2.P.A3.fam3.TypesSep3)) := by
    rintro _ _ rfl h
    exact h
  have hsj := _root_.GlobalTheory.Fam.PtRowsAt.seeEx_and_joinSI_nonempty_of_bWit ⟨h1, h2, h3, h4, h5⟩ w
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := key ⟨β.D, β.O, b⟩ ⟨q.w.D q.Z, q.O, b'⟩ he
    ⟨hsj.2, _root_.GlobalTheory.Fam.PtRowsAt.dcPtG_of_bWit w, _root_.GlobalTheory.Fam.PtRowsAt.framesEx_of_bWit w, hsj.1, _root_.GlobalTheory.Fam.PtRowsAt.exAt_of_bWit w, _root_.GlobalTheory.Fam.PtRowsAt.prim_links_and_typesSep3_of_bWit w⟩
  exact ⟨a1, a2, a3, a4, a5, a6,
    GlobalTheory.Core.Rk.finX_of_gap _ b.S.toSTies (gapHyp_of_hd ((le_max_left _ _).trans hCl) hHD),
    hnc _ _ _ _ _ _ _ _ _ ((le_max_right _ _).trans hCl) hHD b.S.X,
    GlobalTheory.Core.Rk.GapOfNodes.harishChandraNodesFarApart_of_cubic_node_gap _ hB, hrS⟩
end GlobalTheory.Fam.PtRowsAt
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_lines_of_cusp_rapid_decay : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.BundlePointConditions b) := by
  atlas_forward_decl _root_.GlobalTheory.Fam.PtRowsAt.good_linked_ptR_of_cuspRapidDecay
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory
theorem miStarRowClosing_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), (∀ (K : Ctx) (q : Bl.WPt p.s K), Nonempty (Bl.RXs q.x.what₂)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) := by
  intro hHCF hCusp hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG hDSCl hSA hDiag hL p hRX
  exact _root_.GlobalTheory.T.main_theorem_published_results_final_alt_alt hHCF hCusp hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG hDSCl hSA hDiag hL p hRX
    (_root_.GlobalTheory.T.point_lines_of_cusp_rapid_decay hDSC hHCM hCW hHCF hCusp hL p)
end GlobalTheory
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.main_theorem_published_inputs_variant_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), (∀ (K : Ctx) (q : Bl.WPt p.s K), Nonempty (Bl.RXs q.x.what₂)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) := by
  first | exact @_root_.GlobalTheory.miStarRowClosing_alt_alt | exact _root_.GlobalTheory.miStarRowClosing_alt_alt | (intros; apply _root_.GlobalTheory.miStarRowClosing_alt_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory
theorem miStarRow_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun _ _ _ (b : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)) ∧ _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowMultiplicityCondition := by
  intro hHCF hCusp hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG hDSCl hSA hSWU hL N S Γ
  have hE := _root_.GlobalTheory.T.main_theorem_published_inputs_variant_alt_alt hHCF hCusp hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG hDSCl hSA
    (GlobalTheory.T.diagonalRow_of_siegelWeil_unitary hSWU) hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun _ q => ⟨q.x.rx⟩)
  have hr := RowE.row hE
  exact ⟨_root_.GlobalTheory.Fc.RL.LinkedAt.of_row hr,
    _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (hr.imp fun _ _ _ h => GlobalTheory.Fc.FourBoundsAtBundles.evW_of_atAll h)⟩
end GlobalTheory
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.main_theorem_published_inputs_third_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun _ _ _ (b : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)) ∧ _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowMultiplicityCondition := by
  first | exact @_root_.GlobalTheory.miStarRow_alt_alt | exact _root_.GlobalTheory.miStarRow_alt_alt | (intros; apply _root_.GlobalTheory.miStarRow_alt_alt <;> assumption)
end
end
end
