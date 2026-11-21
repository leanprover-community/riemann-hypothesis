import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CanonicalAnalyticData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXTyped
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXHaarPos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.UnipotentIntegralInLevel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.EvalVOpen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptedBasisEveryPlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MSTypP
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MassDataPosAllOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DvPosC

section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace Formalism.L2.SG.Pf.MassDataX

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)

theorem comp_set_conjugated_level_eq : compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 =
    (fun z => PIW.MassDataColumns.xuP X hb u p * z * (PIW.MassDataColumns.xuP X hb u p)⁻¹) '' MassDataIdxSteps.KppX X hb p := by
  unfold MassDataIdxSteps.KppX compSet K2u
  rw [Set.image_image, Set.image_image]
  refine Set.image_congr fun y _ => ?_
  simp only [map_mul, map_inv]

theorem mem_compSet_iff (x : PIW.MassDataColumns.KvH X u p.1) :
    ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈
        compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 ↔
      x ∈ (PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1).subgroupOf (PIW.MassDataColumns.KvH X u p.1) := by
  rw [PIW.MassDataColumns.mem_K2Hp_iff X hb (Formalism.L2.SG.Closed.level_subgroup_is_group X) (Formalism.L2.SG.Closed.level_subgroup_properties X) u p x,
    comp_set_conjugated_level_eq]
  constructor
  · rintro ⟨z, hz, hzx⟩
    rw [← hzx]
    simpa [mul_assoc] using hz
  · intro h
    exact ⟨_, h, by group⟩

theorem idxHp_eq : MassDataLevelSSteps.idxHp X hb u p = PIW.MassDataColumns.lIdxH X hb u p := by
  have hKv : ∀ y : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u), (y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 ↔ y ∈ PIW.MassDataColumns.KvH X u p.1 :=
    fun y => Iff.rfl
  have hC2 : Subgroup.closure (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) = PIW.MassDataColumns.KvH X u p.1 := by
    have e : (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) = (PIW.MassDataColumns.KvH X u p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) :=
      Set.ext hKv
    rw [e, Subgroup.closure_eq]
  have hS : ∀ y : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u), (y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 →
      y ∈ PIW.MassDataColumns.KvH X u p.1 ∧ y ∈ PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1 := by
    intro y hy
    have hyK : y ∈ PIW.MassDataColumns.KvH X u p.1 :=
      (hKv y).1 ((level_compression_chain (X := X) (hb := hb) (p := p) u).2 hy)
    refine ⟨hyK, ?_⟩
    exact Subgroup.mem_subgroupOf.1 ((mem_compSet_iff X hb u p ⟨y, hyK⟩).1 hy)
  have hinf : Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) ⊓ PIW.MassDataColumns.KvH X u p.1 =
      PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1 ⊓ PIW.MassDataColumns.KvH X u p.1 := by
    have hle : Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) ≤ PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1 :=
      (Subgroup.closure_le _).2 fun y hy => (hS y hy).2
    refine le_antisymm (inf_le_inf_right _ hle) ?_
    rintro y ⟨hy2, hyK⟩
    refine ⟨Subgroup.subset_closure ?_, hyK⟩
    exact (mem_compSet_iff X hb u p ⟨y, hyK⟩).2 (Subgroup.mem_subgroupOf.2 hy2)
  have hsub : (Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)))).subgroupOf
      (PIW.MassDataColumns.KvH X u p.1) =
      (PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1).subgroupOf (PIW.MassDataColumns.KvH X u p.1) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    have h1 := SetLike.ext_iff.1 hinf (x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))
    simp only [Subgroup.mem_inf] at h1
    exact ⟨fun h => (h1.1 ⟨h, x.2⟩).1, fun h => (h1.2 ⟨h, x.2⟩).1⟩
  unfold MassDataLevelSSteps.idxHp PIW.MassDataColumns.lIdxH
  rw [hC2]
  exact congrArg Subgroup.index hsub

theorem sTypIdx_holds : STypIdx := by
  intro D X hb u p hT _
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have h1 := MassDataLevelSSteps.haarIdxLoc_holds X hb hK hT hL u p
  rw [MassDataLevelSSteps.locLevi_holds X hb hK hT hL u p, idxHp_eq X hb u p] at h1
  obtain ⟨ρ, hs, hk, hc⟩ := (PIW.MassDataColumns.locRedH_of_rest (PIW.MassDataColumns.locRedRest_of_models
    (PIW.MassDataColumns.hModelAll_of (PIW.MassDataColumns.hAdaptAll_of PIW.MassDataColumns.adapted_basis_every_place)
      PIW.MassDataColumns.level_clause_adapted_basis))) X hb hK u hT hL p
  rw [PIW.MassDataColumns.lIdxH_eq_of_red X hb u p ρ hs hk hc] at h1
  exact h1

theorem typedAll_holds : Formalism.L2.SG.PoincareAmplitudeLowerBounds.TypedAll := typedAll_of_idx sTypIdx_holds

end Formalism.L2.SG.Pf.MassDataX
end
end

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem three_dvd_cubic (r : ℕ) : 3 ∣ (r + 1) * (8 * r ^ 2 + 10 * r + 3) := by

  obtain ⟨k, hk | hk | hk⟩ : ∃ k, r = 3 * k ∨ r = 3 * k + 1 ∨ r = 3 * k + 2 := ⟨r / 3, by omega⟩
  · subst hk
    exact ⟨(3 * k + 1) * (6 * k + 1) * (4 * k + 1), by ring⟩
  · subst hk
    exact ⟨(3 * k + 2) * (2 * k + 1) * (12 * k + 7), by ring⟩
  · subst hk
    exact ⟨(k + 1) * (8 * (3 * k + 2) ^ 2 + 10 * (3 * k + 2) + 3), by ring⟩

variable {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem frameVolAt_of (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hstd : IsStdChar ψ) (hP : ProdConv X u u' ψ) :
    Formalism.L2.SG.NGAnalytic.MassDataLemmas.FrameVolAt X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq := by
  have hMS := Formalism.L2.S.Pv.MSTypP.lemmaMSStd_holds X u u' ψ hψ hstd hP
  have hZZ : 0 < (locOf X u u' ψ).volZZ := hP.2.2.2.2.2.2.1
  unfold Formalism.L2.SG.NGAnalytic.MassDataLemmas.FrameVolAt
  show ((locOf X u u' ψ).localVolumeArchimedean * ∏ p, (locOf X u u' ψ).localVolumeAtPlace p) / (locOf X u u' ψ).volZZ = _
  unfold Formalism.L2.SG.Pf.Carrier.EnergyConst.LemmaMS at hMS
  rw [hMS, mul_div_assoc, div_self hZZ.ne', mul_one]
  have hv : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
  have he : (((D.R.f * (D.R.rS + 1) * (8 * D.R.rS ^ 2 + 10 * D.R.rS + 3) : ℕ) : ℝ) / 3) =
      ((D.R.f * Formalism.L2.SG.Pf.Carrier.EnergyConst.e1 D : ℕ) : ℝ) := by
    unfold Formalism.L2.SG.Pf.Carrier.EnergyConst.e1
    obtain ⟨c, hc⟩ := three_dvd_cubic D.R.rS
    rw [mul_assoc, hc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
    push_cast
    ring
  have hg : (X.B.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) := by rw [X.g_eq]; simp [Formalism.MainNotions.S.Lat.gS]
  rw [hv, he, Real.rpow_natCast, hg, mul_assoc D.R.f]

end Formalism.L2.SG.Pf.MassDataX
end
end

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocVol
  Formalism.L2.SG.NGAnalytic.MassDataLemmas

namespace Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nTy_holds : OnTied fun D X hb Y u u' X0 ψ =>
    Formalism.L2.SG.MassDataConc.InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u)
      (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) Y.M Y.δ (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0) := by
  intro _ _ _ _ _ _ _ _ D _ X Y u u' _ hb X0 ψ hT
  exact inTypedC_loc X hb Y.hK _ _ u u' X0 ψ _ 0 0 1 _ _ _ _ _ _ _
    (fun X v => SDL.sdLocX_holds X v) (fun X v _ => Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v) sTypIdx_holds
    hT.2.1 hT.2.2.1

theorem frameVolAt_of_prodConv (hP : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ) : OnTied fun D X hb Y u u' X0 ψ =>
    FrameVolAt X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0)
      (pairSys0 u u' (X.Fu u) (Y.what₂ u)) (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0) := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT
  exact frameVolAt_of X hb Y u u' X0 ψ 0 0 1 _ _ _ _ _ hT.2.1 hT.2.2.1
    (hP Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT)

theorem nPos_of (hSW : PI.VolStabS.MassDataS.SWXS) (hP : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ) :
    OnTied fun _ X hb Y u u' X0 ψ => (bk0 X hb Y u u' X0 ψ).Pos := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT
  have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hV : 0 < X.volK2 := ENNReal.toReal_pos (ne_of_gt hK2.2.2.1) (ne_of_lt hK2.2.2.2)
  have hH : Formalism.L2.SG.TypedSets.HypX X hb (Y.FN u) (Y.FN u') u u' :=
    ⟨hT.1, hCtx.2.2.1, Y.FN_fund u, Y.FN_fund u'⟩
  exact Formalism.L2.SG.Pf.MassDataPos.massDataPosC_of X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1
    (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) Y.M Y.δ (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)
    (locHaarPosC_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _)
    (covolPosC_of X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _ hSW hT.2.1 hT.2.2.2.1
      hT.1 hT.2.2.2.2.2.2)
    (Formalism.L2.SG.Pf.MassDataPos.quotVolPosC_of X hb Y u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _ hK2 hV)
    (recPosC_of_dv X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _
      (fun X v => dvPosC_holds X v) hH)
    (hP Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT) (Formalism.L2.SG.Pf.MassDataPos.cooOf_pos X u u')
    (Formalism.L2.SG.WConst.kapN_pos (D := D)) le_rfl le_rfl one_pos

end Formalism.L2.SG.Pf.MassDataX
end
end
