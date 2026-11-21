import Development.AbelianVarietyTheory.Proofs.HeightProofs.RowEPartTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RowETiesB
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightCompatibleRayFieldStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightCompatibleRayField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightPsiChoiceTameStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightPsiChoiceTame
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightExportLevelStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightExportLevel
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightRaysOfRayRecStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightRaysOfRayRec

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.PlugPt.side_weight_psi_values_tame_tie : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), Formalism.L2.Host.PsiChoiceCompatible (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf p.O.ex.nch (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).tp ∧ (∀ v, (p.w.D p.Z).what₂.muAt v ≠ (p.w.D p.Z).what₂.mu0 → ((_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).tp.psi v).ValuesIn 0 (p.w.D p.Z).what₂.embLL) ∧ GlobalTheory.DimPartsCompare.TameTie (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf.W.om := by
  intro hL 𝒮 ν K p
  refine ⟨p.x.n.chrPsi, ?_, ?_⟩
  · intro v _
    show (p.x.n.tp.psi v).ValuesIn 0 _
    rw [p.x.n.psi]
    exact GlobalTheory.twDat_psi_valuesIn_LL p.B p.T p.x.coh v
  · have h := p.x.what₂.grp
    have hf := (GlobalTheory.Plug.wPt_frame 𝒮 K p).2.1
    show GlobalTheory.DimPartsCompare.TameTie (p.w.D p.Z) (GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z).W.om
    rw [hf]
    exact types_of_true (D := p.w.D p.Z) _ h
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_weight_psi_choice_tame_tie : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), Formalism.L2.Host.PsiChoiceCompatible (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf p.O.ex.nch (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).tp ∧ (∀ v, (p.w.D p.Z).what₂.muAt v ≠ (p.w.D p.Z).what₂.mu0 → ((_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).tp.psi v).ValuesIn 0 (p.w.D p.Z).what₂.embLL) ∧ GlobalTheory.DimPartsCompare.TameTie (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf.W.om := by
  atlas_forward_decl _root_.GlobalTheory.PlugPt.side_weight_psi_values_tame_tie
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory
theorem sideW_export_small_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), Nonempty (GlobalTheory.SeriesTie.ExportTie (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).YS (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).v₀) ∧ LevelIs (p.w.D p.Z).nexp ((_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).R.eG.trans (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cG) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).P0 (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).ψ0⁻¹ ∧ AllData (p.w.D p.Z).nexp p.O.ex.xd.xd0 ∧ SmallHas (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf := by
  intro hR hL 𝒮 ν K p
  have hE : (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).Export p.O.ex.xd := (ν.rd _ _ _ _ _ _ _ _ _ _ _ _ p.x.nx).2.1.down
  have hcf : (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf = Fr.at (p.w.st p.Z) p.f := (GlobalTheory.Plug.wPt_frame 𝒮 K p).2.1
  refine ⟨hE.1, hE.2.1, hE.2.2, ?_⟩
  rw [hcf]
  exact GlobalTheory.T.small_frame_at_column hR p.B p.f p.T p.w p.Z
end GlobalTheory
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_weight_export_all_data_small_has : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), Nonempty (GlobalTheory.SeriesTie.ExportTie (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).YS (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).v₀) ∧ LevelIs (p.w.D p.Z).nexp ((_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).R.eG.trans (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cG) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).P0 (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).ψ0⁻¹ ∧ AllData (p.w.D p.Z).nexp p.O.ex.xd.xd0 ∧ SmallHas (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf := by
  atlas_forward_decl _root_.GlobalTheory.sideW_export_small_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.PlugPt.side_weight_ties_of_ray_field : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮), CoreSlot 𝒮 → ∀ (K : Ctx) (p : WPt 𝒮 K), (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).Ties p.O.ex.errX p.O.ex.xd := by
  intro hR hL 𝒮 ν hC K p
  obtain ⟨hRC, hTC, -⟩ := GlobalTheory.Plug.wPt_frame 𝒮 K p
  have ht := GlobalTheory.T.coreFrameCompatible_constructed_point hR 𝒮 hC K p
  obtain ⟨hpsi, hval, htame⟩ := _root_.GlobalTheory.T.side_weight_psi_choice_tame_tie hL 𝒮 ν K p
  obtain ⟨hser, hlev, hdat, hsmall⟩ := _root_.GlobalTheory.T.side_weight_export_all_data_small_has hR hL 𝒮 ν K p
  refine ⟨?_, ?_, hser, hlev, hdat, hpsi, hval, hsmall, htame⟩
  · show p.x.what₂.r.z.R.C = GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z
    rw [hRC, hTC]
  · show Tied p.O.ex.errX p.x.what₂.r.z.core (GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z)
    rw [hTC]
    exact ht
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_weight_ties_err_of_ray_field_core_slot : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮), CoreSlot 𝒮 → ∀ (K : Ctx) (p : WPt 𝒮 K), (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).Ties p.O.ex.errX p.O.ex.xd := by
  atlas_forward_decl _root_.GlobalTheory.PlugPt.side_weight_ties_of_ray_field
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX
  GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Plug.RaysW
theorem rays_of_rayRec_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (K : Ctx) (p : WPt 𝒮 K),
    RayRec (p.w.D p.Z) p.O.ex.nch → (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).Rays := by
  intro hL 𝒮 ν K p hR t
  have hlev := p.x.what₂.r.z.lev
  have hmu := p.x.what₂.mu
  have hn := p.x.n.Q
  change R3.TupU p.w.I (R3.usedOf p.w.I p.T p.x.Wt) at t
  show GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField _ (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel p.x.what₂.r.z.R.toRealDat t)
  rcases (R3.mem_range_ixOf p.w.I).1 ⟨t, rfl⟩ with h0 | ⟨w, hw, hxi⟩
  ·
    obtain ⟨v⟩ := nonempty_heightOneSpectrum (p.w.D p.Z).what₂.LL
    refine hR ((p.w.D p.Z).plEq.symm v) _ fun P hP ↦ ?_
    have hram : ¬ (p.x.what₂.r.z.R.xiH t).UnrAt P := (hlev.is.Q_ram t P).2 (Or.inl hP)
    rw [hlev.xiH t, h0, p.w.ok.trueColumnChoices_heckeChar_reference_eq_one] at hram
    exact absurd (Formalism.L2.Fam.DivCQ.unrAt_one P) hram
  ·
    refine hR w _ fun P hP ↦ ?_
    have hram : ¬ (p.x.what₂.r.z.R.xiH t).UnrAt P := (hlev.is.Q_ram t P).2 (Or.inl hP)
    have hpl := (hlev.is.Q_pl t P hP).1
    by_cases hpd : (((p.w.D p.Z).host.pde * (p.w.D p.Z).host.pde' : ℕ) : 𝓞 (p.w.D p.Z).host.E) ∈ P.asIdeal
    · obtain ⟨q, hq, hc, -⟩ := hpl
      exact Or.inl ⟨hpd, hc ▸ hq⟩
    · right
      have hx : p.x.what₂.r.z.R.xiH t = p.T.xiTw p.f w := by
        rw [hlev.xiH t, hxi, p.w.C_eq]
      rw [hx] at hram
      have h1 : ¬ ((p.B.host.pde : ℕ) : 𝓞 p.B.host.E) ∈ P.asIdeal := fun h ↦ hpd (by
        rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
      have h2 : ¬ ((p.B.host.pde' : ℕ) : 𝓞 p.B.host.E) ∈ P.asIdeal := fun h ↦ hpd (by
        rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
      have hδ : (if p.B.places.resChar w = p.B.host.pde then p.f.del' else p.f.del).UnrAt P := by
        split_ifs
        · exact p.f.isDel'.unr P h2
        · exact p.f.isDel.unr P h1
      have hψ : ¬ (p.T.psi w).UnrAt P := fun h ↦ hram (Formalism.L2.Host.HChar.UnrAt.mul hδ h)
      have hQ : P ∈ p.T.Q w := by
        by_contra hq
        exact hψ (((p.T.psi_is w).ram P).2 hq)
      refine ⟨fun hm ↦ ?_, (hn w hw).1 ▸ hQ⟩
      have e1 : p.T.xiTw p.f w = 1 := by
        rw [← hmu.tw w, ← hmu.on w hw]
        exact (congrArg p.w.I.xi hm).trans hmu.mu0
      rw [e1] at hram
      exact hram (Formalism.L2.Fam.DivCQ.unrAt_one P)
end GlobalTheory.Plug.RaysW
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_weight_rays_of_ray_rec' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), RayRec (p.w.D p.Z) p.O.ex.nch → (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).Rays := by
  atlas_forward_decl _root_.GlobalTheory.Plug.RaysW.rays_of_rayRec_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PlugPt
theorem rowE_tiesB_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (Q : V4.Slot),
    CoreSlot 𝒮 → RowE (sAnd Q RayPosition) (linkOf (_root_.GlobalTheory.PlugPt.pinnedPointOfReading ν)) fun _ => TiesB := by
  intro hR hL 𝒮 ν Q hC
  refine RowE.of_all ?_
  intro κ K β c b _ hq hl
  have hray : RayRec β.D β.O.ex.nch := GlobalTheory.T.rayClassFieldsInCoefficientField_constructedPoint K β hq.2
  obtain ⟨p, b', ⟨kap, lam, err, hs⟩, heq⟩ := hl
  let F : (Σ (D : D7) (O : Obj D), BdPt D O c) → Prop := fun x => RayRec x.1 x.2.1.ex.nch → TiesB x.1 x.2.1 c x.2.2
  have hp : F ⟨p.w.D p.Z, p.O, b'⟩ := by
    intro hr
    have hu := GlobalTheory.T.seriesUpdate_preserves_parameterFreeConditions_rayFields _ _ (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p) p.O.ex.errX p.O.ex.xd kap lam err
    show (sidePt b').Ties p.O.ex.errX p.O.ex.xd ∧ (sidePt b').Rays
    rw [hs]
    exact ⟨hu.1 (_root_.GlobalTheory.T.side_weight_ties_err_of_ray_field_core_slot hR hL 𝒮 ν hC K p), hu.2 (_root_.GlobalTheory.T.side_weight_rays_of_ray_rec' hL 𝒮 ν K p hr)⟩
  have hb : F ⟨β.D, β.O, b⟩ := (congrArg F heq).mpr hp
  exact hb hray
end GlobalTheory.PlugPt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PlugPt
theorem rowE_part_ties_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (Q : V4.Slot),
    CoreSlot 𝒮 → RowE (Bd := _root_.GlobalTheory.Fc.Ind.PointSummands) (sAnd Q RayPosition) (linkOf fun K p c b => _root_.GlobalTheory.PlugPt.pinnedPointOfReading ν K p c b.pt)
      fun _ D O c b => TiesB D O c b.pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧ More b.pt := by
  intro hR hL 𝒮 ν Q hC
  refine (EvP.and (_root_.GlobalTheory.PlugPt.rowE_tiesB_alt hR hL 𝒮 ν Q hC) GlobalTheory.T.eventually_constructedPoint_hostSize_numerical).mono ?_
  intro κ K _ H β hq c b hl
  obtain ⟨p, b', hpin, heq⟩ := hl
  have hl' : linkOf (_root_.GlobalTheory.PlugPt.pinnedPointOfReading ν) K β c b.pt :=
    ⟨p, b'.pt, hpin, congrArg (fun y : (Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.Ind.PointSummands D O c) =>
      (⟨y.1, y.2.1, y.2.2.pt⟩ : Σ (D : D7) (O : Obj D), BdPt D O c)) heq⟩
  have ht : TiesB β.D β.O c b.pt := H.1 β hq c b.pt hl'
  have hs : FieldSmall β.D β.O.L := ((H.2 β).2 _ ht.1.tied.field).2.2
  have hw : SingleIndexPlacesAreTwisted b.pt := fun w hw => ((b.muDef 0 0).2.2.2 w).2 hw
  exact ⟨ht, ⟨hs, (GlobalTheory.T.pathCoreConditions_of_intrinsicConditions β.D β.O c b.pt ht hs).2.2.1⟩, GlobalTheory.PlugPt.more_of_tiesB β.D β.O c b.pt ht hs hw⟩
end GlobalTheory.PlugPt
end
end
