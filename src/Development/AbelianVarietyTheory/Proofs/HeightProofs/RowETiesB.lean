import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightRaysOfRayRecStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightCompatibleRayFieldStatement

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

theorem rayClassFields_in_coefficients : ∀ (K : Ctx) (β : BPt K), β.Is RayPosition → RayRec β.D β.O.ex.nch := by
  intro K β h
  obtain ⟨X, f, T, c, Y, hY, p, _, _, _, _, _, _, _, _, _⟩ := β
  change RayRec X.toD7 c.O.nch at h
  rw [← hY] at h
  exact h

end GlobalTheory.PlugPt
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassFieldsInCoefficientField_constructedPoint : ∀ (K : Ctx) (β : BPt K), β.Is RayPosition → RayRec β.D β.O.ex.nch := by
  atlas_forward_decl GlobalTheory.PlugPt.rayClassFields_in_coefficients
end

section
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt.Side

set_option maxHeartbeats 3200000 in

theorem exportTie_upd : ∀ (D : D7) (nch : NChoice D) (s : Side D nch) kap lam err, Nonempty (GlobalTheory.SeriesTie.ExportTie s.YS s.v₀) → Nonempty (GlobalTheory.SeriesTie.ExportTie (s.upd kap lam err).YS (s.upd kap lam err).v₀) := by
  intro D nch s kap lam err ⟨Z⟩
  exact ⟨{
    ρ := Z.ρ
    good := Z.good
    pin := { Z.pin with }
    vec := Z.vec
    ν := Z.ν
    scalar := fun i j b => ⟨(Z.scalar i j b).ne, fun h => (Z.scalar i j b).norm h, fun h => (Z.scalar i j b).rat h⟩
    tie := Z.tie
    hecke := Z.hecke
    univ := Z.univ }⟩

end GlobalTheory.PlugPt.Side
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicThetaSeriesComparison_indep_scalars_errors : ∀ (D : D7) (nch : NChoice D) (s : Side D nch) kap lam err, Nonempty (GlobalTheory.SeriesTie.ExportTie s.YS s.v₀) → Nonempty (GlobalTheory.SeriesTie.ExportTie (s.upd kap lam err).YS (s.upd kap lam err).v₀) := by
  atlas_forward_decl GlobalTheory.PlugPt.Side.exportTie_upd
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

set_option maxHeartbeats 1000000 in

theorem side_upd_ties_rays : ∀ (D : D7) (nch : NChoice D) (s : Side D nch) (EX : ErrX D) (xd : ThData D) kap lam err,
    (s.Ties EX xd → (s.upd kap lam err).Ties EX xd) ∧ (s.Rays → (s.upd kap lam err).Rays) := by
  intro D nch s EX xd kap lam err
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact
      { frame := h.frame
        tied := h.tied
        series := GlobalTheory.T.adelicThetaSeriesComparison_indep_scalars_errors D nch s kap lam err h.series
        level := h.level
        data := h.data
        psi := h.psi
        psiVal := h.psiVal
        small := h.small
        types := h.types }
  · exact h

end GlobalTheory.PlugPt
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesUpdate_preserves_parameterFreeConditions_rayFields : ∀ (D : D7) (nch : NChoice D) (s : Side D nch) (EX : ErrX D) (xd : ThData D) kap lam err, (s.Ties EX xd → (s.upd kap lam err).Ties EX xd) ∧ (s.Rays → (s.upd kap lam err).Rays) := by
  atlas_forward_decl GlobalTheory.PlugPt.side_upd_ties_rays
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

theorem rowE_tiesB : GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (𝒮 : Slots) (ν : NRead hL 𝒮) (Q : V4.Slot),
    CoreSlot 𝒮 → RowE (sAnd Q RayPosition) (linkOf (pinPt ν)) fun _ => TiesB := by
  intro hR hL 𝒮 ν Q hC
  refine RowE.of_all ?_
  intro κ K β c b _ hq hl
  have hray : RayRec β.D β.O.ex.nch := GlobalTheory.T.rayClassFieldsInCoefficientField_constructedPoint K β hq.2
  obtain ⟨p, b', ⟨kap, lam, err, hs⟩, heq⟩ := hl
  let F : (Σ (D : D7) (O : Obj D), BdPt D O c) → Prop := fun x => RayRec x.1 x.2.1.ex.nch → TiesB x.1 x.2.1 c x.2.2
  have hp : F ⟨p.w.D p.Z, p.O, b'⟩ := by
    intro hr
    have hu := GlobalTheory.T.seriesUpdate_preserves_parameterFreeConditions_rayFields _ _ (sideW ν p) p.O.ex.errX p.O.ex.xd kap lam err
    show (sidePt b').Ties p.O.ex.errX p.O.ex.xd ∧ (sidePt b').Rays
    rw [hs]
    exact ⟨hu.1 (GlobalTheory.T.side_weight_compatible_ray_field hR hL 𝒮 ν hC K p), hu.2 (GlobalTheory.T.side_weight_rays_of_ray_rec hL 𝒮 ν K p hr)⟩
  have hb : F ⟨β.D, β.O, b⟩ := (congrArg F heq).mpr hp
  exact hb hray

end GlobalTheory.PlugPt
end
