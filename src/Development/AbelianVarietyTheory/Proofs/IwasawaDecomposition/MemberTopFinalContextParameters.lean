import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesEqMassesOfUnfold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayerParametersAdmissible
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwGoodOneSetDiv

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem untw_set_eq (B : Base) (pl : Finset ℕ) (f : Fr B.toPre) :
    (TwDat.untw B pl).set f = {1, f.del, f.del'} := by
  refine Set.union_eq_left.2 ?_
  rintro _ ⟨w, rfl⟩
  change (if _ then f.del' else f.del) * 1 ∈ _
  rw [mul_one]
  split_ifs
  · exact .inr (.inr rfl)
  · exact .inr (.inl rfl)

theorem recAtG_of_two_passes : (∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D) →
    ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' →
      RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) := by
  intro h2v KP Q Q' hK hF hX hS
  have hL := EvG.imp (EvG.inter hF (EvG.inter hX hS)) fun K _ _ _ _ H =>
    (large₂.inter (large₂.inter H.1 (lg_forced K)) (large₂.inter H.2.1 H.2.2))
  refine EvG.imp (EvG.inter (EvG.inter hK.ex hL) (evG_of_ev GlobalTheory.Mem.Top.LayOfCore.lay_of_core)) ?_
  rintro K _ _ _ _ ⟨⟨⟨P, f₀, hO, hks⟩, S₁, P₁, A, S₂, a₁, a₂, hlg⟩, hlay⟩
  obtain ⟨B, f, hB, hf, hKP, hH₁, hH₂⟩ := hks (S₁ P f₀) (fun F F₀ => S₂ P f₀ F F₀ {1, f₀.del, f₀.del'}) (a₁ _ _)
    (fun F F₀ => a₂ _ _ F F₀ _)
  subst hB
  obtain rfl := eq_of_heq hf
  obtain ⟨⟨h1, hfo⟩, h2, h3⟩ := hlg B f (TwDat.untw B (P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex)) hO
    ⟨hH₁, by rw [untw_set_eq]; exact hH₂⟩ (Finset.Subset.refl _) (fun w v hv => absurd hv (Finset.notMem_empty _))
  obtain ⟨C, W, V, S, N, G, c, hQ⟩ := h1 hKP hfo rfl
  obtain ⟨B', f', T', -, -, -, -, -, C', W', V', S', N', G', c', -, hTw, hQ'⟩ :=
    h3 hKP rfl C W V S N G c hQ (h2 hKP rfl C W V S N G c hQ) (fun _ => ∅) (fun _ _ _ => ∅) (by simp)
  obtain ⟨Y, hY, k1, k2, k3, k4⟩ := hlay ⟨B', C', W', V', S', N', G'⟩ f' T' c' (h2v _ c'.real.vol)
  have hTw' : DQ.TwAllAt (Stages.toD7 ⟨B', C', W', V', S', N', G'⟩) Y.nch Y.xd := by
    have e1 : Y.nch = c'.O.nch := by rw [← hY]; rfl
    have e2 : Y.xd = c'.O.xd := by rw [← hY]; rfl
    rw [e1, e2]
    exact hTw
  exact ⟨_, Y, k1, k2, k3, hTw'.twAt, ⟨_, f', T', c', hQ', by rw [hY]⟩, k4, hTw', c'.mtStable⟩

example : (∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D) → ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' → RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) := recAtG_of_two_passes

end GlobalTheory.Mem.Top.GroupRetwisting
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.layeredAutomorphicData_exists_of_twoPasses : (∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D) → ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' → RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) := by
  atlas_forward_decl GlobalTheory.Mem.Top.GroupRetwisting.recAtG_of_two_passes
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem recExP_of_recAtG : StandardLattice.SiegelMassRatioCM → ∀ (Q' : V4.Slot) (QO : Par → ∀ D : D7, Obj D → Prop), RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) → (EvP fun κ K => ∀ β : BPt K, β.Is Q' → QO κ β.D β.O) → RecExP (fun κ => DQ.withQD (fun D O => κ.Pos → QO κ D O)) := by
  intro hconds Q' QO h hq
  obtain ⟨ε0, hε0, h⟩ := h
  obtain ⟨ε1, hε1, hq⟩ := hq
  refine ⟨min ε0 ε1, lt_min hε0 hε1, fun eps C8 C5 c6 Cb he he0 he52 hC8 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb he (he0.trans (min_le_left _ _)) he52 hC8
  obtain ⟨K1, hq⟩ := hq eps C8 C5 c6 Cb he (he0.trans (min_le_right _ _)) he52 hC8
  refine ⟨K0.sup K1, fun C hstd hC hL => ?_⟩
  obtain ⟨c1, h⟩ := h C hstd hC (large_of_sup hL).1
  obtain ⟨c1', hq⟩ := hq C hstd hC (large_of_sup hL).2
  refine ⟨max (max c1 c1') 0, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hcD)
  obtain ⟨c2q, hq⟩ := hq cD (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hcD)
  obtain ⟨c2', hlow⟩ := GlobalTheory.EX.WinLow.window_lower hconds eps C he he52 hstd cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max (max c2 c2q) c2', fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hch)
  have hq := hq ch (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hch)
  obtain ⟨x1, hlow⟩ := hlow ch (le_trans (le_max_right _ _) hch)
  obtain ⟨x2, hint⟩ := exists_du_nat eps he he52
  have hq' : ∃ x3 : ℝ, Par.Pos ⟨eps, C, cD, ch, C5, c6, Cb⟩ → ∀ K : Ctx, Par.Of ⟨eps, C, cD, ch, C5, c6, Cb⟩ K → x3 ≤ K.s.x →
      ∀ β : BPt K, β.Is Q' → QO ⟨eps, C, cD, ch, C5, c6, Cb⟩ β.D β.O := by
    by_cases hp : Par.Pos ⟨eps, C, cD, ch, C5, c6, Cb⟩
    · obtain ⟨x3, h3⟩ := hq hp
      exact ⟨x3, fun _ => h3⟩
    · exact ⟨0, fun hp' => absurd hp' hp⟩
  obtain ⟨x3, hq'⟩ := hq'
  refine ⟨1, max (max x0 x3) (max x1 x2), one_pos, fun s P a b c hs hx d3 => ?_⟩
  have hok := d3.ok
  have hx0 : x0 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx3 : x3 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : x1 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : x2 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨du, hpos, hdu⟩ := hint s C cD ch P _ a b c hs hx2 hok
  obtain ⟨hD, hDle⟩ := GlobalTheory.Mem.Top.DsLow.DsP_pos_and_lower P
  refine ⟨du, DsP P, hpos, hD, fun u => ?_, fun Lv h1 h2 h3 => ?_⟩
  · rw [one_mul]
    exact hlow s P _ a b c du (DsP P) hs hx1 hok hdu hDle u
  · let K : Ctx := ⟨s, C, cD, ch, P, _, a, b, c, hstd, hok, Lv, fun u => by rw [h1]; exact hdu u, h2, h3⟩
    obtain ⟨D, Y, g1, g2, g3, g4, ⟨X, f, T, co, hQ, he⟩, u1, u2, u3⟩ := h K rfl rfl rfl hs hx0 d3
    refine ⟨D, Y, g1, g2, g3, g4, fun p p1 p2 p3 p4 => ⟨fun hp => ?_, ?_⟩⟩
    · obtain ⟨rfl, he⟩ := Sigma.mk.inj he
      exact hq' hp K ⟨rfl, rfl, rfl, hs, d3⟩ hx3
        ⟨X, f, T, co, Y, eq_of_heq he, p, p1, p2, p3, p4, ⟨C5, c6, Cb, d3⟩, g2, g3, u1, u2⟩ hQ
    · exact DQ.qd_setDiv D (Y.obj p) (nPrime p.L) p.ht ⟨u1, u2, u3⟩

end GlobalTheory.Fc
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsLayeredData_of_goodScaleContexts : StandardLattice.SiegelMassRatioCM → ∀ (Q' : V4.Slot) (QO : Par → ∀ D : D7, Obj D → Prop), RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) → (EvP fun κ K => ∀ β : BPt K, β.Is Q' → QO κ β.D β.O) → RecExP (fun κ => DQ.withQD (fun D O => κ.Pos → QO κ D O)) := by
  atlas_forward_decl GlobalTheory.Fc.recExP_of_recAtG
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem memberTop_final_contextParameters :
    StandardLattice.SiegelMassRatioCM → (∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) →
    ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot) (QO : Par → ∀ D : D7, Obj D → Prop),
      GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' →
      (EvP fun κ K => ∀ β : BPt K, β.Is Q' → QO κ β.D β.O) →
      RecExP (fun κ => DQ.withQD (fun D O => κ.Pos → QO κ D O)) :=
  fun hAll hU KP Q Q' QO hB hF hE hS hEv =>
    GlobalTheory.T.existsLayeredData_of_goodScaleContexts hAll Q' QO
      (GlobalTheory.T.layeredAutomorphicData_exists_of_twoPasses (GlobalTheory.Mem.VolMass.volumes_eq_masses_of_unfold hU) KP Q Q' hB hF hE hS)
      hEv

end GlobalTheory.Fc
end
