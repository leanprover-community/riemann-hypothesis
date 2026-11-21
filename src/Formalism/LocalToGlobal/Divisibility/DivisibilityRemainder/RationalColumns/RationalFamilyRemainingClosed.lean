import Formalism.LocalToGlobal.TieTwRecOf
import Formalism.LocalToGlobal.Divisibility.RecBridgeWire
import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.RationalColumns.ColFacts
import Formalism.LocalToGlobal.Divisibility.TupUsed

section
noncomputable section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace Formalism.L2.DIV.RatFullPt

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

theorem rrFull_of (P : RowSideFamily ex) (hF : ColFacts P.S1 P.C)
    (hR : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) : D.RRFull := by
  have hlat := hF.rr_lattice
  have hlat' : Submodule.IsLattice D.what₂.LL (P.A3.indefDown P.S1).RR := hlat
  have hL : D.div.RR.L = (P.A3.indefDown P.S1).RR.map (P.I.eRR.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) :=
    hR.sharpRR.lat
  refine ⟨by rw [hL]; exact hlat'.fg.map _, ?_⟩
  have hset : (D.div.RR.L : Set D.div.RR.V) = P.I.eRR.toLinearMap '' ((P.A3.indefDown P.S1).RR : Set _) := by
    rw [hL, Submodule.map_coe]; rfl
  rw [hset, Submodule.span_image, hlat'.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact P.I.eRR.surjective

theorem buRational_of (P : RowSideFamily ex) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hF : ColFacts P.S1 P.C)
    (hR : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) (hPt : RowsHoldDcPt3 P)
    (hBu : Rows.BuDefQ D.what₂) : D.BuRational := by
  intro u φ x
  obtain ⟨x', rfl⟩ := (P.I.eNu u).surjective φ
  obtain ⟨y, rfl⟩ := P.I.eRR.surjective x
  rw [hBu, hR.colsBk u x' y]
  have hform := P.tied.div.sharp.forms P.A3.A.μ0
  refine PerDescent.per_sec D u (D.jN u (P.I.eNu u x')) (P.I.tup P.A3.A.μ0) P.tied.div.tup.mu0
    (fun F => P.I.jA P.A3.A.μ0 ((rV0 D P.A3.A P.Ps P.ψs P.A3.A.μ0).mulVec F)) P.I.eRR
    (fun F => (P.S1.ι P.A3.A.μ0).mulVec (((P.A3.side3 P.Ps P.ψs P.Zs).Pq P.A3.A.μ0).mulVec F))
    (P.C.B (P.I.wU u) x') ?_ ?_ ?_ ?_ y
  · exact (hF.bij _).2.comp (hF.wf.Pq_surj _)
  · exact range_op_eq_span hform _ (fun z => lvlOp_range _ _ _ _ _ z)
      (fun F => Formalism.L2.G.ServJoint.level_operator_fixes_image hOk.ok2 P.Ps P.ψs (P.A3.fam3.toSub2 P.Zs) P.A3.A.μ0 F)
  · intro F
    have h := P.tied.div.sharp.iota P.A3.A.μ0 F
    rw [Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_iota] at h
    exact h
  · intro F
    have h1 : P.Dc.Pt (P.I.wU u) P.A3.A.μ0 x' F = P.C.ζ (P.I.wU u) P.A3.A.μ0 * P.C.B (P.I.wU u) x'
        ((P.S1.ι P.A3.A.μ0).mulVec (((P.A3.side3 P.Ps P.ψs P.Zs).Pq P.A3.A.μ0).mulVec F)) := hF.l1b.1 _ _ _ _
    have h2 : P.C.ζ (P.I.wU u) P.A3.A.μ0 = 1 := hF.l1b.2.1 _
    rw [h2, one_mul] at h1
    exact (hPt u P.A3.A.μ0 x' F).symm.trans (congrArg D.what₂.embLL h1)

end Formalism.L2.DIV.RatFullPt

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

namespace Formalism.L2.DIV.RatFullFam

open Formalism.L2.Top3 Formalism.L2.Top4

theorem buRat_rrFull_closed (𝒜 : FamClass)
    (sel : Formalism.L2.TSel 𝒜)
    (selS : SelS 𝒜 sel)
    (selP : BaseLevelCompatibleSelection 𝒜 sel)
    (selDH : SelDH 𝒜 sel)
    (selC : ColumnCompatibleSelection 𝒜 sel selP)
    (selB : SelB 𝒜 sel selS selP selDH selC)
    (hPA : PrimAll sel (selIOf selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (hDcPtG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DcPtG (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, RowsAtSel sel (selIOf selB) (fun Fm hc x hx h i C CH => Formalism.L2.Top4Wire2.DefRowsF (selIOf selB) Fm hc x hx h i C CH) (OneMapOf selB)
        Fm (d3_a hc) CH) :
    Closed (D3 3 𝒜) fun Fm _ => ∀ _ : D3 3 𝒜 Fm, TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational) ∧
        (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).RRFull) :=
  rRows.imp fun Fm CH _ h hc _ _ => by
    obtain ⟨C, _, x0, H⟩ := h hc
    have key : ∀ x ≥ max (max x0 (sel Fm (d3_a hc)).1) (Fm.x1 + 1), ∀ i : Fm.Ix x,
        (Fm.D x i).BuRational ∧ (Fm.D x i).RRFull := by
      intro x hx0 i
      have h0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0
      have hs : (sel Fm (d3_a hc)).1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0
      have hx : Fm.x1 < x := lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) hx0)
      obtain ⟨ra, _⟩ := H x hx hs h0 i
      obtain ⟨prows, hsep⟩ := hPA Fm (d3_a hc) x hx hs i
      have hok1 := (selC Fm (d3_a hc) x hx hs i).ok1
      have hU := Formalism.IndefR.LevelRealisationRankEquality.tupAllUsed_of_real (selB Fm (d3_a hc) x hx hs i).Q
      have hR := (hDivG Fm (d3_a hc) x hx hs i).toRows hU
      have hPt := Formalism.L2.DIV.dcPt_of_G hU (hDcPtG Fm (d3_a hc) x hx hs i)
      have hF := Formalism.L2.DIV.RatFullPt.colFacts_real ((selIOf selB) Fm (d3_a hc) x hx hs i) hok1 hsep prows ra.seeIso ra.miStar
      exact ⟨Formalism.L2.DIV.RatFullPt.buRational_of _ hok1 hF hR hPt (Fm.ties x i).bu_def, Formalism.L2.DIV.RatFullPt.rrFull_of _ hF hR⟩
    exact ⟨⟨_, fun x hx i => (key x hx i).1⟩, ⟨_, fun x hx i => (key x hx i).2⟩⟩

end Formalism.L2.DIV.RatFullFam

end
end
