import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLocalDataTransportDivision

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.WitTr

set_option maxHeartbeats 4000000 in

theorem goodO_setDiv : ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), GoodO D nch xd → GoodO (setDiv D N h) (nchTr N h nch) (xdTr N h xd) := by
  intro D nch xd N h hg
  obtain ⟨⟨⟨E, N0, S⟩, hE, hA, hC⟩, hsep⟩ := hg
  subst hE
  exact ⟨⟨⟨{ (twEOf xd) with }, N0, S⟩, rfl, hA, hC⟩, hsep⟩

end GlobalTheory.Mem.Top.Bl.WitTr

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodTwistsThetaLattices_preserved_divisionChange : ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), GoodO D nch xd → GoodO (setDiv D N h) (nchTr N h nch) (xdTr N h xd) := by
  atlas_forward_decl GlobalTheory.Mem.Top.Bl.WitTr.goodO_setDiv
