module

import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.SquareIntegrableSegments.SegmentReordering.CsOrderfree
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentProductEquivalence.CsReorderord

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace PositivityTheory.PfEss.Zc2

section OrderFree

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irrGL_eq_of_isLSeg_same {Δ : Segment k} {x y : IrrGL (k := k)} (hx : IsLSeg Δ x.rep) (hy : IsLSeg Δ y.rep) :
    x = y := by
  obtain ⟨n, a⟩ := x
  obtain ⟨m, b⟩ := y
  obtain rfl : n = m := hx.deg_eq.symm.trans hy.deg_eq
  have key : IrrGL.of a.rep.ρ a.rep.smooth a.rep.irr = IrrGL.of b.rep.ρ b.rep.smooth b.rep.irr :=
    IrrGL.of_eq_of.mpr (IsLSeg.unique hy hx)
  have ea : IrrGL.of a.rep.ρ a.rep.smooth a.rep.irr = ⟨n, a⟩ := by
    conv_rhs => rw [← a.cl_rep]
    rfl
  have eb : IrrGL.of b.rep.ρ b.rep.smooth b.rep.irr = ⟨n, b⟩ := by
    conv_rhs => rw [← b.cl_rep]
    rfl
  rw [← ea, ← eb]
  exact key

theorem perm_of_univ_map_eq {α : Type*} {l : ℕ} {x y : Fin l → α}
    (h : Finset.univ.val.map y = Finset.univ.val.map x) : ∃ e : Equiv.Perm (Fin l), ∀ a, y a = x (e a) :=
  by apply _root_.CompanionTheory.PfEss.Zc2.perm_of_univ_map_eq; assumption

end OrderFree

theorem cs_orderfree : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LUnlinkedComm k → LOrderFree k := by
  apply CompanionTheory.PfEss.Zc2.cs_orderfree

end PositivityTheory.PfEss.Zc2
