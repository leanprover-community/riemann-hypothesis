import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaCellSemisimplificationGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFinitenessStatement

section
theorem GlobalTheory.CompanionTheory.Glob.cellSemisimplification : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.CellSemisimplification k :=
  GlobalTheory.SmGL.CellSemis.cellSemisimplification GlobalTheory.T.bernstein_zelevinsky_finiteness
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_cell_semisimplification : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.CellSemisimplification k := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Glob.cellSemisimplification
