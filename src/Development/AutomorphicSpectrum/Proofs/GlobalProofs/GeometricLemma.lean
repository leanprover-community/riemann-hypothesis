import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.InducedCellSemisimplification
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetOfInducedFiltrationStatement

section
theorem _root_.GlobalTheory.T.jacquetOfInducedFiltration' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetOfInducedFiltration k := GlobalTheory.T.jacquet_of_induced_filtration
end

section
namespace GlobalTheory.CompanionTheory.GeoLink

theorem geometricLemma : GlobalTheory.Published.GeometricLemma := by
  intro k _ _ _ _
  have h := GlobalTheory.T.induced_cell_semisimplification k
  have hloc := GlobalTheory.T.jacquetOfInducedFiltration' k
  first
    | exact h hloc
    | exact h.mpr hloc
    | exact ⟨h, hloc⟩
    | exact ⟨hloc, h⟩
    | exact hloc.mpr h
    | exact hloc h
    | exact hloc

end GlobalTheory.CompanionTheory.GeoLink
end
