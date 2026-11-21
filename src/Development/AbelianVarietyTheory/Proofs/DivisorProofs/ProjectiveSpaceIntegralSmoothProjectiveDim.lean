import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem pspace_integral_dim_proj_smooth :
    ∀ (k : Type) [Field k] (N : ℕ), IsIntegral (PSpace k N) ∧ topologicalKrullDim (PSpace k N) = N ∧ IsProjOver (PSpace.str k N) ∧ SmoothOfRelativeDimension N (PSpace.str k N) :=
  fun k _ N => ⟨ProjSpace.isIntegral_of_isDomain k N, ProjSpace.topologicalKrullDim_eq k N,
    ⟨N, 𝟙 _, inferInstance, by simp⟩, inferInstance⟩

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveSpace_integral_smooth_projective_dim : ∀ (k : Type) [Field k] (N : ℕ), IsIntegral (PSpace k N) ∧ topologicalKrullDim (PSpace k N) = N ∧ IsProjOver (PSpace.str k N) ∧ SmoothOfRelativeDimension N (PSpace.str k N) := by
  atlas_forward_decl GlobalTheory.pspace_integral_dim_proj_smooth
