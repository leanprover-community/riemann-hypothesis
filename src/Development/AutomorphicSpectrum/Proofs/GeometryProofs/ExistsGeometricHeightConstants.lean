import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspHeightUpper
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeSum
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDegreeLower

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.TopNine

theorem nineGeoU_of_given (hG : Top.Given) (hW : Out.WeilSt) (hF : Fl.FlatDegree) :
    ∃ Ch Cu : ℝ, NineGeoU Ch Cu := by
  obtain ⟨Ch, hCh⟩ := GlobalTheory.T.cusp_height_upper hG hF
  obtain ⟨Cu, hCu⟩ := GlobalTheory.T.cusp_volume_sum hG
  refine ⟨Ch, Cu, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U M S' hII hAdm hU hT
  exact ⟨GlobalTheory.T.intersection_degree_lower hG hW E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U M S' hII hAdm hT,
    hCh E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U M S' hII hAdm hU hT,
    hCu E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U hII hAdm hU⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.TopNine
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometric_height_constants : Top.Given → Out.WeilSt → Fl.FlatDegree → ∃ Ch Cu : ℝ, NineGeoU Ch Cu := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.TopNine.nineGeoU_of_given
