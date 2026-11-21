import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SlopeBoundOfLargeDegreeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyDegreeOfBadReduction
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyBadReductionHolds

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl

theorem slopeBound_and_lemmaS_of_siegel :
    LineOfLargeDegree.Statement → SlopeBoundSt ∧ Prov.LemmaS := fun hS =>
  GlobalTheory.T.slope_bound_of_large_degree_line hS (GlobalTheory.T.key_degree_of_bad_reduction GlobalTheory.T.key_bad_reduction_holds)

end GlobalTheory.CompanionTheory.Ar.Sl
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slope_bound_of_line_large_degree : LineOfLargeDegree.Statement → SlopeBoundSt ∧ Prov.LemmaS := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Sl.slopeBound_and_lemmaS_of_siegel
