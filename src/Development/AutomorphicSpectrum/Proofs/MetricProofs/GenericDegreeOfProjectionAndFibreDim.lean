import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.AigGen
import BuildAid.ForwardExisting

section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim : PFCoordStatement → FibreDimStatement → GenDegStatement := by
  first | exact @PositivityTheory.HtPt.Aig.genDeg | exact PositivityTheory.HtPt.Aig.genDeg
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_degree_of_projection_and_fibre_dim : PFCoordStatement → FibreDimStatement → GenDegStatement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim
