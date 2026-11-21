import Mathlib
import Development.WeilBound.CoreStatements.RationalSupMetrics.PullRatiosAlgebraic

section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem packing : PackingStatement := MultiProjectiveCoordinates.packing_statement

end GlobalTheory.CompanionTheory.Ar.Small
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.packing' : PackingStatement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Small.packing
