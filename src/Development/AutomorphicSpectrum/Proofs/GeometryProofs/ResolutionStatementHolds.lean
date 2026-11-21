import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import BuildAid.ForwardExisting

section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem resBridgeStatement_holds : ReciprocityTheory.ChartRestriction.G.Geo.ResBridgeStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.resBridge

end GlobalTheory.CompanionTheory.Ar.Link
end

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.resolution_statement_holds : ReciprocityTheory.ChartRestriction.G.Geo.ResBridgeStatement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Link.resBridgeStatement_holds
