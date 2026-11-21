import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
import BuildAid.ForwardExisting

section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem degreeStatement_of_intersectionSystem :
    ∀ II : IntersectionSystem, IsIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement :=
  fun II h => GlobalTheory.CompanionTheory.Ar.Giv.degree_of_isIntersectionSystem II h

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_system_degree : ∀ II : IntersectionSystem, IsIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.degreeStatement_of_intersectionSystem
