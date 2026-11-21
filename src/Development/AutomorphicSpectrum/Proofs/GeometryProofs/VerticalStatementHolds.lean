import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
import BuildAid.ForwardExisting

section
namespace GlobalTheory.CompanionTheory.Ar.Flat

open ReciprocityTheory.ChartRestriction.G.AI.I2

theorem vertical_holds : VerticalStatement := GroundTheory.Heights₂.Heights.Inter.InductiveIntersectionFormula.proof

end GlobalTheory.CompanionTheory.Ar.Flat
end

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_statement_holds : VerticalStatement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.vertical_holds
