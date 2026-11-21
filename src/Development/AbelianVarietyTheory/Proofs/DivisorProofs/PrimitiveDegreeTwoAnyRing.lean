import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoStructureSheafVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatementStatement

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem primE2_any_ring : PrimitiveExtendedDegTwoVanish := by
  apply GlobalTheory.T.primitive_degree_two_extension
  apply GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish
  intro R _ A _ g hA hs
  obtain ⟨⟨hfin, hproj, hrk⟩, hw, -, -⟩ := GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hs
  exact ⟨⟨hfin, hproj, hrk⟩, hw⟩

end GlobalTheory.Obs
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_degree_two_any_ring : PrimitiveExtendedDegTwoVanish := by
  atlas_forward_decl GlobalTheory.Obs.primE2_any_ring
