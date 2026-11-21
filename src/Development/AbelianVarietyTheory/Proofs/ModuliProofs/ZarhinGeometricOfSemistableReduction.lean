import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatements
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianSchemeUniformisationExistsGeometric

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem zhGeo_of_semistableReduction :
    GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ZHGeoSt := fun S => by
  obtain ⟨L, L2, L3, L4, L5, -⟩ := GlobalTheory.allSixLaws
  exact GlobalTheory.T.semiAbelianScheme_uniformisation_exists_geometric GlobalTheory.homExtension_semiAbelian_dvr S GlobalTheory.ZH.thmU_and_uTors.1 L L2 L3 L4 L5
    GlobalTheory.ZH.thmU_and_uTors.2

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinGeometric_of_semistableReduction : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ZHGeoSt := by
  atlas_forward_decl GlobalTheory.zhGeo_of_semistableReduction
