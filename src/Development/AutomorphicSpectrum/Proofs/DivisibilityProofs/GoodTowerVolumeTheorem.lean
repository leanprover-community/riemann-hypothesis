import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExistsPosOfFamilyExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGoodRootTower
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VolumeTheoremOfInputs
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGeometricHeightConstants
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOnHodgeFromFamily
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivFlagOnHodgeOfFargues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatDegreeHolds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistAutHolds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComparisonOfInputsAvoidance

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem goodTower_and_volume :
    Top.Given → PtsIntegrableStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement → Out.WeilSt → GlobalTheory.CompanionTheory.Ar.Num.FamilyExistsPos →
      Cmp.CmpPair → Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  intro hG hPts hAv hW hFam hPair
  have hR : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement := hG.2.2.2.2.1
  have hFHT : HT.FarguesHodgeTate := hG.2.2.2.2.2.2.1
  have hGaga : Flat.GagaSections := hG.2.2.2.2.2.2.2.1
  have hPB : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hA0 := GlobalTheory.T.flat_zero_from_resolution_and_gaga hR hGaga
  have hA1 := GlobalTheory.T.flat_first_from_resolution_and_gaga hR hGaga
  refine ⟨?_, ?_⟩
  · intro E _ _ _ H D Xo l c Y _ hgl hs hp hq
    exact GlobalTheory.T.exists_good_root_tower hG hW hA0 hA1 E H D Xo l c Y hgl hs hp hq
  · exact GlobalTheory.T.volume_theorem_of_inputs hG hPts hW (GlobalTheory.T.exists_geometric_height_constants hG hW GlobalTheory.T.FlatDegree_holds) (GlobalTheory.T.model_on_hodge_from_family hFam)
      (GlobalTheory.T.triv_flag_on_hodge_of_fargues hFHT) GlobalTheory.T.FlatDegree_holds GlobalTheory.T.TwistAut_holds hPair (GlobalTheory.T.comparison_of_inputs_avoidance hPB hAv hR)

end GlobalTheory.CompanionTheory.Ar.Top
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_volume_theorem : Top.Given → PtsIntegrableStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement → Out.WeilSt → GlobalTheory.CompanionTheory.Ar.Num.FamilyExistsPos → Cmp.CmpPair → Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.goodTower_and_volume
