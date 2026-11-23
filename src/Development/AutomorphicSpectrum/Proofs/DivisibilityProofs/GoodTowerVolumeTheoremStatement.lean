module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExistsPosOfFamilyExists
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VolumeTheoremOfInputs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComparisonOfInputsAvoidanceStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGeometricHeightConstantsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGoodRootTower
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatDegreeHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatFirstFromResolutionAndGagaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGagaStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOnHodgeFromFamilyStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivFlagOnHodgeOfFarguesStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistAutHoldsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.good_tower_volume_theorem : Top.Given → PtsIntegrableStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement → Out.WeilSt → GlobalTheory.CompanionTheory.Ar.Num.FamilyExistsPos → Cmp.CmpPair → Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  intro hG hPts hAv hW hFam hPair
  have hR : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement := hG.2.2.2.2.1
  have hFHT : HT.FarguesHodgeTate := hG.2.2.2.2.2.2.1
  have hGaga : Flat.GagaSections := hG.2.2.2.2.2.2.2.1
  have hPB : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hA0 := GlobalTheory.T.flat_zero_from_resolution_and_gaga hR hGaga
  have hA1 := GlobalTheory.T.flat_first_from_resolution_and_gaga hR hGaga
  refine ⟨?_, ?_⟩
  · intro E _ _ _ H D Xo l c Y _ hgl hs hp hq
    exact GlobalTheory.CompanionTheory.Ar.TopTower.exists_good_tower hG hW hA0 hA1 E H D Xo l c Y hgl hs hp hq
  · exact GlobalTheory.CompanionTheory.Ar.Cusp.volumeTheoremX_of_inputs hG hPts hW (GlobalTheory.T.exists_geometric_height_constants hG hW GlobalTheory.T.FlatDegree_holds) (GlobalTheory.T.model_on_hodge_from_family hFam)
      (GlobalTheory.T.triv_flag_on_hodge_of_fargues hFHT) GlobalTheory.T.FlatDegree_holds GlobalTheory.T.TwistAut_holds hPair (GlobalTheory.T.comparison_of_inputs_avoidance hPB hAv hR)

