module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EventuallyDifferentiableAtOfContDiffAtTwo
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.Cartier
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CurveDens

theorem cHess_apply_eq_ddbar {n : ℕ} {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hg : ContDiffAt ℝ 2 g x) (j k : Fin n) :
    ReciprocityTheory.L2DbarEstimates.cHess n g x j k =
      ddbar g x (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) := by
  have e : ReciprocityTheory.L2DbarEstimates.wdb n k g = fun y => dbar g y (EuclideanSpace.single k 1) := by
    funext y
    simp only [ReciprocityTheory.L2DbarEstimates.wdb, dbar_apply, ReciprocityTheory.L2DbarEstimates.bas, smul_eq_mul]
    ring
  rw [ddbar_eq_del_dbar hg, del_apply, ReciprocityTheory.L2DbarEstimates.cHess, Matrix.of_apply, e]
  simp only [ReciprocityTheory.L2DbarEstimates.wd, ReciprocityTheory.L2DbarEstimates.bas, smul_eq_mul]
  ring

end GlobalTheory.CurveDens

namespace GlobalTheory.CurveDens

end GlobalTheory.CurveDens
