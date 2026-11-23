module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.ETSymmApply
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.MemSpanMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.NstatementOf

@[expose] public section

theorem ReciprocityTheory.ChartRestriction.G.I2.thetaBasis_holds : ReciprocityTheory.ChartRestriction.G.I2.NStatement :=
  ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.nstatement_of ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepT ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepI ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepF ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepP ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepPos ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepDual ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepK
    ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepD
