module

public import Formalism.QuotientMetricDivisors.DivIntoDualShift
public import Formalism.QuotientMetricDivisors.HeightBoundExactNorms
public import Formalism.QuotientMetricDivisors.LatticeGlueUnique
public import Formalism.QuotientMetricDivisors.ScalarLiftLowerBoundRows
public import Formalism.QuotientMetricDivisors.TheoremDivIneqRowsShift
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DescendedNorm
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TwistedLatticeNaturality
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.WeightedPlaceLogSum
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.YoungDiagramHook
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.YoungDiagramTopExact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

namespace Formalism.DivisionValues

theorem latticeGlue : LatticeGlue := lattice_gluing

theorem height_constant_bound : HeightBoundConstant := height_constant_first

theorem rowsHook : RowsHook := young_diagram_hook

theorem rowsStepEOrigin : RowsStepEOrigin := young_diagram_step_origin

theorem shiftMu : ShiftMu := by
  unfold ShiftMu
  exact shift_slope_mu

theorem shiftEx : ShiftEx := by
  unfold ShiftEx
  exact shift_existence

theorem divIntoDualShift : DivIntoDualShift := divisor_into_dual_shift

theorem primeLogSum : PrimeLogSum := prime_log_sum_bound

end Formalism.DivisionValues
