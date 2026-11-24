module

public import Formalism.PeriodIntegrals.AreaLat
public import Formalism.PeriodIntegrals.SigmaStarUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.CoefShift
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.SiegelSetCompleteness
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.SiegelSetShiftInvariance
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.ZeroOfCoef
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

namespace PI.SSU

theorem sigmaStarUniq_of (h : AreaLat) : SigmaStarUniq :=
  main_of (key_of siegel_set_shift_invariance siegel_set_completeness) h

end PI.SSU
