module

public import Formalism.PeriodIntegrals.ScXuExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LocalDataSatisfyLinearHypotheses
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.SplitLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.SplitUnitaryProjectionCompatibility
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

theorem sc_xu_exists : PI.ScXuExists.Target :=
  PI.UnitaryGroupMassFormula.ScXuExists.scXuExists_of PI.UnitaryGroupMassFormula.ScXuExists.local_splitting_projection
    PI.UnitaryGroupMassFormula.ScXuExists.BrA.local_data_satisfy_linear_hypotheses PI.UnitaryGroupMassFormula.ScXuExists.BrB.split_unitary_projection_compatibility
