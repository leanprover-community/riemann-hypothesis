module

public import Formalism.PeriodIntegrals.EntAtD
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Bridge
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.EntAtDOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.ExpCoeff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.LapComm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.LapForms
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.MinorAff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.SDegMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

theorem jet_bound_ramified_prime : PI.EntAtD.EntAtD :=
  PI.EntAtD.W.entAtD_of PI.EntAtD.W.pExpCoeff PI.EntAtD.W.pBridge PI.EntAtD.W.pLapComm
    PI.EntAtD.W.pMinorAff PI.EntAtD.W.pSDegMul PI.EntAtD.W.pLapForms
