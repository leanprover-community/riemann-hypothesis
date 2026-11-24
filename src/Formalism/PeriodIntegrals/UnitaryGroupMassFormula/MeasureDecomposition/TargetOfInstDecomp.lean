module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ContinuousUMatApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.GenSemiOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.GenericWeilRepresentation
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.HaarSub
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstLeftInvMuInf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ModOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.Proper
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

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem target_of_instDecomp (hd : InstDecomp) : PI.ScMuExists.Target :=
  target_of_steps generic_haar_subgroup (genSemi_of generic_haar_subgroup) generic_weil_representation measure_subFacts
    (genModOne_of generic_haar_subgroup) hd proper_action_instance

end PI.ScMuExists.UnitaryGroupMassFormula
