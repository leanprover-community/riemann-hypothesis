module

public import Formalism.PeriodIntegrals.LocDensCorank
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.SplitCount
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.EulerFactorTwo
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.CongruenceDensity
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

open ValuativeRel Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocDensCorank

theorem locDensCorank_of (hC : CongStep) (hF : FieldCount) (hS : SplitCount) :
    PI.LocDensCorank.LocDensCorank := by
  intro F E _ _ _ _ _ _ _ M hloc hchar V _ _ H Λ hsd ϖ hϖ ι _ _ A a hA hdet hcard
  rw [hC F E M V H Λ ϖ ι A a hA hdet]
  by_cases hE : ∀ x : E, x ≠ 0 → IsUnit x
  · rw [if_pos hE]
    exact hF F E M hloc hchar hE V H Λ hsd ϖ hϖ ι a hcard
  · rw [if_neg hE]
    exact hS F E M hloc hchar ((PI.UnitaryGroupMassFormula.CntFormula.locE_isUnit_or_exists_algEquiv_prod_swap M.L).resolve_left hE) V H Λ hsd ϖ hϖ ι a hcard

theorem locDensCorank_of_counts (hF : FieldCount) (hS : SplitCount) : PI.LocDensCorank.LocDensCorank := by
  exact locDensCorank_of congruence_density hF hS

end PI.UnitaryGroupMassFormula.LocDensCorank
