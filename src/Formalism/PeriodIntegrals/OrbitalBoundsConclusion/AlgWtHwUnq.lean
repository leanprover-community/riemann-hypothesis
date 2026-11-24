module

public import Formalism.PeriodIntegrals.AlgWtHwUnq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.DensityFirstBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GeneralLinearReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GlueStepSubstitution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem algebraic_weight_highest_unique (L : Type) [Field L] [NumberField L] [NumberField.IsCMField L] (n : ℕ) : PI.AlgWtHwUnq.Stmt L n :=
  fun a τ lam lam' h1 h2 =>
    PI.UnitaryGroupMassFormula.HwConjInf.glue_holds_var PI.UnitaryGroupMassFormula.HwConjInf.density_induction PI.UnitaryGroupMassFormula.HwConjInf.general_linear_reduction L n a τ lam lam' h1 h2
