module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.DiscreteHaar
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace PI.NglqJacSplitW

section Mod

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  [LocallyCompactSpace F]

theorem modF_of_ne {a : F} (h : a ≠ 0) :
    modF F a = ((distribHaarChar F (Units.mk0 a h) : ℝ≥0) : ℝ≥0∞) := by
  rw [modF.eq_1]
  simp [h]

theorem modF_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : modF F (a * b) = modF F a * modF F b := by
  rw [modF_of_ne (mul_ne_zero ha hb), modF_of_ne ha, modF_of_ne hb,
    show Units.mk0 (a * b) (mul_ne_zero ha hb) = Units.mk0 a ha * Units.mk0 b hb from Units.ext rfl, map_mul]
  push_cast
  rfl

end Mod

end PI.NglqJacSplitW
