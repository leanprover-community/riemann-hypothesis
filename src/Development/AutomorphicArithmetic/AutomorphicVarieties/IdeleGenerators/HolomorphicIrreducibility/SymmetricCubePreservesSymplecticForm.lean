module

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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

open Polynomial UpperTheory.V.Af Formalism.ConjugateSelfDual
open scoped Matrix

namespace UpperTheory.V.Sd

section Rel

variable {K : Type} [NormedField K] [IsUltrametricDist K]

private def Rl (x y : K) : Prop := ‖y‖ ≤ 1 ∧ ‖x - y‖ < 1

private theorem Rl.left {x y : K} (h : Rl x y) : ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - y) y
  rw [sub_add_cancel] at this
  exact this.trans (max_le h.2.le h.1)


private theorem Rl.mul {x y z w : K} (h : Rl x y) (h' : Rl z w) : Rl (x * z) (y * w) := by
  refine ⟨by rw [norm_mul]; exact mul_le_one₀ h.1 (norm_nonneg _) h'.1, ?_⟩
  rw [show x * z - y * w = x * (z - w) + (x - y) * w by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h.left (norm_nonneg _) h'.2
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h.2 h'.1

end Rel

end UpperTheory.V.Sd
