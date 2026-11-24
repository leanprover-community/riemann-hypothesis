module

public import Mathlib.NumberTheory.NumberField.Basic
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

namespace GlobalTheory.UpperUnitriangularMul

open Matrix

theorem upperUnitriangular_mul {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
    {U W : Matrix (Fin N) (Fin N) E}
    (hU : ∀ a b : Fin N, b < a → U a b = (0 : E)) (hU1 : ∀ a : Fin N, U a a = (1 : E))
    (hW : ∀ a b : Fin N, b < a → W a b = (0 : E)) (hW1 : ∀ a : Fin N, W a a = (1 : E)) :
    (∀ a b : Fin N, b < a → (U * W) a b = (0 : E)) ∧ ∀ a : Fin N, (U * W) a a = (1 : E) := by
  constructor
  · intro a b hba
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro c _
    rcases lt_or_ge c a with h | h
    · rw [hU a c h, zero_mul]
    · rw [hW c b (lt_of_lt_of_le hba h), mul_zero]
  · intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hU1, hW1, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [hU a c h, zero_mul]
      · rw [hW c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

end GlobalTheory.UpperUnitriangularMul
