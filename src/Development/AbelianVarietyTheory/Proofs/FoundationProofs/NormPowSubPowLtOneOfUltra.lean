module

public import Formalism.ConjugateSelfDual.Statement
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.PowerDifferenceNorm

theorem norm_pow_sub_pow_lt_one_of_ultra {K : Type*} [NormedCommRing K] [IsUltrametricDist K]
    {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (h : ‖x - y‖ < 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ < 1 := by
  rcases n with _ | n
  · simp
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have e : x ^ (n + 1 + 1) - y ^ (n + 1 + 1)
        = x * (x ^ (n + 1) - y ^ (n + 1)) + (x - y) * y ^ (n + 1) := by ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt ((norm_mul_le _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) hx)) ih
    · have hp : ‖y ^ (n + 1)‖ ≤ 1 :=
        (norm_pow_le' y n.succ_pos).trans (pow_le_one₀ (norm_nonneg _) hy)
      exact lt_of_le_of_lt ((norm_mul_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) hp)) h

theorem norm_pow_sub_pow_lt_one :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {x y : Formalism.ConjugateSelfDual.Qbar l}, ‖x‖ ≤ (1 : ℝ) → ‖y‖ ≤ (1 : ℝ) →
      ‖x - y‖ < (1 : ℝ) → ∀ (n : ℕ), ‖x ^ n - y ^ n‖ < (1 : ℝ) := by
  intro l _ x y hx hy h n
  exact norm_pow_sub_pow_lt_one_of_ultra hx hy h n

end GlobalTheory.PowerDifferenceNorm
