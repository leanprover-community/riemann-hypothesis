module

public import Formalism.FilteredPoleLength.ReducedBasisBounds.FilteredPoleLength
public import Formalism.GelfandTransference.HadamardGelfand.Hadamard
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module Matrix MeasureTheory

theorem complexHadamard : ComplexHadamard := by
  intro n M A hA
  have h1 := Formalism.HadamardInequality.P.hadamard_inequality_holds n M.transpose
  rw [Matrix.det_transpose] at h1
  simp only [Matrix.transpose_apply] at h1
  have hprod : (∏ j, Real.sqrt (∑ i, ‖M i j‖ ^ 2)) ^ 2 = ∏ j, ∑ i, ‖M i j‖ ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ =>
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  refine ⟨?_, ?_⟩
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _)
      (Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _) two_ne_zero).1 ?_
    rw [hprod]
    exact h1
  · have h2 := Formalism.HadamardInequality.P.hadamard_maximum_holds n M A hA
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA ⟨0, hn⟩ ⟨0, hn⟩)
    have h3 : ((Real.sqrt n * A) ^ n) ^ 2 = ((n : ℝ) * A ^ 2) ^ n := by
      rw [← pow_mul, mul_comm n 2, pow_mul, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [h3]
    exact h2

end Formalism.LatticeBaseChangeAlt
