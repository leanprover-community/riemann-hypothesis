module

public import Formalism.PeriodIntegrals.WeylProd
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Rat.BigOperators

@[expose] public section

namespace PI.WeylProdWork

open Finset

noncomputable def wg (x : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i < j then (x i - x j) / ((j : ℝ) - (i : ℝ)) else 1

theorem denom_eq (n : ℕ) :
    ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) =
      ∏ i ∈ range n, ((i.factorial : ℕ) : ℝ) := by
  have h1 : ∀ i ∈ range n, ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) = (((n - 1 - i).factorial : ℕ) : ℝ) := by
    intro i hi
    rw [mem_range] at hi
    rw [Finset.prod_Ico_eq_prod_range]
    have e : n - (i + 1) = n - 1 - i := by omega
    rw [e, ← Finset.prod_range_add_one_eq_factorial]
    push_cast
    exact Finset.prod_congr rfl (fun t _ => by ring)
  rw [Finset.prod_congr rfl h1]
  exact Finset.prod_range_reflect (fun i => ((i.factorial : ℕ) : ℝ)) n

theorem row_eq (x : ℕ → ℝ) (n i : ℕ) :
    ∏ j ∈ range n, wg x i j =
      (∏ j ∈ Ico (i + 1) n, (x i - x j)) / ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) := by
  rw [← Finset.prod_div_distrib]
  by_cases hin : i + 1 ≤ n
  · rw [← Finset.prod_range_mul_prod_Ico _ hin]
    have h1 : ∏ j ∈ range (i + 1), wg x i j = 1 := Finset.prod_eq_one (fun j hj => by
      rw [mem_range] at hj
      simp [wg, show ¬ i < j by omega])
    rw [h1, one_mul]
    exact Finset.prod_congr rfl (fun j hj => by
      rw [mem_Ico] at hj
      simp [wg, show i < j by omega])
  · push_neg at hin
    rw [Finset.Ico_eq_empty_of_le (by omega), Finset.prod_empty]
    exact Finset.prod_eq_one (fun j hj => by
      rw [mem_range] at hj
      simp [wg, show ¬ i < j by omega])

theorem weylProd : PI.WeylProd := by
  intro n μ w c hμ
  have hterm : ∀ i j : Fin n,
      (((if i < j then (((μ i : ℤ) : ℚ) - ((μ j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) /
        (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) else 1 : ℚ)) : ℝ) = wg (shiftSeq w) i j := by
    intro i j
    unfold wg
    by_cases h : i < j
    · have h' : (i : ℕ) < (j : ℕ) := h
      rw [if_pos h, if_pos h']
      have hi : shiftSeq w (i : ℕ) = ((w i : ℤ) : ℝ) - ((i : ℕ) : ℝ) := by
        simp [shiftSeq]
      have hj : shiftSeq w (j : ℕ) = ((w j : ℤ) : ℝ) - ((j : ℕ) : ℝ) := by
        simp [shiftSeq]
      rw [hi, hj, hμ i, hμ j]
      push_cast
      ring
    · have h' : ¬ (i : ℕ) < (j : ℕ) := h
      rw [if_neg h, if_neg h', Rat.cast_one]
  rw [Rat.cast_prod]
  simp only [Rat.cast_prod]
  rw [Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => hterm i j))]
  have e1 : ∀ i : ℕ, ∏ j : Fin n, wg (shiftSeq w) i (j : ℕ) = ∏ j ∈ range n, wg (shiftSeq w) i j :=
    fun i => Fin.prod_univ_eq_prod_range (wg (shiftSeq w) i) n
  simp only [e1]
  rw [Fin.prod_univ_eq_prod_range (fun i => ∏ j ∈ range n, wg (shiftSeq w) i j) n]
  simp only [row_eq]
  rw [Finset.prod_div_distrib, denom_eq]
  rfl

end PI.WeylProdWork
