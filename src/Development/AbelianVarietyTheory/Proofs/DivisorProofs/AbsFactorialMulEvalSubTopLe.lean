module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section

namespace GlobalTheory

theorem abs_factorial_mul_eval_sub_top_le (d : ℕ) (p : Polynomial ℚ) (hp : p.natDegree ≤ d) :
    ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℚ) * p.eval (m : ℚ) - (d.factorial : ℚ) * p.coeff d * (m : ℚ) ^ d|
      ≤ C * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
  obtain ⟨C, hC⟩ := exists_nat_ge ((d.factorial : ℚ) * ∑ i ∈ Finset.range d, |p.coeff i|)
  refine ⟨C, fun m => ?_⟩
  have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hf : (0 : ℚ) ≤ d.factorial := Nat.cast_nonneg _
  rw [Polynomial.eval_eq_sum_range' (n := d + 1) (Nat.lt_succ_of_le hp), Finset.sum_range_succ]
  have e : (d.factorial : ℚ) * (∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i + p.coeff d * (m : ℚ) ^ d)
      - (d.factorial : ℚ) * p.coeff d * (m : ℚ) ^ d
      = (d.factorial : ℚ) * ∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i := by ring
  rw [e, abs_mul, abs_of_nonneg hf]
  have hX : (0 : ℚ) ≤ (d : ℚ) * ((m : ℚ) + 1) ^ (d - 1) := by positivity
  have h1 : |∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i|
      ≤ (∑ i ∈ Finset.range d, |p.coeff i|) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' : i < d := Finset.mem_range.mp hi
    rw [abs_mul, abs_of_nonneg (pow_nonneg hm i)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have a1 : (m : ℚ) ^ i ≤ ((m : ℚ) + 1) ^ i := pow_le_pow_left₀ hm (by linarith) i
    have a2 : ((m : ℚ) + 1) ^ i ≤ ((m : ℚ) + 1) ^ (d - 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have a3 : (1 : ℚ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have a4 : (0 : ℚ) ≤ ((m : ℚ) + 1) ^ (d - 1) := by positivity
    exact a1.trans (a2.trans (le_mul_of_one_le_left a4 a3))
  calc _ ≤ (d.factorial : ℚ) * ((∑ i ∈ Finset.range d, |p.coeff i|) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1))) :=
        mul_le_mul_of_nonneg_left h1 hf
    _ = ((d.factorial : ℚ) * ∑ i ∈ Finset.range d, |p.coeff i|) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC hX

end GlobalTheory
