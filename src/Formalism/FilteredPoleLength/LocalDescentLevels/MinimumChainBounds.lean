module

public import Formalism.FilteredPoleLength.ReducedBasisBounds.AlternatingBinomial
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.LatticeBaseChangeAlt

open Real

private theorem pow_sub_pow_le_mul_sub_mul_pow {x y M : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hxM : x ≤ M) (hM : 1 ≤ M) :
    ∀ n : ℕ, x ^ n - y ^ n ≤ n * (x - y) * M ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hx : 0 ≤ x := hy.trans hyx
    have hxy : 0 ≤ x - y := sub_nonneg.2 hyx
    have hMn : 0 ≤ M ^ n := pow_nonneg (by linarith) n
    have hyn : y ^ n ≤ M ^ n := by
      first
      | exact pow_le_pow_left hy (hyx.trans hxM) n
      | exact pow_le_pow_left₀ hy (hyx.trans hxM) n
      | (gcongr <;> linarith)
    have hMn1 : M ^ n ≤ M ^ (n + 1) := by
      rw [pow_succ]; nlinarith [mul_nonneg hMn (sub_nonneg.2 hM)]
    have h1 : x * (x ^ n - y ^ n) ≤ x * (n * (x - y) * M ^ n) := mul_le_mul_of_nonneg_left ih hx
    have h2 : x * (n * (x - y) * M ^ n) ≤ M * (n * (x - y) * M ^ n) :=
      mul_le_mul_of_nonneg_right hxM (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hxy) hMn)
    have h3 : (x - y) * y ^ n ≤ (x - y) * M ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (hyn.trans hMn1) hxy
    have e : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by ring
    have e2 : M * (n * (x - y) * M ^ n) = n * (x - y) * M ^ (n + 1) := by ring
    rw [e]
    push_cast
    linarith

theorem detProductRest : DetProductRest := by
  intro i c ε hε hε1
  have h2 : (0 : ℝ) ≤ 2 ^ c := by positivity
  have hM : (1 : ℝ) ≤ 2 ^ c + 1 := by linarith
  have key := pow_sub_pow_le_mul_sub_mul_pow h2 (by linarith : (2 : ℝ) ^ c ≤ 2 ^ c + ε)
    (by linarith : (2 : ℝ) ^ c + ε ≤ 2 ^ c + 1) hM i
  have e : (2 : ℝ) ^ c + ε - 2 ^ c = ε := by ring
  rw [e] at key
  rw [pow_mul]
  exact key

end Formalism.LatticeBaseChangeAlt
