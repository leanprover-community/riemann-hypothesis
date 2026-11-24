module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open UpperTheory.V.Lit.Geo

private theorem moment_pt (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ k * Real.exp (-Real.pi * x) ≤
      (k.factorial * Real.exp 1) * Real.exp (-Real.pi * (1 / 2 * x)) := by
  have h1 : (1 + x) ^ k / (k.factorial : ℝ) ≤ Real.exp (1 + x) :=
    Real.pow_div_factorial_le_exp (1 + x) (by linarith) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h2 : (1 + x) ^ k ≤ k.factorial * Real.exp (1 + x) := by
    rw [div_le_iff₀ hf] at h1
    linarith
  calc (1 + x) ^ k * Real.exp (-Real.pi * x)
      ≤ k.factorial * Real.exp (1 + x) * Real.exp (-Real.pi * x) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (k.factorial * Real.exp 1) * Real.exp (x + -Real.pi * x) := by
        rw [Real.exp_add, Real.exp_add]
        ring
    _ ≤ (k.factorial * Real.exp 1) * Real.exp (-Real.pi * (1 / 2 * x)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.2
        nlinarith [Real.pi_gt_three]

theorem UpperTheory.moment_bound_of_pointwise_moments :
    Moment := by
  intro N k
  refine ⟨k.factorial * Real.exp 1 * 2 ^ N, by positivity, fun ι q hq => ?_⟩
  obtain ⟨hs1, hle⟩ := hq.2 (1 / 2) 1 (by norm_num) (by norm_num)
  have hnn : ∀ i, 0 ≤ (1 + q i) ^ k * Real.exp (-Real.pi * q i) := fun i => by
    have := hq.1 i
    positivity
  have hpt : ∀ i, (1 + q i) ^ k * Real.exp (-Real.pi * q i) ≤
      (k.factorial * Real.exp 1) * Real.exp (-Real.pi * (1 / 2 * q i)) := fun i => moment_pt k (q i) (hq.1 i)
  have hsum : Summable fun i => (1 + q i) ^ k * Real.exp (-Real.pi * q i) :=
    Summable.of_nonneg_of_le hnn hpt (hs1.mul_left _)
  refine ⟨hsum, ?_⟩
  calc ∑' i, (1 + q i) ^ k * Real.exp (-Real.pi * q i)
      ≤ ∑' i, (k.factorial * Real.exp 1) * Real.exp (-Real.pi * (1 / 2 * q i)) :=
        hsum.tsum_le_tsum hpt (hs1.mul_left _)
    _ = (k.factorial * Real.exp 1) * ∑' i, Real.exp (-Real.pi * (1 / 2 * q i)) := tsum_mul_left
    _ ≤ (k.factorial * Real.exp 1) * ((1 / (1 / 2)) ^ N * ∑' i, Real.exp (-Real.pi * (1 * q i))) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = k.factorial * Real.exp 1 * 2 ^ N * ∑' i, Real.exp (-Real.pi * q i) := by
        rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num]
        simp only [one_mul]
        ring
