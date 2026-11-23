module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset UpperTheory.V.Bern

private theorem bernoulli_poly_reflection (k : ℕ) (x : ℚ) :
    (Polynomial.bernoulli k).eval (1 - x) = (-1) ^ k * (Polynomial.bernoulli k).eval x := by
  exact Polynomial.bernoulli_eval_one_sub k x

theorem UpperTheory.V.Bern.b_shift :
    ∀ (N k a : ℕ), 0 < N → bcoef N k (a + N) = bcoef N k a + (k : ℚ) * (a : ℚ) ^ (k - 1) ∧ (∀ m : ℕ, 0 < m → bcoef (m * N) k (m * a) = (m : ℚ) ^ ((k : ℤ) - 1) * bcoef N k a) ∧ (a ≤ N → bcoef N k (N - a) = (-1) ^ k * bcoef N k a) := by
  intro N k a hN
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨?_, ?_, ?_⟩
  · unfold bcoef
    have e : ((a + N : ℕ) : ℚ) / N = 1 + (a : ℚ) / N := by
      push_cast; field_simp; ring
    rw [e, Polynomial.bernoulli_eval_one_add, mul_add]
    congr 1
    rcases k with _ | k
    · simp
    · have : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
      rw [this, zpow_natCast, Nat.add_sub_cancel, div_pow]
      field_simp
  · intro m hm
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    unfold bcoef
    have e : ((m * a : ℕ) : ℚ) / ((m * N : ℕ) : ℚ) = (a : ℚ) / N := by
      push_cast; field_simp
    rw [e, Nat.cast_mul, mul_zpow, mul_assoc]
  · intro h
    unfold bcoef
    have e : ((N - a : ℕ) : ℚ) / N = 1 - (a : ℚ) / N := by
      rw [Nat.cast_sub h]; field_simp
    rw [e, bernoulli_poly_reflection]
    ring
