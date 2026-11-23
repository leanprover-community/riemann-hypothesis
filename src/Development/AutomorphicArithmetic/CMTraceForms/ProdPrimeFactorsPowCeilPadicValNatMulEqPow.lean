module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.PrimeFin
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Nat.Factorization.Defs

@[expose] public section

theorem UpperTheory.prod_primeFactors_pow_ceil_padicValNat_mul_eq_pow :
    ∀ (Q T a b : ℕ), Q ≠ 0 → ∏ p ∈ Q.primeFactors.filter Nat.Prime,
      p ^ (T * ⌈(padicValNat p Q : ℝ) * (a : ℝ)⌉.toNat + ⌈(padicValNat p Q : ℝ) * (b : ℝ)⌉.toNat) = Q ^ (T * a + b) := by
  intro Q T a b hQ
  have hc : ∀ m n : ℕ, ⌈(m : ℝ) * (n : ℝ)⌉.toNat = m * n := by
    intro m n
    rw [← Nat.cast_mul, Int.ceil_natCast, Int.toNat_natCast]
  have hf : Q.primeFactors.filter Nat.Prime = Q.primeFactors :=
    Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp
  have hQ' : ∏ p ∈ Q.primeFactors, p ^ (Q.factorization p) = Q := by
    simpa only [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hQ
  rw [hf]
  conv_rhs => rw [← hQ', ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [hc, hc, ← pow_mul, Nat.factorization_def Q (Nat.prime_of_mem_primeFactors hp),
    Nat.padicValNat_def]
  congr 1
  ring
