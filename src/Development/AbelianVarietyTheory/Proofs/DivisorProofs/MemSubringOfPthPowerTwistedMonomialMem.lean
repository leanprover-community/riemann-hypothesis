module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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

@[expose] public section

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem LogDR.round_coeff_mem : ∀ (K : Type) [Field K] (p : ℕ) (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (I J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ) (g : K), 0 < p → AlgChart A x → (∀ j, r j < p) → g ^ p * ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) / ∏ j ∈ I \ J, (x j : K) ∈ A → g * t / ∏ j ∈ I \ J, (x j : K) ∈ A := by
  intro K _ p A n x I J t r g hp hA hr h
  have hP0 : (∏ j ∈ I \ J, (x j : K)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (x j).ne_zero)
  have hQ0 : (∏ j ∈ J, (x j : K)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (x j).ne_zero)
  have hcast : ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) = (t : K) ^ p * ∏ j ∈ J, (x j : K) ^ (r j) := by
    push_cast; rfl
  rw [hcast] at h
  have hpow : ∀ j ∈ J, (x j : K) ^ p = (x j : K) ^ (r j) * (x j : K) * (x j : K) ^ (p - 1 - r j) := by
    intro j _
    rw [← pow_succ, ← pow_add]
    congr 1
    have := hr j
    omega
  have hprod : (∏ j ∈ J, (x j : K)) ^ p = (∏ j ∈ J, (x j : K) ^ (r j)) * (∏ j ∈ J, (x j : K)) *
      ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hpow
  have hS : ∏ j ∈ J ∪ I \ J, (x j : K) = (∏ j ∈ J, (x j : K)) * ∏ j ∈ I \ J, (x j : K) :=
    Finset.prod_union Finset.disjoint_sdiff
  have hB : ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) ∈ A :=
    Subring.prod_mem _ (fun j _ => Subring.pow_mem _ (hA.mem j) _)
  have key : (g * t * ∏ j ∈ J, (x j : K)) ^ p / ∏ j ∈ J ∪ I \ J, (x j : K) =
      (g ^ p * ((t : K) ^ p * ∏ j ∈ J, (x j : K) ^ (r j)) / ∏ j ∈ I \ J, (x j : K)) *
        ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) := by
    rw [hS, mul_pow, mul_pow, hprod]
    field_simp
  have h2 := hA.root (J ∪ I \ J) _ p hp (key ▸ A.mul_mem h hB)
  have e : (g * t * ∏ j ∈ J, (x j : K)) / ∏ j ∈ J ∪ I \ J, (x j : K) = g * t / ∏ j ∈ I \ J, (x j : K) := by
    rw [hS]
    field_simp
  rwa [e] at h2

end GlobalTheory
