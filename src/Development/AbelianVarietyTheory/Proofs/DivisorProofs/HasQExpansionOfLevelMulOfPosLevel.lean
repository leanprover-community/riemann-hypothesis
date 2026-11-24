module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

private lemma hasSum_conv_mul_of_multiplicative {a b : ℕ → ℂ} {e : ℕ → ℂ} {x y : ℂ}
    (he : ∀ m n, e (m + n) = e m * e n)
    (ha : HasSum (fun n => a n * e n) x) (hb : HasSum (fun n => b n * e n) y) :
    HasSum (fun n => conv a b n * e n) (x * y) := by
  have hna : Summable fun n => ‖a n * e n‖ := summable_norm_iff.mpr ha.summable
  have hnb : Summable fun n => ‖b n * e n‖ := summable_norm_iff.mpr hb.summable
  have hS : HasSum (fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (a p.1 * e p.1) * (b p.2 * e p.2)) (x * y) := by
    rw [← ha.tsum_eq, ← hb.tsum_eq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hna hnb]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hna hnb).of_norm.hasSum
  convert hS using 1
  funext n
  rw [conv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, he]
  ring

private lemma mvExp_add_character_germs (N : ℕ) (τ : ℍ) (m n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((m + n : ℕ) : ℂ) * τ / N) =
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * τ / N) *
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / N) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem HasQ.mul_conv {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ * g τ) (conv a b) :=
  fun τ => hasSum_conv_mul_of_multiplicative (mvExp_add_character_germs N τ) (hf τ) (hg τ)

theorem hasQ_mul_conv : ∀ (N : ℕ) (f g : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N g b →
    HasQ N (fun τ => f τ * g τ) (conv a b) := by
  intro N f g a b _ hf hg τ
  exact hasSum_conv_mul_of_multiplicative (mvExp_add_character_germs N τ) (hf τ) (hg τ)

end GlobalTheory.QFam
