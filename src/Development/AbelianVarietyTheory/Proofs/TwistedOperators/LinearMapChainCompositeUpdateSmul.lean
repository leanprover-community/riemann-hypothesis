module

public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open GlobalTheory.FunObj

namespace GlobalTheory.ChainSmul

theorem chainTo_update_of_le {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (B : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    ∀ n, n ≤ j₀ → chainTo (Function.update k j₀ B) n = chainTo k n
  | 0, _ => rfl
  | n + 1, h => by
    have hne : n ≠ j₀ := by omega
    show Function.update k j₀ B n ∘ₗ chainTo (Function.update k j₀ B) n = k n ∘ₗ chainTo k n
    rw [Function.update_of_ne hne, chainTo_update_of_le k j₀ B n (by omega)]

theorem chainTo_update_smul {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (c : ℂ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    ∀ n, j₀ < n → chainTo (Function.update k j₀ (c • A)) n = c • chainTo (Function.update k j₀ A) n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    show Function.update k j₀ (c • A) n ∘ₗ chainTo (Function.update k j₀ (c • A)) n =
      c • (Function.update k j₀ A n ∘ₗ chainTo (Function.update k j₀ A) n)
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · have hne : n ≠ j₀ := by omega
      rw [Function.update_of_ne hne, Function.update_of_ne hne, chainTo_update_smul k j₀ c A n h',
        LinearMap.comp_smul]
    · rw [Function.update_self, Function.update_self, chainTo_update_of_le k j₀ _ j₀ le_rfl,
        chainTo_update_of_le k j₀ _ j₀ le_rfl, LinearMap.smul_comp]

end GlobalTheory.ChainSmul
