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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem hasQ_vadd : ∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) (b : ℝ), HasQ N f a →
    HasQ N (fun τ => f (b +ᵥ τ))
      (fun n => a n * Complex.exp (2 * Real.pi * Complex.I * n * b / N)) := by
  intro N f a b h τ
  have h1 := h (b +ᵥ τ)
  have he : (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * b / N) *
      Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) =
      fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * ((b +ᵥ τ : ℍ) : ℂ) / N) := by
    funext n
    rw [UpperHalfPlane.coe_vadd, mul_assoc (a n), ← Complex.exp_add]
    congr 2
    ring
  show HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * b / N) *
      Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) (f (b +ᵥ τ))
  rw [he]
  exact h1

end GlobalTheory.QFam
