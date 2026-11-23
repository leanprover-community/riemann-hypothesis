module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

@[expose] public section

open Finset

namespace GlobalTheory.LamSize

theorem main : ∀ (C b T T' : ℝ) (r N : ℕ), 0 ≤ C → 3 ≤ b → (N : ℝ) ≤ b → b ^ (-(C * ((2 * r + 2 : ℕ) : ℝ))) ≤ T → b ^ (-(C * ((2 * r + 2 : ℕ) : ℝ))) ≤ T' → 1 ≤ b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ)) ∧ (N : ℝ) * b ^ (11 * (2 * r + 2)) ≤ (b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 * (T * T') := by
  intro C b T T' r N hC hb hN hT hT'
  have hm1 : 1 ≤ 2 * r + 2 := by omega
  generalize 2 * r + 2 = m at *
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine ⟨Real.one_le_rpow hb1 (by positivity), ?_⟩
  have hp : 0 < b ^ (-(C * (m : ℝ))) := Real.rpow_pos_of_pos hb0 _
  have hTT : b ^ (-(C * (m : ℝ))) * b ^ (-(C * (m : ℝ))) ≤ T * T' :=
    mul_le_mul hT hT' hp.le (hp.le.trans hT)
  have key : (b ^ ((6 + C) * (m : ℝ))) ^ 2 * (b ^ (-(C * (m : ℝ))) * b ^ (-(C * (m : ℝ))))
      = b ^ (12 * m) := by
    rw [sq, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  calc (N : ℝ) * b ^ (11 * m) ≤ b * b ^ (11 * m) := by gcongr
    _ = b ^ (11 * m + 1) := by ring
    _ ≤ b ^ (12 * m) := pow_le_pow_right₀ hb1 (by omega)
    _ = _ := key.symm
    _ ≤ _ := by gcongr

end GlobalTheory.LamSize
