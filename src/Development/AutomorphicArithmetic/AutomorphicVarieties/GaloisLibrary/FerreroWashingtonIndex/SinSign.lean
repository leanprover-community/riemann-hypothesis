module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

@[expose] public section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.sinSign :
    ∀ x : ℝ, 0 ≤ x → Real.sin (Real.pi * x) ≠ 0 → (Real.sin (Real.pi * x) < 0 ↔ Odd ⌊x⌋₊) := by
  intro x hx hne
  set n := ⌊x⌋₊ with hn
  have h0 : (0 : ℝ) ≤ x - n := sub_nonneg.mpr (Nat.floor_le hx)
  have h1 : x - n ≤ 1 := by
    have := Nat.lt_floor_add_one x
    linarith
  have hs : 0 ≤ Real.sin (Real.pi * (x - n)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le h0)
      (mul_le_of_le_one_right Real.pi_pos.le h1)
  have he : Real.sin (Real.pi * x) = (-1) ^ n * Real.sin (Real.pi * (x - n)) := by
    rw [← Real.sin_add_nat_mul_pi]
    congr 1
    ring
  rw [he] at hne ⊢
  have hpos : 0 < Real.sin (Real.pi * (x - n)) :=
    lt_of_le_of_ne hs (fun h => hne (by rw [← h, mul_zero]))
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, one_mul]
    exact ⟨fun hlt => absurd hlt (not_lt.mpr hpos.le), fun ho => absurd ho (Nat.not_odd_iff_even.mpr h)⟩
  · rw [h.neg_one_pow]
    exact ⟨fun _ => h, fun _ => by linarith⟩
