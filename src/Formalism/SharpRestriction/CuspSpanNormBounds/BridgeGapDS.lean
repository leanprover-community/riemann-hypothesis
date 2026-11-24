module

public import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.GapDS

open Formalism.MainNotions.PlaceDegreeData

def thrDS {n : ℕ} (ε : Fin n → Bool) : ℝ := (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1

theorem pOf_le {n : ℕ} (ε : Fin n → Bool) : pOf ε ≤ n := by
  unfold pOf
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem qOf_le {n : ℕ} (ε : Fin n → Bool) : qOf ε ≤ n := by
  unfold qOf
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem thrDS_le {n : ℕ} (ε : Fin n → Bool) : thrDS ε ≤ (n : ℝ) ^ 3 + 1 := by
  unfold thrDS
  have hp : (pOf ε : ℝ) ≤ n := by exact_mod_cast pOf_le ε
  have hq : (qOf ε : ℝ) ≤ n := by exact_mod_cast qOf_le ε
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ pOf ε := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ qOf ε := Nat.cast_nonneg _
  have : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ (n : ℝ) * n * n :=
    mul_le_mul (mul_le_mul_of_nonneg_left hp h0) hq h2 (mul_nonneg h0 h0)
  nlinarith

end Formalism.MainNotions.GapDS

end
