module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem le_two_mul_ediv {x m T h : ℤ} (hm : 0 < m) (hT : 4 * m ≤ 5 * T) (hh : 0 ≤ h)
    (hx : 3 * h ≤ 4 * (x - m)) : h ≤ 2 * T * (x / m) := by
  have h1 : m * (x / m) + x % m = x := Int.mul_ediv_add_emod x m
  have h2 : x % m < m := Int.emod_lt_of_pos x hm
  have h3 : 0 ≤ x / m := Int.ediv_nonneg (by omega) hm.le
  have h4 : 4 * m * (x / m) ≤ 5 * T * (x / m) := mul_le_mul_of_nonneg_right hT h3
  have h5 : 0 ≤ T * (x / m) := mul_nonneg (by omega) h3
  nlinarith

theorem divided_gaps : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ (a b : Fin N), (b : ℕ) = a + 1 → (((b : ℕ) ≠ W.p → (W.T : ℤ) + W.Dd + 2 + 2 * N ≤ W.u1 τ a - W.u1 τ b) ∧ ((b : ℕ) = W.p → W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) ∧ W.h0 ≤ 4 * W.T * (W.u1 τ a - W.u1 τ b - 3 * N)) ∧ ((b : ℕ) ≠ W.p → W.kc ≤ (a : ℕ) → W.h0 ≤ 4 * W.T * (W.u1 τ a - W.u1 τ b))) := by
  intro ι _ N W H hD τ a b hab
  have hq := (hD τ).2 a b hab
  obtain ⟨g1, g2, g3⟩ := H.h4 τ a b hab
  obtain ⟨k1, k2⟩ := H.h2
  have c0 := H.weightConst_nonneg
  have h1 : 4 * (W.Dd : ℤ) + 4 ≤ W.T := by exact_mod_cast H.h1
  have hm : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
  have hT : 4 * ((W.T : ℤ) + W.Dd + 1) ≤ 5 * (W.T : ℤ) := by omega
  have hh : 0 ≤ W.h0 := by omega
  refine ⟨fun hb => ?_, fun hb => ?_, fun hb ha => ?_⟩
  · rw [hq, if_neg hb]
    refine Int.le_ediv_of_mul_le hm ?_
    have := g1 hb
    have h0 : (0 : ℤ) ≤ (W.T : ℤ) + W.Dd + 2 + 2 * N := by positivity
    nlinarith
  · have := g3 hb
    have key : W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) := by
      rw [hq, if_pos hb]
      exact le_two_mul_ediv hm hT hh (by omega)
    exact ⟨key, by nlinarith⟩
  · have := g2 ha
    have key : W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) := by
      rw [hq, if_neg hb]
      exact le_two_mul_ediv hm hT hh (by omega)
    nlinarith

end GlobalTheory.MeanTop
