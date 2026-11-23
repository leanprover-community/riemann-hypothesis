module

public import Formalism.TruncatedSeriesCounting.LengthQuotientLeOfPowSMul
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.TruncatedSeriesCounting.R9

open PowerSeries

theorem mem_span_of_X_pow_mul : CancelQ := by
  intro O _ _ a η b g hg
  rw [Ideal.mem_span_pair] at hg ⊢
  obtain ⟨F, G, hFG⟩ := hg
  have hX : (X : PowerSeries O) ^ η ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  by_cases ha : a = 0
  · subst ha
    refine ⟨0, G, ?_⟩
    have h1 : (X : PowerSeries O) ^ η * (G * X ^ b) = X ^ η * g := by
      rw [← hFG, map_zero, mul_zero, zero_add, pow_add]
      ring
    rw [zero_mul, zero_add]
    exact mul_left_cancel₀ hX h1
  · have hdvd : (X : PowerSeries O) ^ η ∣ F := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      have h1 : (X : PowerSeries O) ^ η ∣ F * C a := by
        have h0 : F * C a = X ^ η * (g - G * X ^ b) := by
          rw [mul_sub, ← hFG, pow_add]
          ring
        rw [h0]
        exact dvd_mul_right _ _
      rw [PowerSeries.X_pow_dvd_iff] at h1
      have h2 := h1 m hm
      rw [mul_comm, PowerSeries.coeff_C_mul] at h2
      exact (mul_eq_zero.mp h2).resolve_left ha
    obtain ⟨F', rfl⟩ := hdvd
    refine ⟨F', G, ?_⟩
    apply mul_left_cancel₀ hX
    rw [← hFG, pow_add]
    ring

end Formalism.TruncatedSeriesCounting.R9
