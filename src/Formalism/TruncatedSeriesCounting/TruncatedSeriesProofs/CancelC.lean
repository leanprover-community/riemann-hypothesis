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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.TruncatedSeriesCounting.R9

open PowerSeries

theorem mem_span_of_C_pow_mul : CancelC := by
  intro O _ _ a v t b g ha hvt hg
  rw [Ideal.mem_span_pair] at hg ⊢
  obtain ⟨p, q, hpq⟩ := hg
  have hdiv : (X : PowerSeries O) ^ b ∣ g - p * C (a ^ (t - v)) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    have h1 := congrArg (PowerSeries.coeff n) hpq
    simp only [map_add (f := _), PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      if_neg (show ¬ b ≤ n by omega), add_zero] at h1
    rw [map_sub, PowerSeries.coeff_mul_C, sub_eq_zero]
    apply mul_left_cancel₀ (pow_ne_zero v ha)
    rw [← h1]
    have ht : a ^ t = a ^ v * a ^ (t - v) := by rw [← pow_add, Nat.add_sub_cancel' hvt]
    rw [ht]
    ring
  obtain ⟨r, hr⟩ := hdiv
  exact ⟨p, r, by linear_combination (-1 : PowerSeries O) * hr⟩

end Formalism.TruncatedSeriesCounting.R9
