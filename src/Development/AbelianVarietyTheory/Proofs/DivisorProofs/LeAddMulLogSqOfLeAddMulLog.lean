module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Filter Topology

namespace GlobalTheory

theorem le_add_mul_log_sq_of_le_add_mul_log :
    ∀ (α β r s : ℝ), 0 ≤ α → 0 ≤ β → 1 ≤ r → r ≤ s → s ≤ α + β * Real.log r →
      s ≤ α + β * Real.log ((α + 2 * β + 1) ^ 2) := by
  intro α β r s hα hβ hr hrs hs
  have hr0 : 0 < r := by linarith
  set t := Real.sqrt r with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg r
  have htt : t * t = r := Real.mul_self_sqrt hr0.le
  have ht1 : 1 ≤ t := by
    by_contra h
    push_neg at h
    nlinarith
  have htpos : 0 < t := by linarith
  have hlog : Real.log r ≤ 2 * t - 2 := by
    have h1 : Real.log r = 2 * Real.log t := by
      rw [← htt, Real.log_mul htpos.ne' htpos.ne']; ring
    have h2 := Real.log_le_sub_one_of_pos htpos
    linarith
  have hle : t ≤ α + 2 * β + 1 := by
    by_contra h
    push_neg at h
    nlinarith [mul_lt_mul_of_pos_left h htpos, mul_nonneg hα (sub_nonneg.mpr ht1),
      mul_le_mul_of_nonneg_left hlog hβ]
  have hrc : r ≤ (α + 2 * β + 1) ^ 2 := by
    rw [← htt]; nlinarith
  have hl : Real.log r ≤ Real.log ((α + 2 * β + 1) ^ 2) := Real.log_le_log hr0 hrc
  nlinarith [mul_le_mul_of_nonneg_left hl hβ]

end GlobalTheory
