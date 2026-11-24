module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal Topology

namespace GlobalTheory.GrowthShift

theorem eventually_mul_inv_pow_le (D e : ℕ) {a : ℝ≥0∞} (ha : a < 1) :
    ∀ᶠ k : ℕ in atTop, a * ((k : ℝ≥0∞) ^ D)⁻¹ ≤ (((k + e : ℕ) : ℝ≥0∞) ^ D)⁻¹ := by
  lift a to NNReal using ha.ne_top
  have ha' : (a : ℝ) < 1 := by exact_mod_cast ha
  have h1 : Tendsto (fun k : ℕ => ((k : ℝ) / (k + (e : ℝ))) ^ D) atTop (𝓝 1) := by
    simpa using (tendsto_natCast_div_add_atTop (e : ℝ)).pow D
  filter_upwards [h1.eventually (lt_mem_nhds ha'), eventually_gt_atTop 0] with k hk hk0
  have hkR : (0 : ℝ) < k := Nat.cast_pos.2 hk0
  have hke : (0 : ℝ) < ((k : ℝ) + e) ^ D := by positivity
  rw [div_pow, lt_div_iff₀ hke] at hk
  have h2 : (a : ℝ≥0∞) * ((k + e : ℕ) : ℝ≥0∞) ^ D ≤ (k : ℝ≥0∞) ^ D := by
    have h3 : a * ((k + e : ℕ) : NNReal) ^ D ≤ (k : NNReal) ^ D := by
      rw [← NNReal.coe_le_coe]
      push_cast
      exact hk.le
    exact_mod_cast h3
  have n0 : (k : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hk0.ne')
  have nt : (k : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top k)
  rw [ENNReal.le_inv_iff_mul_le, mul_right_comm, ← div_eq_mul_inv, ENNReal.div_le_iff n0 nt, one_mul]
  exact h2

theorem growth_shift_le : ∀ (D e : ℕ) (r : ℕ → ℕ∞), growth D (fun k => r (k + e)) ≤ growth D r := by
  intro D e r
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  rw [growth, growth, ← ENNReal.limsup_const_mul_of_ne_top ha.ne_top,
    ← Filter.limsup_nat_add (fun τ : ℕ => (D.factorial : ℝ≥0∞) * (r τ : ℝ≥0∞) / (τ : ℝ≥0∞) ^ D) e]
  refine limsup_le_limsup ((eventually_mul_inv_pow_le D e ha).mono fun k hk => ?_)
  simp only [div_eq_mul_inv]
  rw [mul_left_comm]
  exact mul_le_mul_right hk _

end GlobalTheory.GrowthShift
