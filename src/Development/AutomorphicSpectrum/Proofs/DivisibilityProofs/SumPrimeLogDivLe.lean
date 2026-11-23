module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PMertensUpper
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

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem mertens_first_log_four :
    ∀ x : ℝ, 1 ≤ x →
      ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log x + Real.log 4 := by
  intro B hB
  set N := ⌊B⌋₊ with hN
  set P := (Finset.Iic N).filter Nat.Prime with hP
  have hN2 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hB)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNB : (N : ℝ) ≤ B := Nat.floor_le (by linarith)
  have hpos : ∀ p ∈ P, (1 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt.le

  have hle : ∏ p ∈ P, p ^ (N / p) ≤ N ^ N :=
    (Nat.le_of_dvd (Nat.factorial_pos _) (GroundTheory.Heights₂.Heights.Model.prod_pow_div_dvd_factorial N)).trans
      (Nat.factorial_le_pow N)
  have hlog : ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p ≤ N * Real.log N := by
    have hprod : (0 : ℝ) < ∏ p ∈ P, ((p : ℝ) ^ (N / p)) :=
      Finset.prod_pos fun p hp => pow_pos (by linarith [hpos p hp]) _
    have h := Real.log_le_log hprod
      (show ∏ p ∈ P, ((p : ℝ) ^ (N / p)) ≤ (N : ℝ) ^ N by exact_mod_cast hle)
    rw [Real.log_prod (fun p hp => (pow_pos (by linarith [hpos p hp]) _).ne'),
      Real.log_pow] at h
    simpa [Real.log_pow] using h

  have hfloor : ∀ p ∈ P, ((N : ℝ) / p - 1) * Real.log p ≤ ((N / p : ℕ) : ℝ) * Real.log p :=
    fun p hp => mul_le_mul_of_nonneg_right
      (by rw [← Nat.floor_div_eq_div (K := ℝ)]; exact (Nat.sub_one_lt_floor _).le)
      (Real.log_nonneg (hpos p hp))

  have htheta : ∑ p ∈ P, Real.log p ≤ Real.log 4 * N := by
    have h := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) hNpos.le
    have hset : P = (Finset.Ioc 0 ⌊(N : ℝ)⌋₊).filter Nat.Prime := by
      rw [Nat.floor_natCast, hP]
      ext p
      simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, h1⟩, h2⟩
      · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
    rw [hset]; exact h
  have key : (N : ℝ) * ∑ p ∈ P, Real.log p / p - ∑ p ∈ P, Real.log p ≤ N * Real.log N := by
    calc (N : ℝ) * ∑ p ∈ P, Real.log p / p - ∑ p ∈ P, Real.log p
        = ∑ p ∈ P, ((N : ℝ) / p - 1) * Real.log p := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
      _ ≤ ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p := Finset.sum_le_sum hfloor
      _ ≤ N * Real.log N := hlog
  have hS : ∑ p ∈ P, Real.log p / p ≤ Real.log N + Real.log 4 := by
    have : (N : ℝ) * ∑ p ∈ P, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
      rw [mul_add]; linarith
    exact le_of_mul_le_mul_left this hNpos
  have hlogNB : Real.log N ≤ Real.log B := Real.log_le_log hNpos hNB
  linarith

end GlobalTheory.CompanionTheory.Ar.Small
