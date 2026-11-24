module

public import Formalism.PeriodIntegrals.AreaLat
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

namespace PI.AreaLatWork

open PI

lemma im_conj_mul_combo (w₁ w₂ : ℂ) (m n m' n' : ℤ) :
    ((starRingEnd ℂ) (m • w₁ + n • w₂) * (m' • w₁ + n' • w₂)).im
      = ((m * n' - n * m' : ℤ) : ℝ) * ((starRingEnd ℂ) w₁ * w₂).im := by
  simp only [zsmul_eq_mul, map_add (f := _), map_mul, map_intCast, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]
  push_cast
  ring

lemma im_integral (w₁ w₂ : ℂ) :
    ∀ a ∈ lat2 w₁ w₂, ∀ b ∈ lat2 w₁ w₂,
      ∃ n : ℤ, ((starRingEnd ℂ) a * b).im = n * ((starRingEnd ℂ) w₁ * w₂).im := by
  intro a ha b hb
  obtain ⟨m, n, rfl⟩ := (AddSubgroup.mem_closure_pair (x := w₁) (y := w₂)).mp ha
  obtain ⟨m', n', rfl⟩ := (AddSubgroup.mem_closure_pair (x := w₁) (y := w₂)).mp hb
  exact ⟨m * n' - n * m', im_conj_mul_combo w₁ w₂ m n m' n'⟩

theorem areaLat : PI.AreaLat := by
  intro w₁ w₂ hne
  refine ⟨?_, im_integral w₁ w₂⟩
  unfold PI.area
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨abs_pos.mpr hne, w₁, ?_, w₂, ?_, rfl⟩
    · exact AddSubgroup.subset_closure (Set.mem_insert _ _)
    · exact AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · rintro a ⟨ha, x, hx, y, hy, rfl⟩
    obtain ⟨n, hn⟩ := im_integral w₁ w₂ x hx y hy
    rw [hn, abs_mul] at ha ⊢
    have hn0 : (n : ℝ) ≠ 0 := by
      intro h0
      rw [h0, abs_zero, zero_mul] at ha
      exact lt_irrefl _ ha
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by exact_mod_cast hn0)
    have h2 := mul_le_mul_of_nonneg_right hn1 (abs_nonneg (((starRingEnd ℂ) w₁ * w₂).im))
    linarith

end PI.AreaLatWork
