module

public import Formalism.StatementOC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZF

open ArithmeticFunction in
theorem zetaPrimeSum_nonneg_and_le (y : ℝ) (hy : 1 ≤ y) :
    0 ≤ Formalism.Sz y ∧ Formalism.Sz y ≤ y * y * Real.log y := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊y⌋₊, 0 ≤ ArithmeticFunction.vonMangoldt n * (y / n - 1) ∧
      ArithmeticFunction.vonMangoldt n * (y / n - 1) ≤ Real.log y * y := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < n := by linarith
    have hny : (n : ℝ) ≤ y := (Nat.cast_le.mpr hn2).trans (Nat.floor_le hy0)
    have h1 : 0 ≤ y / n - 1 := by
      rw [sub_nonneg, le_div_iff₀ hnpos]
      linarith
    have h2 : y / n - 1 ≤ y := by
      have : y / n ≤ y := div_le_self hy0 hn1'
      linarith
    have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log y :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnpos hny)
    exact ⟨mul_nonneg ArithmeticFunction.vonMangoldt_nonneg h1, mul_le_mul hΛ h2 h1 hlog⟩
  unfold Formalism.Sz
  refine ⟨Finset.sum_nonneg fun n hn => (hterm n hn).1, ?_⟩
  calc ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / n - 1)
        ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Real.log y * y := Finset.sum_le_sum fun n hn => (hterm n hn).2
    _ = (⌊y⌋₊ : ℝ) * (Real.log y * y) := by simp
    _ ≤ y * (Real.log y * y) := mul_le_mul_of_nonneg_right (Nat.floor_le hy0) (mul_nonneg hlog hy0)
    _ = y * y * Real.log y := by ring

theorem abs_zetaPrimeSumError_le_of_one_le (y : ℝ) (hy : 1 ≤ y) :
    |Formalism.Gz y| ≤ y * (y * Real.log y + Real.log y + 2) := by
  obtain ⟨hS0, hS1⟩ := zetaPrimeSum_nonneg_and_le y hy
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hp1 : 0 ≤ y * Real.log y := mul_nonneg hy0 hlog
  have hp2 : 0 ≤ y * (y * Real.log y) := mul_nonneg hy0 hp1
  have hγy : Real.eulerMascheroniConstant * y ≤ y := by nlinarith
  have hγy0 : 0 ≤ Real.eulerMascheroniConstant * y := by nlinarith
  unfold Formalism.Gz
  rw [abs_le]
  constructor <;> nlinarith

end Formalism.ZF
