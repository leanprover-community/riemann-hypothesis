module

public import Formalism.PeriodIntegrals.PrimeSums
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MertensLogSum.PrimeLogOverPWork
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MertensLogSum.SLeOfBlock
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MertensLogSum.LogFactorialEqSumLog

@[expose] public section

namespace PI.PrimeLogOverPWork

open Finset in
theorem sum_log_div_prime_le : PI.PrimeLogOverP := by
  intro Y hY Q hQ
  have hN1 : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by simpa using hY.le)
  have hNY : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have h1 : ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ≤ S ⌊Y⌋₊ := by
    unfold S
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpp, hpY⟩ := hQ p hp
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hpp.pos, Nat.le_floor hpY⟩, hpp⟩
    · intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have h2 : S ⌊Y⌋₊ ≤ Real.log ((⌊Y⌋₊ : ℕ) : ℝ) := by
    rcases Nat.lt_or_ge 63 ⌊Y⌋₊ with h | h
    · exact S_le_large _ (by omega)
    · exact S_le_small _ hN1 h
  have h3 : Real.log ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Real.log Y := Real.log_le_log (Nat.cast_pos.mpr hN1) hNY
  linarith

end PI.PrimeLogOverPWork
