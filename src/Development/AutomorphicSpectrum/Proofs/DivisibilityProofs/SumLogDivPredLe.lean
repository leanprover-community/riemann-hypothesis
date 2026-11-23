module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogDivNSqLeTwoStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumPrimeLogDivLeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem sum_log_div_pred_le :
    ∀ (x : ℝ) (S : Finset ℕ), 1 ≤ x → (∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ x) →
      ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ Real.log x + 17 / 5 := by
  intro x S hx hS
  have hsplit : ∀ p ∈ S, Real.log p / ((p : ℝ) - 1)
      = Real.log p / p + Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).1.two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have h1 : ∑ p ∈ S, Real.log p / (p : ℝ) ≤ Real.log x + Real.log 4 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (GlobalTheory.T.sum_prime_log_div_le x hx)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_Iic]
      exact ⟨Nat.le_floor (hS p hp).2, (hS p hp).1⟩
    · intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have h2 : ∑ p ∈ S, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 :=
    GlobalTheory.T.sum_log_div_n_sq_le_two S (fun p hp => (hS p hp).1.two_le)
  have hl4 : Real.log 4 < 7 / 5 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have h := Real.log_two_lt_d9
    norm_num at h
    linarith
  linarith

end GlobalTheory.CompanionTheory.Ar.Small
