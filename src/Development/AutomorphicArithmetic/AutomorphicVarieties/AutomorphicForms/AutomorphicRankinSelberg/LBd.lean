module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.NumberTheory.ZetaValues
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.V.Af.Rs.lBd :
    UpperTheory.V.Af.Rs.LBd := by
  intro L _ ψ s hs
  set f : ℕ → ℂ := fun n => ψ n / ((n : ℝ) ^ (2 * s) : ℝ) with hf
  set g : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 with hg
  have hs2 : (2 * s) ≠ 0 := by linarith
  have hbd : ∀ n, ‖f n‖ ≤ g n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hf, hg, Real.zero_rpow hs2]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hpos : (0 : ℝ) < (n : ℝ) ^ (2 * s) := Real.rpow_pos_of_pos (by linarith) _
      have hle : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ (2 * s) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      rw [Real.rpow_two] at hle
      simp only [hf, hg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      calc ‖ψ n‖ / (n : ℝ) ^ (2 * s) ≤ 1 / (n : ℝ) ^ (2 * s) :=
            div_le_div_of_nonneg_right (DirichletCharacter.norm_le_one ψ _) hpos.le
        _ ≤ 1 / (n : ℝ) ^ 2 := one_div_le_one_div_of_le (by positivity) hle
  have hgs : HasSum g (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have hsum : Summable f := Summable.of_norm_bounded hgs.summable hbd
  refine ⟨hsum, ?_⟩
  have hg2 : HasSum (fun n => g (n + 2)) (Real.pi ^ 2 / 6 - 1) := by
    have := (hasSum_nat_add_iff' (f := g) 2).mpr hgs
    simpa [Finset.sum_range_succ, hg] using this
  have htail : ‖∑' n, f (n + 2)‖ ≤ Real.pi ^ 2 / 6 - 1 :=
    tsum_of_norm_bounded hg2 (fun n => hbd (n + 2))
  have hsplit : UpperTheory.V.Af.Rs.Lps ψ s = 1 + ∑' n, f (n + 2) := by
    rw [UpperTheory.V.Af.Rs.Lps, ← hsum.sum_add_tsum_nat_add 2]
    simp [Finset.sum_range_succ, hf, Real.zero_rpow hs2]
  have hpi : Real.pi ^ 2 / 6 - 1 ≤ 3 / 4 := by
    have h1 := Real.pi_lt_d2
    have h0 := Real.pi_pos
    nlinarith
  rw [hsplit]
  constructor
  · have := norm_sub_norm_le (1 : ℂ) (-(∑' n, f (n + 2)))
    rw [sub_neg_eq_add, norm_neg, norm_one] at this
    linarith
  · have := norm_add_le (1 : ℂ) (∑' n, f (n + 2))
    rw [norm_one] at this
    linarith
