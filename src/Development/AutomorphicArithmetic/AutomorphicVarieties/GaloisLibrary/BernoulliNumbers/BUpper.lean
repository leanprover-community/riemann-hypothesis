module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Polybound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_upper :
    ∀ {N : ℕ} (k : ℕ) (Φ : ZMod N → ℂ), 0 < N → (∀ a, ‖Φ a‖ ≤ 1) → ‖genB k Φ‖ ≤ 4 * (N : ℝ) ^ k * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
  intro N k Φ hN hΦ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set C : ℝ := 4 * (k.factorial : ℝ) / (2 * Real.pi) ^ k with hC
  have hterm : ∀ a ∈ Icc 1 N,
      ‖Φ (a : ZMod N) * algebraMap ℚ ℂ (bcoef N k a)‖ ≤ (N : ℝ) ^ ((k : ℤ) - 1) * C := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have hx0 : (0 : ℚ) ≤ (a : ℚ) / N := by positivity
    have hx1 : (a : ℚ) / N ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hN)]
      exact_mod_cast ha.2
    have hb : ‖algebraMap ℚ ℂ (bcoef N k a)‖ =
        (N : ℝ) ^ ((k : ℤ) - 1) * |((Polynomial.eval ((a : ℚ) / N) (Polynomial.bernoulli k) : ℚ) : ℝ)| := by
      rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, bcoef]
      push_cast
      rw [abs_mul, abs_of_pos (zpow_pos hNr _)]
    rw [norm_mul, hb]
    have hp := b_polybound k ((a : ℚ) / N) hx0 hx1
    calc ‖Φ (a : ZMod N)‖ * ((N : ℝ) ^ ((k : ℤ) - 1) *
          |((Polynomial.eval ((a : ℚ) / N) (Polynomial.bernoulli k) : ℚ) : ℝ)|)
        ≤ 1 * ((N : ℝ) ^ ((k : ℤ) - 1) * C) := by
          apply mul_le_mul (hΦ _) _ (by positivity) zero_le_one
          exact mul_le_mul_of_nonneg_left hp (zpow_pos hNr _).le
      _ = (N : ℝ) ^ ((k : ℤ) - 1) * C := one_mul _
  calc ‖genB k Φ‖ ≤ ∑ a ∈ Icc 1 N, ‖Φ (a : ZMod N) * algebraMap ℚ ℂ (bcoef N k a)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a ∈ Icc 1 N, (N : ℝ) ^ ((k : ℤ) - 1) * C := Finset.sum_le_sum hterm
    _ = 4 * (N : ℝ) ^ k * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
          zpow_sub_one₀ hNr.ne', zpow_natCast, hC]
        field_simp
