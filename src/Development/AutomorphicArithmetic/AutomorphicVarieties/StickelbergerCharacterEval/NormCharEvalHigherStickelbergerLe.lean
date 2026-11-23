module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BUpper
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.GroupRingCharEvalStickelbergerYNeZeroOfParity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Real.Pi.Bounds
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

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.norm_charEval_higherStickelberger_le :
    ∀ {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] (π : (ZMod N)ˣ →* Γ) (χ : Γ →* ℂˣ) (a : ℕ) (ha : a.Coprime N) (k : ℕ), 2 ≤ N → 1 ≤ k → ‖ev ℚ χ (yEl k a ha π)‖ ≤ (sizeY N a k : ℝ) := by
  intro N _ Γ _ π χ a ha k hN hk
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h
      have h' := (Nat.coprime_zero_left N).mp ha
      omega
    · exact h
  rw [groupRingCharEval_stickelbergerY_eq_euler_mul_genBernoulli π χ a ha k hN]
  set d := dirOf π χ
  have hd : ∀ x, ‖d x‖ ≤ 1 := fun x => DirichletCharacter.norm_le_one d x
  have hB := b_upper k (⇑d) (by omega) hd
  have h1 : ‖(1 : ℂ) - (a : ℂ) ^ k * d (a : ZMod N)‖ ≤ 2 * (a : ℝ) ^ k := by
    calc ‖(1 : ℂ) - (a : ℂ) ^ k * d (a : ZMod N)‖
        ≤ ‖(1 : ℂ)‖ + ‖(a : ℂ) ^ k * d (a : ZMod N)‖ := norm_sub_le _ _
      _ ≤ 1 + (a : ℝ) ^ k * 1 := by
          rw [norm_one, norm_mul, norm_pow, Complex.norm_natCast]
          gcongr
          exact hd _
      _ ≤ 2 * (a : ℝ) ^ k := by
          have : (1 : ℝ) ≤ (a : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast ha1)
          linarith
  have hpi : (4 : ℝ) ≤ (2 * Real.pi) ^ k := by
    calc (4 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      _ = (2 * Real.pi) ^ 1 := (pow_one _).symm
      _ ≤ (2 * Real.pi) ^ k := pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hk
  have h2 : ‖genB k ⇑d‖ ≤ (N : ℝ) ^ k * k.factorial := by
    calc ‖genB k ⇑d‖ ≤ 4 * (N : ℝ) ^ k * k.factorial / (2 * Real.pi) ^ k := hB
      _ ≤ (N : ℝ) ^ k * k.factorial := by
        rw [div_le_iff₀ (by positivity)]
        have : 0 ≤ (N : ℝ) ^ k * k.factorial := by positivity
        nlinarith
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [norm_mul, norm_div, norm_neg, Complex.norm_natCast]
  calc ‖(1 : ℂ) - (a : ℂ) ^ k * d (a : ZMod N)‖ * (‖genB k ⇑d‖ / k)
      ≤ 2 * (a : ℝ) ^ k * ((N : ℝ) ^ k * k.factorial) := by
        apply mul_le_mul h1 _ (by positivity) (by positivity)
        rw [div_le_iff₀ (by linarith)]
        nlinarith [norm_nonneg (genB k ⇑d)]
    _ = (sizeY N a k : ℝ) := by
        rw [sizeY]
        push_cast
        ring
