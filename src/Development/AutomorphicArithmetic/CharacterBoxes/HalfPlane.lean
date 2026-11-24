module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

def Claim.HalfPlane : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def Claim.Strip : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def Claim.Zeta : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2

open Complex

/-- An extra Euler factor cannot vanish to the right of zero. -/
theorem Claim.factor_ne_zero {M : ℕ} (ψ : DirichletCharacter ℂ M) {s : ℂ} (hs : 0 < s.re) (p : ℕ)
    (hp : p.Prime) : (1 : ℂ) - ψ p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : ψ p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hn : ‖ψ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖ψ p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ := by
          gcongr; exact ψ.norm_le_one _
      _ < 1 := by rw [one_mul]; exact hpow
  rw [h1, norm_one] at hn
  exact lt_irrefl _ hn
