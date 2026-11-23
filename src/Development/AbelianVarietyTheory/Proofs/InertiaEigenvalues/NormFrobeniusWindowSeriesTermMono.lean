module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PMonE

namespace GlobalTheory.PMonE

theorem iter_frobSymm_pow {F : Type*} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (m : ℕ) (y : F) : (((frobeniusEquiv F p).symm)^[m] y) ^ p ^ m = y := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, frobeniusEquiv_symm_pow_p]

theorem norm_pw_mono {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (k : ℤ) (y y' : F) (hy : ‖y‖ ≤ ‖y'‖) : ‖pw p k y‖ ≤ ‖pw p k y'‖ := by
  unfold pw
  split_ifs with hk
  · rw [norm_pow, norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hy _
  · set m := (-k).toNat
    have hN : p ^ m ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    have e1 := iter_frobSymm_pow p m y
    have e2 := iter_frobSymm_pow p m y'
    by_contra hc
    push_neg at hc
    have := pow_lt_pow_left₀ hc (norm_nonneg _) hN
    rw [← norm_pow, ← norm_pow, e1, e2] at this
    linarith

theorem term_norm_mono : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π x : Fin h → F), (∀ j, ‖x j‖ ≤ ‖π j‖) → ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam x r j n‖ ≤ ‖term p ϖ lam π r j n‖ := by
  intro F _ p _ _ _ h ϖ lam π x hx r j n
  unfold term
  rw [norm_mul, norm_mul (lam j * _)]
  exact mul_le_mul_of_nonneg_left (norm_pw_mono p _ _ _ (hx j)) (norm_nonneg _)

end GlobalTheory.PMonE
