module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivRiemannZetaLocalZeroSum
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivativeBound
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
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.ZeroFreeRegion.FinalZFR

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology

namespace GlobalTheory.ZeroFreePrincipal

theorem _root_.GlobalTheory.ZeroFreePrincipal.zero_free : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (s : ℂ),
    s ≠ 1 → LFunction (1 : DirichletCharacter ℂ q) s = 0 →
    s.re < 1 - c / Real.log (q * (|s.im| + 2)) := by
  obtain ⟨c₁, hc₁, hζ⟩ := Formalism.ZF.zeroFreeRegion
  refine ⟨min c₁ (1 / 2), by positivity, fun q _ s hs hL => ?_⟩
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  have habs := abs_nonneg s.im
  have hln2 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog2 : Real.log 2 ≤ Real.log (|s.im| + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hL2 : Real.log (|s.im| + 2) ≤ Real.log (q * (|s.im| + 2)) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hcL : min c₁ (1 / 2) / Real.log (q * (|s.im| + 2)) < 1 := by
    rw [div_lt_one (by linarith)]; linarith [min_le_right c₁ (1 / 2)]
  have he : LFunction (1 : DirichletCharacter ℂ q) s =
      (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s :=
    LFunctionTrivChar_eq_mul_riemannZeta hs
  rw [he] at hL
  rcases mul_eq_zero.1 hL with hp | hz
  · obtain ⟨p, hpq, hp0⟩ := Finset.prod_eq_zero_iff.1 hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpq
    have hnorm := congrArg norm (sub_eq_zero.1 hp0).symm
    rw [norm_natCast_cpow_of_pos hpp.pos, norm_one, neg_re,
      Real.rpow_def_of_pos (by exact_mod_cast hpp.pos), Real.exp_eq_one_iff] at hnorm
    have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
    have hre : s.re = 0 := by
      rcases mul_eq_zero.1 hnorm with h | h <;> linarith
    rw [hre]; linarith
  · have hre : s.re < 1 - c₁ / Real.log (|s.im| + 2) := by
      by_contra h; exact hζ s hs (not_lt.1 h) hz
    have : min c₁ (1 / 2) / Real.log (q * (|s.im| + 2)) ≤ c₁ / Real.log (|s.im| + 2) :=
      div_le_div₀ hc₁.le (min_le_left _ _) (by linarith) hL2
    linarith

end GlobalTheory.ZeroFreePrincipal
