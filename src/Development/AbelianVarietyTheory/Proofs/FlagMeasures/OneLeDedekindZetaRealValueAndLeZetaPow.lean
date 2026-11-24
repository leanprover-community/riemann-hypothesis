module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.LSeries.Dirichlet
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
public import Mathlib.NumberTheory.LSeries.Convolution

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.DedekindZetaBound

theorem term_eq_ofReal (a : ℕ → ℕ) {l : ℕ} (hl : 2 ≤ l) (n : ℕ) :
    LSeries.term (fun n => (a n : ℂ)) (l : ℂ) n = (((a n : ℝ) * ((n : ℝ) ^ l)⁻¹ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : l ≠ 0 := by omega
    simp [this]
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_natCast, div_eq_mul_inv]
    push_cast
    rfl

theorem lseriesHasSum_zeta_pow {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    LSeriesHasSum (fun n => (((ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) n : ℕ) : ℂ)) s
      (riemannZeta s ^ k) := by
  induction k with
  | zero =>
    have := hasSum_single (f := LSeries.term
      (fun n => (((ArithmeticFunction.zeta ^ 0 : ArithmeticFunction ℕ) n : ℕ) : ℂ)) s) 1
      (fun b hb => by
        rcases eq_or_ne b 0 with rfl | h0
        · simp
        · simp [LSeries.term_of_ne_zero h0, ArithmeticFunction.one_apply_ne hb])
    simpa [LSeriesHasSum] using this
  | succ k ih =>
    have := ArithmeticFunction.LSeriesHasSum_mul
      (f := ((ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℂ))
      (g := ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ))
      ih (ArithmeticFunction.LSeriesHasSum_zeta hs)
    rw [← ArithmeticFunction.natCoe_mul] at this
    rw [pow_succ, pow_succ]
    exact this

theorem hasSum_zeta_pow {l : ℕ} (hl : 2 ≤ l) (k : ℕ) :
    HasSum (fun n : ℕ => (((ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) n : ℕ) : ℝ) *
      ((n : ℝ) ^ l)⁻¹) ((∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ^ k) := by
  have hs : 1 < ((l : ℂ)).re := by
    rw [Complex.natCast_re]; exact_mod_cast hl
  have h := lseriesHasSum_zeta_pow hs k
  have e : riemannZeta (l : ℂ) = ((∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l : ℝ) : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, Complex.ofReal_tsum]
    refine tsum_congr fun m => ?_
    rw [Complex.cpow_natCast]
    push_cast
    rfl
  rw [e, ← Complex.ofReal_pow, LSeriesHasSum, funext (term_eq_ofReal _ hl)] at h
  exact Complex.hasSum_ofReal.1 h

theorem one_le_zetaE_and_le : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), 2 ≤ l →
    1 ≤ zetaE E l ∧ zetaE E l ≤ (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ^ Module.finrank ℚ E := by
  intro E _ _ l hl
  have h := hasSum_zeta_pow hl (Module.finrank ℚ E)
  set a : ℕ → ℝ := fun n =>
    (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ l)⁻¹ with ha
  have h0 : ∀ n, 0 ≤ a n := fun n => by positivity
  have hle : ∀ n : ℕ, a n ≤
      (((ArithmeticFunction.zeta ^ Module.finrank ℚ E : ArithmeticFunction ℕ) n : ℕ) : ℝ) *
        ((n : ℝ) ^ l)⁻¹ := fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · have : l ≠ 0 := by omega
      simp [ha, this]
    · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast GlobalTheory.ncard_ideal_absNorm_eq_le E hn
  have hsum : Summable a := Summable.of_nonneg_of_le h0 hle h.summable
  have e : zetaE E l = ∑' n, a n := by
    unfold zetaE dedekindZeta LSeries
    rw [funext (term_eq_ofReal _ hl), ← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [e]
  refine ⟨le_trans ?_ (hsum.le_tsum 1 fun n _ => h0 n), hasSum_le hle hsum.hasSum h⟩
  simp [ha, Ideal.absNorm_eq_one_iff]

end GlobalTheory.DedekindZetaBound
