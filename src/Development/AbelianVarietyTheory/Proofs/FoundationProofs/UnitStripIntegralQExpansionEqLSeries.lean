module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumParsevalQExpansionHorizontalLineStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralEqIteratedStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.Analysis.MellinTransform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

private theorem im_ofComplex_pt (x y : ℝ) (hy : 0 < y) :
    (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by
  have h : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  rw [ofComplex_apply_of_im_pos h]
  simp [UpperHalfPlane.im]

theorem strip_eq_LSeries : ∀ (h b : ℕ → ℂ) (w : ℝ), 0 < w → PolyB h → PolyB b → h 0 = 0 →
    LSeriesSummable (fun n => conj (h n) * b n) w →
    IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ)) strip →
    ∫ τ in strip, conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ) =
      ((Real.Gamma w / (4 * π) ^ w : ℝ) : ℂ) * LSeries (fun n => conj (h n) * b n) w := by
  intro h b w hw hh hb h0 hL hint
  set a : ℕ → ℂ := fun n => conj (h n) * b n with ha
  set P : ℝ → ℂ := fun y => ∫ x in (0 : ℝ)..1,
    conj (qs h (ofComplex (x + y * Complex.I))) * qs b (ofComplex (x + y * Complex.I)) with hPd
  have h4 : (0 : ℝ) < 4 * π := by positivity
  have ha0 : a 0 = 0 := by simp [ha, h0]
  have h1 : (∫ τ in strip, conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ)) = mellin P (w : ℂ) := by
    rw [GlobalTheory.T.unitStrip_integral_eq_iterated.2 _ hint]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy : 0 < y := hy
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    simp only [im_ofComplex_pt _ _ hy, hPd, smul_eq_mul]
    rw [intervalIntegral.integral_mul_const]
    have e : ((y : ℂ) ^ ((w : ℂ) - 1)) = ((y ^ (w + 1) : ℝ) : ℂ) / (y : ℂ) ^ 2 := by
      have e1 : (w : ℂ) - 1 = ((w - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [e1, ← Complex.ofReal_cpow hy.le]
      have e2 : y ^ (w - 1) = y ^ (w + 1) / y ^ 2 := by
        have : w - 1 = (w + 1) - ((2 : ℕ) : ℝ) := by push_cast; ring
        rw [this, Real.rpow_sub hy, Real.rpow_natCast]
      rw [e2]; push_cast; ring
    rw [e]; ring
  have hsum : Summable fun n : ℕ => ‖a n‖ / (4 * π * n) ^ ((w : ℂ).re) := by
    have hs2 := (hL.norm).div_const ((4 * π) ^ w)
    refine hs2.congr (fun n => ?_)
    rw [LSeries.norm_term_eq, Complex.ofReal_re]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha0]
    · rw [if_neg hn.ne', Real.mul_rpow h4.le (Nat.cast_nonneg n), div_div, mul_comm ((n : ℝ) ^ w)]
  have h2 := hasSum_mellin (a := a) (p := fun n : ℕ => 4 * π * n) (F := P) (s := (w : ℂ))
    (fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · left; exact ha0
      · right; positivity)
    (by simpa using hw)
    (fun y hy => by
      have := GlobalTheory.T.hasSum_parseval_qExpansion_horizontal_line h b y hh hb hy
      refine this.congr_fun (fun n => ?_)
      simp only [ha]
      congr 2
      ring_nf)
    hsum
  rw [h1, ← h2.tsum_eq, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha0]
  rw [LSeries.term_of_ne_zero hn.ne', ← Complex.ofReal_cpow (by positivity), Real.mul_rpow h4.le (Nat.cast_nonneg n),
    Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, Complex.Gamma_ofReal]
  push_cast
  field_simp

end GlobalTheory.EisM
