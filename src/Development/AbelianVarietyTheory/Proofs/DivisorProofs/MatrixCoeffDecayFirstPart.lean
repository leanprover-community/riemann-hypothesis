module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory

theorem one_add_pow_le_two_pow_mul (a : ℝ) (ha : 0 ≤ a) (N : ℕ) :
    (1 + a) ^ N ≤ 2 ^ N * (1 + a ^ N) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ ≤ 2 ^ N * (1 + a ^ N) := by
        have : 0 ≤ a ^ N := pow_nonneg ha N
        nlinarith [pow_pos (two_pos : (0:ℝ) < 2) N]
  · calc (1 + a) ^ N ≤ (2 * a) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * a ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + a ^ N) := by
        gcongr
        linarith

theorem one_add_norm_le_mul_of_add {E : Type*} [NormedAddCommGroup E] (x p : E) :
    1 + ‖p‖ ≤ (1 + ‖x + p‖) * (1 + ‖x‖) := by
  have h : ‖p‖ ≤ ‖x + p‖ + ‖x‖ := by
    have := norm_sub_le (x + p) x
    simpa using this
  nlinarith [norm_nonneg (x + p), norm_nonneg x, mul_nonneg (norm_nonneg (x + p)) (norm_nonneg x)]

theorem matrixCoeff_pPart_decay : ∀ (n : ℕ) (g g' : Sch (Fin n)) (N : ℕ), ∃ C : ℝ,
    ∀ w : Fin n ⊕ Fin n → ℝ,
      ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖pPart w‖) ^ N ≤ C := by
  intro n g g' N
  set A : ℝ := 2 ^ (N, 0).1 * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) g with hA
  have hg : ∀ y, (1 + ‖y‖) ^ N * ‖g y‖ ≤ A := fun y => by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 0)) (k := N) (n := 0)
      le_rfl le_rfl g y
    rwa [norm_iteratedFDeriv_zero] at this
  set h : EuclideanSpace ℝ (Fin n) → ℝ := fun x => (1 + ‖x‖) ^ N * ‖g' x‖ with hh
  have hint : Integrable h := by
    have i1 := (g'.integrable_pow_mul volume 0).add (g'.integrable_pow_mul volume N)
    refine (i1.const_mul (2 ^ N)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((continuous_const.add continuous_norm).pow N |>.mul g'.continuous.norm).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      simp only [hh, pow_zero, one_mul]
      calc (1 + ‖x‖) ^ N * ‖g' x‖ ≤ (2 ^ N * (1 + ‖x‖ ^ N)) * ‖g' x‖ :=
            mul_le_mul_of_nonneg_right (one_add_pow_le_two_pow_mul _ (norm_nonneg _) N) (norm_nonneg _)
        _ = 2 ^ N * (‖g' x‖ + ‖x‖ ^ N * ‖g' x‖) := by ring
  refine ⟨A * ∫ x, h x, fun w => ?_⟩
  set c : ℝ := (1 + ‖pPart w‖) ^ N with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ x, ‖rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * c ≤ A * h x := fun x => by
    have e : ‖rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ = ‖g (x + pPart w)‖ * ‖g' x‖ := by
      simp [rhoFun, norm_phase]
    rw [e, hc]
    have hp := pow_le_pow_left₀ (by positivity) (one_add_norm_le_mul_of_add x (pPart w)) N
    rw [mul_pow] at hp
    calc ‖g (x + pPart w)‖ * ‖g' x‖ * (1 + ‖pPart w‖) ^ N
        ≤ ‖g (x + pPart w)‖ * ‖g' x‖ * ((1 + ‖x + pPart w‖) ^ N * (1 + ‖x‖) ^ N) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = ((1 + ‖x + pPart w‖) ^ N * ‖g (x + pPart w)‖) * h x := by simp only [hh]; ring
      _ ≤ A * h x := mul_le_mul_of_nonneg_right (hg _) (by positivity)
  calc ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * c
      ≤ (∫ x, ‖rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖) * c :=
        mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) hc0
    _ = ∫ x, ‖rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * c := (integral_mul_const _ _).symm
    _ ≤ ∫ x, A * h x :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
          (hint.const_mul A) (Filter.Eventually.of_forall hpt)
    _ = A * ∫ x, h x := integral_const_mul _ _

end GlobalTheory
