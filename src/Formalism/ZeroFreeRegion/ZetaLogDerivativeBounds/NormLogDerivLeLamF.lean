module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LSeries.RiemannZeta
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
public import Mathlib.NumberTheory.LSeries.Dirichlet
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation

noncomputable section

namespace Formalism.ZF

def lamF (σ : ℝ) : ℝ := ∑' n, ‖term ↗Λ (σ : ℂ) n‖

lemma norm_logDeriv_le_lamF {s : ℂ} (hs : 1 < s.re) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ lamF s.re := by
  have hL := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hsum : Summable fun n => ‖term ↗Λ s n‖ := summable_norm_iff.2 (LSeriesSummable_vonMangoldt hs)
  have heq : (fun n => ‖term ↗Λ s n‖) = fun n => ‖term ↗Λ ((s.re : ℝ) : ℂ) n‖ := by
    funext n
    rw [norm_term_eq, norm_term_eq]
    simp
  calc ‖deriv riemannZeta s / riemannZeta s‖ = ‖L ↗Λ s‖ := by rw [hL, neg_div, norm_neg]
    _ ≤ ∑' n, ‖term ↗Λ s n‖ := norm_tsum_le_tsum_norm hsum
    _ = lamF s.re := by rw [heq]; rfl

lemma term_vonMangoldt_real (σ : ℝ) (n : ℕ) :
    term ↗Λ (σ : ℂ) n = ((‖term ↗Λ (σ : ℂ) n‖ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have h : term ↗Λ (σ : ℂ) n = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n),
        Complex.ofReal_natCast]
    rw [h, Complex.norm_real, Real.norm_of_nonneg (div_nonneg vonMangoldt_nonneg (by positivity))]

lemma lamF_eq_norm {σ : ℝ} (hσ : 1 < σ) : lamF σ = ‖L ↗Λ (σ : ℂ)‖ := by
  have h : L ↗Λ (σ : ℂ) = ((lamF σ : ℝ) : ℂ) := by
    rw [LSeries, lamF, Complex.ofReal_tsum]
    exact tsum_congr fun n => term_vonMangoldt_real σ n
  rw [h, Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ lamF σ from tsum_nonneg fun n => norm_nonneg _)]

lemma lamF_anti {σ τ : ℝ} (hσ : 1 < σ) (h : σ ≤ τ) : lamF τ ≤ lamF σ := by
  have hs : ∀ x : ℝ, 1 < x → Summable fun n => ‖term ↗Λ (x : ℂ) n‖ := fun x hx =>
    summable_norm_iff.2 (LSeriesSummable_vonMangoldt (by simpa using hx))
  unfold lamF
  refine Summable.tsum_le_tsum (fun n => ?_) (hs τ (by linarith)) (hs σ hσ)
  rw [norm_term_eq, norm_term_eq]
  split_ifs with hn
  · rfl
  · simp only [ofReal_re]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hn1 h)

end Formalism.ZF
