module

import Development.WeilBound.ThetaLifts.LeviDeterminants.NormIteratedFDerivIdLeOneAdd
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyMulGaussianBounded
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.GaussDerivBound

open scoped Nat

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_id_le_one_add' (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (id : E → E) x‖ ≤ 1 + ‖x‖ := by
  rcases j with _ | n
  · rw [norm_iteratedFDeriv_zero]; simp
  · rw [← norm_iteratedFDeriv_fderiv,
      show fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E from funext fun _ => fderiv_id]
    rcases n with _ | n
    · rw [norm_iteratedFDeriv_zero]
      exact (ContinuousLinearMap.norm_id_le).trans (by linarith [norm_nonneg x])
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
      simp only [Pi.zero_apply, norm_zero]
      positivity

theorem norm_iteratedFDeriv_diag_le' (B : E →L[ℝ] E →L[ℝ] ℝ) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => B y y) x‖ ≤ ‖B‖ * (2 ^ n * (1 + ‖x‖) ^ 2) := by
  apply PositivityTheory.ThKF0.Lib.norm_iteratedFDeriv_diag_le <;> assumption

theorem norm_iteratedFDeriv_rexp' (i : ℕ) (y : ℝ) : ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_exp_const_mul i 1) y
  simp only [one_mul, one_pow] at h
  rw [show (fun s => Real.exp s) = Real.exp from rfl] at h
  rw [h, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]

theorem exists_bound_poly_mul_exp' (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ C, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ N * Real.exp (-(c * r ^ 2)) ≤ C := by
  first
  | exact @_root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded
  | exact _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded
  | (apply _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded ..)

theorem weighted_bound : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c α : ℝ), 0 < c → α < 1 → ∀ (k m : ℕ),
    ∃ K : ℝ, ∀ y : E, ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
      Real.exp (c * α * ‖y‖ ^ 2) ≤ K := by
  intro E _ _ c α hc hα k m
  set B : E →L[ℝ] E →L[ℝ] ℝ := (-c) • innerSL ℝ with hBdef
  have hBy : ∀ y : E, B y y = -(c * ‖y‖ ^ 2) := fun y => by
    simp [hBdef, real_inner_self_eq_norm_sq]
    left
    first | exact real_inner_self_eq_norm_sq y | simp [innerSL_apply, real_inner_self_eq_norm_sq] | rfl
  have hfun : (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) =
      Complex.ofRealLI ∘ (Real.exp ∘ fun y : E => B y y) := by
    funext y
    simp only [Function.comp_apply, Complex.ofRealLI_apply, hBy, Complex.ofReal_exp, Complex.ofReal_neg]
  have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => B y y) := B.contDiff.clm_apply contDiff_id
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Real.exp ∘ fun y : E => B y y) := Real.contDiff_exp.comp hq
  have hc' : 0 < c * (1 - α) := mul_pos hc (by linarith)
  obtain ⟨C, hC⟩ := exists_bound_poly_mul_exp' (c * (1 - α)) hc' (k + 2 * m)
  refine ⟨m ! * (2 * (‖B‖ + 1)) ^ m * C, fun x => ?_⟩
  have hn : ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  rw [hfun, LinearIsometry.norm_iteratedFDeriv_comp_left _ hg.contDiffAt hn]
  have hfb := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := fun y : E => B y y)
    Real.contDiff_exp hq hn x (C := Real.exp (B x x)) (D := 2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2)
    (fun i _ => (norm_iteratedFDeriv_rexp' i _).le) (fun i hi _ => by
      have hB0 := norm_nonneg B
      have hx0 := norm_nonneg x
      have a1 : ‖B‖ ≤ (‖B‖ + 1) ^ i :=
        le_trans (by linarith) (le_self_pow₀ (by linarith) (by omega))
      have a2 : (1 + ‖x‖) ^ 2 ≤ ((1 + ‖x‖) ^ 2) ^ i :=
        le_self_pow₀ (by nlinarith) (by omega)
      calc ‖iteratedFDeriv ℝ i (fun y : E => B y y) x‖ ≤ ‖B‖ * (2 ^ i * (1 + ‖x‖) ^ 2) :=
            norm_iteratedFDeriv_diag_le' B i x
        _ = 2 ^ i * ‖B‖ * (1 + ‖x‖) ^ 2 := by ring
        _ ≤ 2 ^ i * (‖B‖ + 1) ^ i * ((1 + ‖x‖) ^ 2) ^ i := by gcongr
        _ = (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ i := by rw [mul_pow, mul_pow])
  rw [hBy x] at hfb
  have hx0 := norm_nonneg x
  have hB0 := norm_nonneg B
  have hexp : Real.exp (-(c * ‖x‖ ^ 2)) * Real.exp (c * α * ‖x‖ ^ 2) =
      Real.exp (-(c * (1 - α) * ‖x‖ ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (Real.exp ∘ fun y : E => B y y) x‖ * Real.exp (c * α * ‖x‖ ^ 2)
      ≤ (1 + ‖x‖) ^ k * (m ! * Real.exp (-(c * ‖x‖ ^ 2)) * (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ m) *
          Real.exp (c * α * ‖x‖ ^ 2) := by
        gcongr
        linarith
    _ = m ! * (2 * (‖B‖ + 1)) ^ m * ((1 + ‖x‖) ^ (k + 2 * m) *
          (Real.exp (-(c * ‖x‖ ^ 2)) * Real.exp (c * α * ‖x‖ ^ 2))) := by
        rw [show (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ m = (2 * (‖B‖ + 1)) ^ m * (1 + ‖x‖) ^ (2 * m) by
          rw [mul_pow, pow_mul], pow_add]; ring
    _ ≤ m ! * (2 * (‖B‖ + 1)) ^ m * C := by
        rw [hexp]
        gcongr
        exact hC ‖x‖ hx0

end GlobalTheory.GaussDerivBound
