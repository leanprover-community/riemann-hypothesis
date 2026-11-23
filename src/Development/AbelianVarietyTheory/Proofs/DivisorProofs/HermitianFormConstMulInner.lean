module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory

theorem gaussian_selfPairing_pos (n : ℕ) :
    ∃ r : ℝ, 0 < r ∧ (∫ x, GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin n)) x *
      starRingEnd ℂ (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin n)) x)) = (r : ℂ) := by
  refine ⟨∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2), ?_, ?_⟩
  · rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
    have : 0 < Real.pi / (2 * Real.pi) := by positivity
    positivity
  · rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [GroundTheory.Global.gaussianSchwartz_apply, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring

theorem hermitian_form_eq_smul_l2 : ∀ (n : ℕ) (B : Sch (Fin n) → Sch (Fin n) → ℂ), (∀ h h', B h' h = starRingEnd ℂ (B h h')) →
    (∀ h, 0 ≤ (B h h).re) →
    (∀ f f' g g' : Sch (Fin n), (∫ x, f x * starRingEnd ℂ (g x)) * B g' f' = (∫ x, g' x * starRingEnd ℂ (f' x)) * B f g) →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x) := by
  intro n B hherm hpos hid
  set h₀ : Sch (Fin n) := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin n)) with hh₀
  obtain ⟨r, hr, hs⟩ := gaussian_selfPairing_pos n
  have hb : B h₀ h₀ = ((B h₀ h₀).re : ℂ) := by
    have := hherm h₀ h₀
    apply Complex.ext
    · simp
    · have h2 : (B h₀ h₀).im = -(B h₀ h₀).im := by
        conv_lhs => rw [this]
        simp
      simp; linarith
  refine ⟨(B h₀ h₀).re / r, div_nonneg (hpos h₀) hr.le, fun h h' => ?_⟩
  have key := hid h₀ h' h₀ h
  rw [hs, hb] at key
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp
  linear_combination key

end GlobalTheory
