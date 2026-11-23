module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.LaplaceStrip

theorem norm_integrand {α : Type} (ℓ : α → ℝ) (g : α → ℂ) (s : ℂ) (x : α) :
    ‖g x * Complex.exp (s * (ℓ x : ℂ))‖ = ‖g x‖ * Real.exp (s.re * ℓ x) := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

theorem laplace_entire_boundedInStrips {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (ℓ : α → ℝ) (g : α → ℂ)
    (hℓ : Measurable ℓ) (hg : MeasureTheory.AEStronglyMeasurable g μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ ℓ x)
    (hint : ∀ σ : ℝ, MeasureTheory.Integrable (fun x => ‖g x‖ * Real.exp (σ * ℓ x)) μ) :
    Differentiable ℂ (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) := by
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x => g x * Complex.exp (s * (ℓ x : ℂ))) μ := fun s =>
    hg.mul (by fun_prop : Measurable fun x => Complex.exp (s * (ℓ x : ℂ))).aestronglyMeasurable
  have hI : ∀ s : ℂ, Integrable (fun x => g x * Complex.exp (s * (ℓ x : ℂ))) μ := fun s =>
    (hint s.re).mono' (hmeas s) (Filter.Eventually.of_forall fun x => (norm_integrand ℓ g s x).le)
  refine ⟨fun s₀ => ?_, fun a b _ => ⟨∫ x, ‖g x‖ * Real.exp (b * ℓ x) ∂μ, fun s _ hsb => ?_⟩⟩
  · have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun s x => g x * Complex.exp (s * (ℓ x : ℂ)))
      (F' := fun s x => g x * (Complex.exp (s * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))))
      (x₀ := s₀) (bound := fun x => ‖g x‖ * Real.exp ((s₀.re + 2) * ℓ x)) (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall hmeas) (hI s₀)
      (hg.mul (by fun_prop : Measurable fun x =>
        Complex.exp (s₀ * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))).aestronglyMeasurable)
      ?_ (hint _) ?_
    · exact key.2.differentiableAt
    · filter_upwards [hpos] with x hx s hs
      have hre : s.re ≤ s₀.re + 1 := by
        have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
        have h2 : ‖s - s₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hs
        have h3 := (abs_le.mp h1).2
        simp only [Complex.sub_re] at h3
        linarith
      rw [one_mul, ← mul_assoc, norm_mul, norm_integrand, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
      have e1 : Real.exp (s.re * ℓ x) ≤ Real.exp ((s₀.re + 1) * ℓ x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre hx)
      have e2 : ℓ x ≤ Real.exp (ℓ x) := by linarith [Real.add_one_le_exp (ℓ x)]
      have e3 : Real.exp ((s₀.re + 2) * ℓ x) = Real.exp ((s₀.re + 1) * ℓ x) * Real.exp (ℓ x) := by
        rw [← Real.exp_add]; ring_nf
      rw [e3, mul_assoc]
      gcongr
    · exact Filter.Eventually.of_forall fun x s _ => by
        have := (((hasDerivAt_id s).mul_const (ℓ x : ℂ)).cexp).const_mul (g x)
        simpa using this
  · refine norm_integral_le_of_norm_le (hint b) ?_
    filter_upwards [hpos] with x hx
    rw [norm_integrand]
    gcongr

end GlobalTheory.LaplaceStrip
