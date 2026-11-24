module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianMulMultilinearDiagonalMemSchwartzSubmoduStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumGaussianConvolutionSeriesTermIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSchwartzOfSummableSeminormsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSeminormGaussianConvolutionSeriesTermStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open FourierTransform MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.ConvSeries

theorem mem_of_conv_gaussian : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    ∀ (b c : ℝ), 0 < b → 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (h u : SchwartzMap E ℂ),
      (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) →
      u ∈ M := by
  intro E _ _ _ _ _ M hM hℓ b c hb hc hg h u hu
  have ht : ∀ j, ∃ t ∈ M, ∀ y, t y = term b c h j y := by
    intro j
    obtain ⟨t, htM, ht⟩ := GlobalTheory.T.gaussian_mul_multilinear_diagonal_mem_schwartzSubmodule E M hℓ c hc hg j (coef b c h j)
    refine ⟨(((2 * c) ^ j / (j.factorial : ℝ) : ℝ) : ℂ) • t, M.smul_mem _ htM, fun y => ?_⟩
    simp only [SchwartzMap.smul_apply, ht, term, smul_eq_mul]
    ring
  choose t htM hty using ht
  have hs : Summable t := GlobalTheory.T.summable_schwartz_of_summable_seminorms E t (GlobalTheory.T.summable_seminorm_gaussianConvolutionSeriesTerm E b c hb hc h t hty)
  have hL := hs.hasSum
  have hev : ∀ y, (∑' j, t j) y = u y := by
    intro y
    let φ : SchwartzMap E ℂ →L[ℂ] ℂ :=
      (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ E ℂ)
    have h1 : HasSum (fun j => t j y) ((∑' j, t j) y) := hL.mapL φ
    have h2 : HasSum (fun j => t j y) (u y) := by
      rw [hu y]
      exact (GlobalTheory.T.hasSum_gaussianConvolutionSeriesTerm_integral E b c hb hc h y).congr_fun (fun j => hty j y)
    exact h1.unique h2
  have hLu : (∑' j, t j) = u := SchwartzMap.ext hev
  rw [← hLu]
  exact hM.mem_of_tendsto hL (Eventually.of_forall fun s => M.sum_mem fun j _ => htM j)

end GlobalTheory.ConvSeries
