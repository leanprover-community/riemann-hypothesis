module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.Inversion
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Fourier.FourierTransform

@[expose] public section

open MeasureTheory FourierTransform

theorem UpperTheory.eq_zero_at_one_of_fourierIntegral_eq_zero :
    ∀ (G : ℝ → ℂ), MeasureTheory.Integrable G → ContinuousAt G 1 →
        (∀ u : ℝ, ∫ y : ℝ, G y * Complex.exp (2 * Real.pi * Complex.I * ((y * u : ℝ) : ℂ)) = 0) → G 1 = 0 := by
  intro G hG hc h
  have hF : 𝓕 G = 0 := by
    funext w
    have h1 := h (-w)
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [Pi.zero_apply]
    rw [← h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hint : Integrable (𝓕 G) := by rw [hF]; exact integrable_zero _ _ _
  have key := hG.fourierInv_fourier_eq hint hc
  rw [← key, hF]
  simp [Real.fourierInv_eq']
