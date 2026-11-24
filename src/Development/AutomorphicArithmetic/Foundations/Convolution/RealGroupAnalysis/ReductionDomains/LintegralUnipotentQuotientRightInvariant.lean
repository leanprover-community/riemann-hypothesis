module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.WtA
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.WtEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.WtOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.lintegral_unipotent_quotient_right_invariant :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (u : G1 F → ℝ≥0∞), Measurable u → (∀ b g, u (nU b * g) = u g) → ∀ g₀, (M.J0 M₀ fun g => u (g * g₀)) = M.J0 M₀ u := by
  intro F _ _ M₀ u hu hinv g₀
  obtain ⟨β, hβ⟩ := UpperTheory.ConvolutionTheory.R2.M.wtEx F
  haveI := M₀.right
  have hone := UpperTheory.ConvolutionTheory.R2.M.wtOne F β hβ
  have hm : ∀ h : G1 F, Measurable fun g : G1 F => g * h := fun h => measurable_mul_const h
  have h1 := UpperTheory.ConvolutionTheory.R2.M.wtA F M₀ β (fun g => u (g * g₀)) 1 hβ.1 hone (hu.comp (hm g₀))
    (fun b g => by rw [mul_assoc, hinv])
  have h2 := UpperTheory.ConvolutionTheory.R2.M.wtA F M₀ (fun g => β (g * g₀⁻¹)) u 1 (hβ.1.comp (hm g₀⁻¹))
    (fun g => by simpa only [mul_assoc] using hone (g * g₀⁻¹)) hu hinv
  have h3 := lintegral_mul_right_eq_self (μ := M₀.μ) (fun g => u g * β (g * g₀⁻¹)) g₀
  simp only [mul_inv_cancel_right] at h3
  rw [one_mul] at h1 h2
  rw [← h1, ← h2, h3]
