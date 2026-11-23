module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RealGaussianFourierTransform
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
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.real_gaussian_fourier_transform : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S P : Matrix ι ι ℝ), S.IsSymm → S.det ≠ 0 → P.PosDef → P * S⁻¹ * P = S → ∃ c : ℂ → ℂ, ∀ τ : ℂ, 0 < τ.im → ‖c τ‖ = (Real.sqrt ‖τ‖ ^ Fintype.card ι)⁻¹ ∧ c τ * c (-τ⁻¹) = 1 ∧ Integrable (fun x : ι → ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) * ((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) - (Real.pi : ℂ) * (τ.im : ℂ) * ((x ⬝ᵥ (P *ᵥ x) : ℝ) : ℂ))) ∧ ∀ y : ι → ℝ, ((Real.sqrt |S.det| : ℝ) : ℂ) * ∫ x : ι → ℝ, Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) * ((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) - (Real.pi : ℂ) * (τ.im : ℂ) * ((x ⬝ᵥ (P *ᵥ x) : ℝ) : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (S *ᵥ y) : ℝ) : ℂ)) = c τ * Complex.exp ((Real.pi : ℂ) * Complex.I * ((-τ⁻¹).re : ℂ) * ((y ⬝ᵥ (S *ᵥ y) : ℝ) : ℂ) - (Real.pi : ℂ) * ((-τ⁻¹).im : ℂ) * ((y ⬝ᵥ (P *ᵥ y) : ℝ) : ℂ)) := by
  exact @GlobalTheory.CompanionTheory.SW.GaussOne.fourier_gaussian_real_place
