module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierOneParameterIntegral
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

@[expose] public section

open MeasureTheory


theorem _root_.GlobalTheory.T.fourier_one_parameter_integral : ∀ (A : Type) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] (lam : Measure A) [lam.IsAddHaarMeasure] [SFinite lam] (c : ℝ →+ A), Continuous c → ∀ (F G : A → ℂ), Continuous F → Continuous G → Integrable F lam → Integrable G lam → ∀ (χ : AddChar A ℂ), Continuous χ → (∀ x, ‖χ x‖ = 1) → ∀ (f : ℝ), (∀ s : ℝ, χ (c s) = Complex.exp (-(2 * Real.pi * Complex.I * ((s * f : ℝ) : ℂ)))) → (∀ (b : A) (s : ℝ), HasDerivAt (fun t : ℝ => F (b + c t)) (2 * Real.pi * Complex.I * G (b + c s)) s) → ∫ b, G b * χ b ∂lam = (f : ℂ) * ∫ b, F b * χ b ∂lam := by
  exact @GlobalTheory.CompanionTheory.OneParamFourier.integral_mul_char_eq_of_hasDerivAt
