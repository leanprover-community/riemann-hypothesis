module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierTransformMatrixSpaceInvolution
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

open scoped Matrix

theorem _root_.GlobalTheory.T.fourier_transform_matrix_space_involution : ∀ (m n : ℕ) (C s : ℂ) (k : ℝ), C ≠ 0 → k ≠ 0 → ‖s‖ = 2 * |k| → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, (fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u) ⇑φ))))) 0 = c * ∫ v : Fin m → Fin n → ℂ, φ v := by
  first | exact @GlobalTheory.CompanionTheory.Kloc.Fresnel.value_at_zero | exact GlobalTheory.CompanionTheory.Kloc.Fresnel.value_at_zero | (intros; apply GlobalTheory.CompanionTheory.Kloc.Fresnel.value_at_zero <;> assumption)
