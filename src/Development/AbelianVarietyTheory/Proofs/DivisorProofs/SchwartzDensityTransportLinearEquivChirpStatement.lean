module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzDensityTransportLinearEquivChirp
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

open FourierTransform MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.schwartz_density_transport_linearEquiv_chirp : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : V ≃L[ℝ] E) (Q : V →L[ℝ] V →L[ℝ] ℂ) (N : Submodule ℂ (SchwartzMap V ℂ)),
    (∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re) →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ N₂ : Submodule ℂ (SchwartzMap E ℂ),
      (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N₂) ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N₂) ∧
      (∀ (g : SchwartzMap V ℂ) (G : SchwartzMap E ℂ), (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
        (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N₂) ∧
      (Dense (N₂ : Set (SchwartzMap E ℂ)) → Dense (N : Set (SchwartzMap V ℂ))) := by
  first | exact @GlobalTheory.GaussTransport.transport | exact GlobalTheory.GaussTransport.transport | (intros; apply GlobalTheory.GaussTransport.transport <;> assumption)
