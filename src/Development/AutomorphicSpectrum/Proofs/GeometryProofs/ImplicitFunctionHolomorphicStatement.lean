module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ImplicitFunctionHolomorphic
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

@[expose] public section

open Filter Topology Metric

theorem _root_.GlobalTheory.T.implicit_function_holomorphic : ∀ (n : ℕ) (I J : Type) [Fintype I] [Fintype J] (Ω : Set ((Fin n → ℂ) × (I → ℂ))) (Φ : (Fin n → ℂ) × (I → ℂ) → (J → ℂ)) (b₀ : Fin n → ℂ) (x₀ : I → ℂ) (L : (I → ℂ) ≃L[ℂ] (J → ℂ)), IsOpen Ω → (b₀, x₀) ∈ Ω → DifferentiableOn ℂ Φ Ω → HasFDerivAt (fun x => Φ (b₀, x)) (L : (I → ℂ) →L[ℂ] (J → ℂ)) x₀ →
  ∃ (ε δ : ℝ) (X : (Fin n → ℂ) × (J → ℂ) → (I → ℂ)), 0 < ε ∧ 0 < δ ∧ X (b₀, Φ (b₀, x₀)) = x₀ ∧
    DifferentiableOn ℂ X (ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε) ∧
    (∀ p ∈ ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε, (p.1, X p) ∈ Ω ∧ Φ (p.1, X p) = p.2 ∧
      ∀ v, fderiv ℂ (fun x => Φ (p.1, x)) (X p) v = 0 → v = 0) ∧
    ∀ b ∈ ball b₀ δ, ∀ x ∈ ball x₀ δ, (b, x) ∈ Ω ∧ Φ (b, x) ∈ ball (Φ (b₀, x₀)) ε ∧ X (b, Φ (b, x)) = x := by
  first | exact @GlobalTheory.CompanionTheory.HoloChart.holomorphic_inverse_with_parameters | exact GlobalTheory.CompanionTheory.HoloChart.holomorphic_inverse_with_parameters | (intros; apply GlobalTheory.CompanionTheory.HoloChart.holomorphic_inverse_with_parameters <;> assumption)
