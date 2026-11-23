module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSet
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

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

theorem _root_.GlobalTheory.T.heisenberg_smooth_of_weak_derivative_closed_set : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), IsHeis (fun x y => om x y) ρ → ∀ (X : Type) (l : X → B →L[ℂ] ℂ), (∀ x b, ‖l x b‖ ≤ ‖b‖) → (∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) → (∀ x v, ∃ (a : ℂ) (x' : X), ∀ b, l x (ρ v b) = a * l x' b) → ∀ Θ : Set B, (∀ f ∈ Θ, ∀ x, Differentiable ℝ fun v => l x (ρ v f)) → (∀ f ∈ Θ, ∀ z : V, ∃ f' ∈ Θ, ∀ x, HasDerivAt (fun t : ℝ => l x (ρ (t • z) f)) (l x f') 0) → ∀ f ∈ Θ, Sm ρ f := by
  first | exact @GlobalTheory.RealWeil.sm_of_weak_deriv_closed | exact GlobalTheory.RealWeil.sm_of_weak_deriv_closed | (intros; apply GlobalTheory.RealWeil.sm_of_weak_deriv_closed <;> assumption)
