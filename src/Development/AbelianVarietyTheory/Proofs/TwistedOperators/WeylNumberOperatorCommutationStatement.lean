module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylNumberOperatorCommutation
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

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.weyl_number_operator_commutation_alt : ∀ (V A κ : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Ring A] [Algebra ℂ A] [Fintype κ] (J : V ≃ₗᵢ[ℝ] V) (e : OrthonormalBasis κ ℝ V) (D a c : V → A) (N : A), (∀ x, J (J x) = -x) → (∀ u v, D (u + v) = D u + D v) → (∀ (r : ℝ) v, D (r • v) = (r : ℂ) • D v) → (∀ u v, D u * D v - D v * D u = (2 * Real.pi * Complex.I * (inner ℝ u (J v) : ℝ) : ℂ) • 1) → (∀ z, c z = D z - Complex.I • D (J z)) → (∀ z, a z = -(D z + Complex.I • D (J z))) → N = ∑ j, c (e j) * a (e j) → (∀ z, a z * c z - c z * a z = ((4 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) • 1) ∧ (∀ z, N * c z = c z * (N + ((8 * Real.pi : ℝ) : ℂ) • 1)) ∧ (∀ z, N * a z = a z * (N - ((8 * Real.pi : ℝ) : ℂ) • 1)) ∧ ∀ z, D z ∈ Submodule.span ℂ (Set.range (fun j => a (e j)) ∪ Set.range fun j => c (e j)) := by
  exact @GlobalTheory.weyl_number_operator_commutation
