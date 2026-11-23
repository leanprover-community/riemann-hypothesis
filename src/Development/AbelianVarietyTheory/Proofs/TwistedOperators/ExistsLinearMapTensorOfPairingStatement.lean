module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearMapTensorOfPairing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

theorem _root_.GlobalTheory.T.exists_linearMap_tensor_of_pairing : ∀ (V A B H₁ H₂ : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (i₁ : A →ₗ[ℂ] H₁) (i₂ : B →ₗ[ℂ] H₂), Function.Injective i₁ → Function.Injective i₂ → ∀ (φ : H₂ → V →ₗ[ℂ] A) (ψ : H₁ → V →ₗ[ℂ] B), (∀ x y P, inner ℂ x (i₁ (φ y P)) = inner ℂ y (i₂ (ψ x P))) → (∀ P, ∃ E : Submodule ℂ A, FiniteDimensional ℂ E ∧ ∀ y, φ y P ∈ E) → ∃ f : V →ₗ[ℂ] TensorProduct ℂ A B, (∀ P, f P = 0 → ∀ y, φ y P = 0) ∧ (∀ (c : Module.End ℂ V) (a : Module.End ℂ A), (∀ y P, φ y (c P) = a (φ y P)) → f ∘ₗ c = TensorProduct.map a LinearMap.id ∘ₗ f) ∧ (∀ (c : Module.End ℂ V) (b : Module.End ℂ B), (∀ x P, ψ x (c P) = b (ψ x P)) → f ∘ₗ c = TensorProduct.map LinearMap.id b ∘ₗ f) := by
  first | exact @GlobalTheory.PairingTensor.exists_linearMap_tensor | exact GlobalTheory.PairingTensor.exists_linearMap_tensor | (intros; apply GlobalTheory.PairingTensor.exists_linearMap_tensor <;> assumption)
