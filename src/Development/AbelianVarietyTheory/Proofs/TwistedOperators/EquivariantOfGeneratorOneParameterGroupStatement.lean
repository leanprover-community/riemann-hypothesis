module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfGeneratorOneParameterGroup
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.equivariant_of_generator_oneParameterGroup : ∀ (σ Z H : Type) [Finite σ] [AddCommGroup H] [Module ℂ H] (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Z → ℂ)) (R : ℝ → Module.End ℂ (Z → ℂ)) (L : Module.End ℂ (MvPolynomial σ ℂ)) (U : ℝ → Module.End ℂ H) (B : MvPolynomial σ ℂ →ₗ[ℂ] H) (Λ : Set (H →ₗ[ℂ] ℂ)), Function.Injective pt → R 0 = 1 → (∀ s t, R (s + t) = R s * R t) → (∀ t φ, ∃ ψ, ψ.totalDegree ≤ φ.totalDegree ∧ R t (pt φ) = pt ψ) → (∀ φ z, HasDerivAt (fun t : ℝ => R t (pt φ) z) (pt (L φ) z) 0) → U 0 = 1 → (∀ s t, U (s + t) = U s * U t) → (∀ x, (∀ l ∈ Λ, l x = 0) → x = 0) → (∀ l ∈ Λ, ∀ t, l ∘ₗ U t ∈ Λ) → (∀ l ∈ Λ, ∀ φ, HasDerivAt (fun t : ℝ => l (U t (B φ))) (l (B (L φ))) 0) → ∀ φ φ', pt φ' = R 1 (pt φ) → B φ' = U 1 (B φ) := by
  first | exact @GlobalTheory.OneParamEquivariance.equivariant_of_generator | exact GlobalTheory.OneParamEquivariance.equivariant_of_generator | (intros; apply GlobalTheory.OneParamEquivariance.equivariant_of_generator <;> assumption)
