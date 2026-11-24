module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorMapSurjectiveAndKer
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.piTensorProduct_map_surjective_and_dual_vanishes : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A B : ι → Type) [∀ τ, AddCommGroup (A τ)] [∀ τ, Module ℂ (A τ)] [∀ τ, AddCommGroup (B τ)] [∀ τ, Module ℂ (B τ)] (π : ∀ τ, A τ →ₗ[ℂ] B τ), (∀ τ, Function.Surjective (π τ)) → Function.Surjective (PiTensorProduct.map π) ∧ ∀ l : Module.Dual ℂ (⨂[ℂ] τ, A τ), (∀ (τ : ι) (x : ∀ σ, A σ), π τ (x τ) = 0 → l (PiTensorProduct.tprod ℂ x) = 0) → ∀ z, PiTensorProduct.map π z = 0 → l z = 0 := by
  first | exact @GlobalTheory.TensorKernel.piTensor_map_surjective_and_ker | exact GlobalTheory.TensorKernel.piTensor_map_surjective_and_ker | (intros; apply GlobalTheory.TensorKernel.piTensor_map_surjective_and_ker <;> assumption)
