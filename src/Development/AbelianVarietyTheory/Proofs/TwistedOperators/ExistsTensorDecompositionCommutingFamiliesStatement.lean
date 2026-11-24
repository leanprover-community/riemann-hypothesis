module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTensorDecompositionCommutingFamilies
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_tensorDecomposition_commutingFamilies : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] (G : ι → Type) (a : ∀ i, G i → Module.End ℂ W), (∀ i j, i ≠ j → ∀ g h, a i g * a j h = a j h * a i g) → (∀ N : Submodule ℂ W, (∀ i g, ∀ x ∈ N, a i g x ∈ N) → N = ⊥ ∨ N = ⊤) → ∃ (X : ι → Type) (_ : ∀ i, AddCommGroup (X i)) (_ : ∀ i, Module ℂ (X i)) (_ : ∀ i, FiniteDimensional ℂ (X i)) (b : ∀ i, G i → Module.End ℂ (X i)) (m : ∀ i, X i →ₗ[ℂ] W) (e : (⨂[ℂ] i, X i) ≃ₗ[ℂ] W), (∀ i, Function.Injective (m i)) ∧ (∀ i g x, m i (b i g x) = a i g (m i x)) ∧ (∀ i, ∀ N : Submodule ℂ (X i), (∀ g, ∀ x ∈ N, b i g x ∈ N) → N = ⊥ ∨ N = ⊤) ∧ ∀ i g (x : ∀ i, X i), e (PiTensorProduct.tprod ℂ (Function.update x i (b i g (x i)))) = a i g (e (PiTensorProduct.tprod ℂ x)) := by
  first | exact @GlobalTheory.TensorDecomp.tensor_decomp | exact GlobalTheory.TensorDecomp.tensor_decomp | (intros; apply GlobalTheory.TensorDecomp.tensor_decomp <;> assumption)
