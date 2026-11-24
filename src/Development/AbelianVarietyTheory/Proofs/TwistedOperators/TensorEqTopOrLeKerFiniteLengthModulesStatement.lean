module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorEqTopOrLeKerFiniteLengthModules
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

@[expose] public section

open scoped TensorProduct


theorem _root_.GlobalTheory.T.tensor_eq_top_or_le_ker_finiteLength_modules : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ P₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup P₀] [Module ℂ P₀]
    {M P : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i)))
    (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (p₀ : M₀ →ₗ[ℂ] P₀) (p : ∀ i, M i →ₗ[ℂ] P i),
    Module.rank ℂ M₀ ≤ Cardinal.aleph0 → (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) →
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M₀), StrictMono N →
        (∀ j, Rel₀ ≤ N j ∧ ∀ g ∈ Op₀, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → (∀ g ∈ Op₀, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker p₀) →
    Rel₀ ≤ LinearMap.ker p₀ → (∀ g ∈ Op₀, ∀ x ∈ LinearMap.ker p₀, g x ∈ LinearMap.ker p₀) →
    (∀ i, ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (M i)), StrictMono N →
        (∀ j, Rel i ≤ N j ∧ ∀ g ∈ Op i, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ i, ∀ N : Submodule ℂ (M i), Rel i ≤ N → (∀ g ∈ Op i, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker (p i)) →
    (∀ i, Rel i ≤ LinearMap.ker (p i)) → (∀ i, ∀ g ∈ Op i, ∀ x ∈ LinearMap.ker (p i), g x ∈ LinearMap.ker (p i)) →
    ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) →
      (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j), x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) →
      (∀ g ∈ Op₀, ∀ t ∈ N, TensorProduct.map g LinearMap.id t ∈ N) →
      (∀ i, ∀ g ∈ Op i, ∀ t ∈ N, TensorProduct.map LinearMap.id
        (PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)) t ∈ N) →
      N = ⊤ ∨ N ≤ LinearMap.ker (TensorProduct.map p₀ (PiTensorProduct.map p)) := by
  first | exact @GlobalTheory.TensHead.tensor_eq_top_or_le_ker_map | exact GlobalTheory.TensHead.tensor_eq_top_or_le_ker_map | (intros; apply GlobalTheory.TensHead.tensor_eq_top_or_le_ker_map <;> assumption)
