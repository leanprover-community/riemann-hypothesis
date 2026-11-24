module

public import Mathlib.NumberTheory.Padics.PadicIntegers
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

noncomputable section

namespace Formalism.CL.W

structure Base (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra ℤ_[p] A] where
  φA : A →ₐ[ℤ_[p]] A
  γA : A →ₐ[ℤ_[p]] A
  π₀ : A
  q : A
  hq : q = π₀ + algebraMap ℤ_[p] A p
  hφ : ∃ v : A, φA π₀ = π₀ * q ^ (p - 1) * v
  comm : ∀ a, φA (γA a) = γA (φA a)

variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]

structure WachMod (B : Base p A) (η : ℕ) (D : Type) [AddCommGroup D] [Module A D]
    [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D] where
  N : Submodule A D
  φ : D →ₗ[ℤ_[p]] D
  γ : D →ₗ[ℤ_[p]] D
  φ_smul : ∀ (a : A) (x : D), φ (a • x) = B.φA a • φ x
  γ_smul : ∀ (a : A) (x : D), γ (a • x) = B.γA a • γ x
  comm : ∀ x, φ (γ x) = γ (φ x)
  π₀_inj : ∀ x : D, B.π₀ • x = 0 → x = 0
  q_bij : Function.Bijective (fun x : D => B.q • x)
  φ_N : ∀ x ∈ N, B.q ^ η • φ x ∈ N
  γ_N : ∀ x ∈ N, ∃ x' ∈ N, γ x - x = B.π₀ • x'
  γ_qN : ∀ y : D, B.q ^ η • y ∈ N → ∃ y' : D, B.q ^ η • y' ∈ N ∧ γ y - y = B.π₀ • y'

namespace WachMod

variable {B : Base p A} {η : ℕ} {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D]
  [IsScalarTower ℤ_[p] A D] (W : WachMod B η D)

end WachMod

variable {B : Base p A} {η : ℕ}

section Hyp

variable {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[p] D₀] [IsScalarTower ℤ_[p] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[p] D₁] [IsScalarTower ℤ_[p] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[p] D₂] [IsScalarTower ℤ_[p] A D₂]
    {W₀ : WachMod B η D₀} {W₁ : WachMod B η D₁} {W₂ : WachMod B η D₂}

end Hyp

end Formalism.CL.W
