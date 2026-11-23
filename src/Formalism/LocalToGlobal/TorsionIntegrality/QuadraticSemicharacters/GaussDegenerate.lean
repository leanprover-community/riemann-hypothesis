module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section Objects

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def psiT (H : Sesq V) (α : V → ℂ) (z y : V) : ℂ :=
  α z * α y * α (z + y) * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H z y : ℂ))


open Classical in
def tripleSum (H : Sesq V) (α : V → ℂ) (Λ₁ : AddSubgroup V) (S₂ S₃ : Finset V) : ℂ :=
  by classical exact ∑ z ∈ S₃, ∑ y ∈ S₂, if z + y ∈ Λ₁ then psiT H α z y else 0

def tripleMu (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V) (S₂ S₃ : Finset V) : ℂ :=
  ((Real.sqrt (relIdx Λ₁ Λ₃) / (Real.sqrt (relIdx Λ₁ Λ₂) * Real.sqrt (relIdx Λ₂ Λ₃)) : ℝ) : ℂ)
    * tripleSum H α Λ₁ S₂ S₃

structure TripleData (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V) : Prop where
  herm : IsHerm H
  sd₁ : IsSelfDual H Λ₁
  sd₂ : IsSelfDual H Λ₂
  sd₃ : IsSelfDual H Λ₃
  sc₁ : IsSemiChar H Λ₁ α
  sc₂ : IsSemiChar H Λ₂ α
  sc₃ : IsSemiChar H Λ₃ α
  i₁₂ : relIdx Λ₁ Λ₂ ≠ 0
  i₂₁ : relIdx Λ₂ Λ₁ ≠ 0
  i₁₃ : relIdx Λ₁ Λ₃ ≠ 0
  i₃₁ : relIdx Λ₃ Λ₁ ≠ 0
  i₂₃ : relIdx Λ₂ Λ₃ ≠ 0
  i₃₂ : relIdx Λ₃ Λ₂ ≠ 0

end Objects

def TripleFormula : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V),
    TripleData H α Λ₁ Λ₂ Λ₃ → ∀ S₂ S₃ : Finset V, IsReps Λ₁ Λ₂ S₂ → IsReps Λ₂ Λ₃ S₃ →
    ∀ F ∈ fixedBy H α Λ₁, ∀ v,
      inter H α Λ₂ Λ₃ (inter H α Λ₁ Λ₂ F) v = tripleMu H α Λ₁ Λ₂ Λ₃ S₂ S₃ * inter H α Λ₁ Λ₃ F v

def PsiQuadratic : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V),
    TripleData H α Λ₁ Λ₂ Λ₃ →
    (∀ z ∈ Λ₃, ∀ y ∈ Λ₂, z + y ∈ Λ₁ → ∀ z' ∈ Λ₃, ∀ y' ∈ Λ₂, z' + y' ∈ Λ₁ →
      psiT H α (z + z') (y + y') = psiT H α z y * psiT H α z' y'
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H y z' : ℂ))) ∧
    (∀ z ∈ Λ₃, ∀ y ∈ Λ₂, z + y ∈ Λ₁ → ∀ k : ℕ, psiT H α (k • z) (k • y) = psiT H α z y ^ (k ^ 2)) ∧
    (∀ z ∈ Λ₃, ∀ y ∈ Λ₂, z + y ∈ Λ₁ → ‖psiT H α z y‖ = 1) ∧
    (∀ z ∈ Λ₃, ∀ y ∈ Λ₂, z + y ∈ Λ₁ → ∀ u' ∈ Λ₁ ⊓ Λ₃, ∀ u ∈ Λ₁ ⊓ Λ₂, ∀ t ∈ Λ₂ ⊓ Λ₃,
      psiT H α (z + u' + t) (y + u - t) = psiT H α z y)

structure IsQuadFn0 {M : Type*} [AddCommGroup M] (φ : M → ℂ) (b : M → M → ℂ) : Prop where
  add : ∀ x y, φ (x + y) = φ x * φ y * b x y
  left : ∀ x y z, b (x + y) z = b x z * b y z
  sq : ∀ (k : ℕ) (x : M), φ (k • x) = φ x ^ (k ^ 2)
  ne : ∀ x, φ x ≠ 0

def GaussDegenerate : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Fintype M] (φ : M → ℂ) (b : M → M → ℂ), IsQuadFn0 φ b →
    ∑ x, φ x ≠ 0 → ∃ r : ℝ, 0 < r ∧ (∑ x, φ x) ^ 8 = (r : ℂ)

def TripleSumEighth : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V),
    TripleData H α Λ₁ Λ₂ Λ₃ → ∀ S₂ S₃ : Finset V, IsReps Λ₁ Λ₂ S₂ → IsReps Λ₂ Λ₃ S₃ →
    tripleSum H α Λ₁ S₂ S₃ ≠ 0 → ∃ r : ℝ, 0 < r ∧ tripleSum H α Λ₁ S₂ S₃ ^ 8 = (r : ℂ)

def TripleConj : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V),
    TripleData H α Λ₁ Λ₂ Λ₃ → ∀ S₂ S₃ S₂' S₃' : Finset V, IsReps Λ₁ Λ₂ S₂ → IsReps Λ₂ Λ₃ S₃ →
    IsReps Λ₁ Λ₃ S₃' → IsReps Λ₃ Λ₂ S₂' →
    tripleMu H α Λ₁ Λ₃ Λ₂ S₃' S₂' = conj (tripleMu H α Λ₁ Λ₂ Λ₃ S₂ S₃)

def TripleEighth : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V),
    TripleData H α Λ₁ Λ₂ Λ₃ → (∃ F ∈ fixedBy H α Λ₁, F ≠ 0) →
    ∀ S₂ S₃ : Finset V, IsReps Λ₁ Λ₂ S₂ → IsReps Λ₂ Λ₃ S₃ → tripleMu H α Λ₁ Λ₂ Λ₃ S₂ S₃ ^ 8 = 1

end Formalism.L2.Th1.H
