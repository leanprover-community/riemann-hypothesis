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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

open Formalism.L2.Th1.H

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def wU (H : Sesq V) (α : V → ℂ) (x : V) : (V → ℂ) →ₗ[ℂ] (V → ℂ) where
  toFun F z := α x * opU H x F z
  map_add' F G := by funext z; simp [opU, mul_add, add_mul]
  map_smul' r F := by funext z; simp [opU, smul_eq_mul]; ring

def cU (H : Sesq V) (A B : AddSubgroup V) (b : B) (a : A) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H (a : V) (b : V) : ℂ))

def wA (H : Sesq V) (α : V → ℂ) (A : AddSubgroup V) (a : A) : (V → ℂ) →ₗ[ℂ] (V → ℂ) := wU H α (a : V)

def wB (H : Sesq V) (α : V → ℂ) (B : AddSubgroup V) (b : B) : (V → ℂ) →ₗ[ℂ] (V → ℂ) := wU H α (b : V)

def GoodLat (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V) : Prop :=
  IsSemiChar H Λ α ∧ Λ ≤ (Λ ⊓ A) ⊔ (Λ ⊓ B) ∧
    (∀ a ∈ A, ∀ b ∈ B, a + b ∈ Λ → a ∈ Λ) ∧
    (∀ a ∈ A, (∀ b ∈ B, b ∈ Λ → ∃ m : ℤ, altE H a b = m) → a ∈ Λ) ∧
    (∀ b ∈ B, (∀ a ∈ A, a ∈ Λ → ∃ m : ℤ, altE H a b = m) → b ∈ Λ)

def volA (A Λ₀ Λ : AddSubgroup V) : ℝ :=
  (((Λ₀ ⊓ A).relIndex (Λ ⊓ A) : ℕ) : ℝ) / (((Λ ⊓ A).relIndex (Λ₀ ⊓ A) : ℕ) : ℝ)

end Formalism.L2.PairingIndexBounds.Mv
