module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.InnerAutomorphism

section Inner

variable {A : Type*} (R : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

def innerAut (u : Aˣ) : A ≃ₐ[R] A where
  toFun x := (u : A) * x * ((u⁻¹ : Aˣ) : A)
  invFun x := ((u⁻¹ : Aˣ) : A) * x * (u : A)
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_mul' x y := by simp [mul_assoc]
  map_add' x y := by simp [mul_add, add_mul]
  commutes' r := by rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

end Inner

section Bounded

variable {K n : Type*} [NormedField K]

def EntriesBounded (M : Matrix n n K) (c : ℝ) : Prop :=
  ∀ i j, ‖M i j‖ ≤ c

end Bounded

section DropLast

variable (K : Type*) [Semiring K] (d : ℕ)

def dropLast : (Fin (d + 1) → K) →ₗ[K] (Fin d → K) where
  toFun x i := x i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end DropLast

section Split

variable {ι : Type*} [DecidableEq ι] (F : ι → Type*)

def sigmaSplit (j : ι) : (Σ i, F i) ≃ F j ⊕ (Σ i : {i // i ≠ j}, F i.1) where
  toFun p := if h : p.1 = j then Sum.inl (h ▸ p.2) else Sum.inr ⟨⟨p.1, h⟩, p.2⟩
  invFun s := Sum.elim (fun x => ⟨j, x⟩) (fun q => ⟨q.1.1, q.2⟩) s
  left_inv := by
    rintro ⟨i, x⟩
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  right_inv := by
    rintro (x | ⟨⟨i, hi⟩, x⟩)
    · simp
    · simp [show ¬ i = j from hi]

theorem sigmaSplit_self (j : ι) (x : F j) : sigmaSplit F j ⟨j, x⟩ = Sum.inl x :=
  (Equiv.apply_eq_iff_eq_symm_apply _).2 rfl

theorem sigmaSplit_of_ne {i j : ι} (h : i ≠ j) (x : F i) :
    sigmaSplit F j ⟨i, x⟩ = Sum.inr ⟨⟨i, h⟩, x⟩ :=
  (Equiv.apply_eq_iff_eq_symm_apply _).2 rfl

end Split

end GlobalTheory.InnerAutomorphism
