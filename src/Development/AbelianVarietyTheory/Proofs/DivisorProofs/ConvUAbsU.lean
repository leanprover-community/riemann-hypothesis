module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich
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
import Mathlib.Tactic.Basify
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

noncomputable section

open MeasureTheory

namespace GlobalTheory

namespace WeylCell

def partnerU {n : ℕ} (k : Fin (n / 2)) : Fin n :=
  if h : k.val + 1 < n / 2 then lo (⟨k.val + 1, h⟩ : Fin (n / 2)) else (lo k).rev

def simpleU {n : ℕ} (k : Fin (n / 2)) : Equiv.Perm (Fin n) :=
  if k.val + 1 < n / 2 then Equiv.swap (lo k) (partnerU k) * Equiv.swap (lo k).rev (partnerU k).rev
  else Equiv.swap (lo k) (lo k).rev

def actU {n : ℕ} (k : Fin (n / 2)) (α : Fin (n / 2) → ℂˣ) : Fin (n / 2) → ℂˣ :=
  if h : k.val + 1 < n / 2 then α ∘ Equiv.swap k ⟨k.val + 1, h⟩ else Function.update α k (α k)⁻¹

def cSimpleU (q : ℕ) {n : ℕ} (k : Fin (n / 2)) (α : Fin (n / 2) → ℂˣ) : ℂ :=
  if h : k.val + 1 < n / 2 then cSL ((q : ℂ) ^ 2) ((α k : ℂ) / α ⟨k.val + 1, h⟩)
  else if Even n then cSL q (α k) else cSU q (α k)

theorem IsWeylRep.inv {R : Type} [CommRing R] {n : ℕ} {v : Equiv.Perm (Fin n)} {y : GL (Fin n) R}
    (hy : IsWeylRep v y) : IsWeylRep v⁻¹ y⁻¹ := by
  have key : ∀ i j, ((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i (v j) *
      (y : Matrix (Fin n) (Fin n) R) (v j) j = if i = j then 1 else 0 := by
    intro i j
    have h := congrFun (congrFun (Units.inv_mul y) i) j
    rw [Matrix.mul_apply, Finset.sum_eq_single (v j)] at h
    · rw [h, Matrix.one_apply]
    · intro b _ hb; rw [hy b j hb, mul_zero]
    · simp
  have hv : ∀ j, v (v⁻¹ j) = j := fun j => by simp
  intro i j hij
  have hu : IsUnit ((y : Matrix (Fin n) (Fin n) R) j (v⁻¹ j)) := by
    have h := key (v⁻¹ j) (v⁻¹ j)
    rw [hv, if_pos rfl] at h
    exact IsUnit.of_mul_eq_one_right _ h
  have h := key i (v⁻¹ j)
  rw [hv, if_neg hij] at h
  exact hu.mul_left_eq_zero.1 h

end WeylCell

end GlobalTheory

end
