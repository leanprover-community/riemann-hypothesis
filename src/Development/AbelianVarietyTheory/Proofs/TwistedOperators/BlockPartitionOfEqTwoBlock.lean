module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
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
import Mathlib.Tactic.Linter.Style
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

open Matrix Formalism.L2.DIV

namespace GlobalTheory.ParIndex

variable {κ : Type} [CommRing κ] {n r : ℕ}

def parSub (hr : r ≤ n) (H : Subgroup (GL (Fin r) κ)) : Subgroup (GL (Fin n) κ) where
  carrier := {g | g ∈ blockTri (blk2 r) ∧ upperLeftBlock hr g ∈ H}
  one_mem' := ⟨Subgroup.one_mem _, by
    show ext1 (blockTri (blk2 r)) (blkR hr) 1 ∈ H
    rw [blockDiagonalExtendByOnePrimeField_one]; exact Subgroup.one_mem _⟩
  mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, by
    show ext1 (blockTri (blk2 r)) (blkR hr) (x * y) ∈ H
    rw [extendMatrixByIdentityAlongIndices_mul _ hx.1 hy.1]; exact Subgroup.mul_mem _ hx.2 hy.2⟩
  inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, by
    show ext1 (blockTri (blk2 r)) (blkR hr) x⁻¹ ∈ H
    rw [extendOne_inv _ hx.1]; exact Subgroup.inv_mem _ hx.2⟩

theorem mem_parSub {hr : r ≤ n} {H : Subgroup (GL (Fin r) κ)} {g : GL (Fin n) κ} :
    g ∈ parSub hr H ↔ g ∈ blockTri (blk2 r) ∧ upperLeftBlock hr g ∈ H := Iff.rfl

theorem blockPartitionOf_eq_twoBlock {t : ℕ} (hn : n = r + t) : (blkOf r t : Fin n → ℕ) = blk2 r := by
  funext a
  unfold blkOf blk2
  split_ifs with h
  · rfl
  · have : (a.val - r) / t = 0 := Nat.div_eq_of_lt (by have := a.2; omega)
    rw [this]

theorem blockTri_blkOf_eq {t : ℕ} (hn : n = r + t) :
    blockTri (κ := κ) (n := n) (blkOf r t) = blockTri (blk2 r) := by
  rw [blockPartitionOf_eq_twoBlock hn]

end GlobalTheory.ParIndex

end
