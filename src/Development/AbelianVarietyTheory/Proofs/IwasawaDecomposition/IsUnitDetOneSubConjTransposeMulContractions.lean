module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem isUnit_det_one_sub_conjTranspose_mul_of_contractions (P Q : ℕ)
    (A B : Matrix (Fin P) (Fin Q) ℂ) (hA : (1 - Aᴴ * A).PosDef) (hB : (1 - Bᴴ * B).PosDef) :
    IsUnit (1 - Aᴴ * B).det := by
  rw [isUnit_iff_ne_zero]
  intro h
  obtain ⟨u, hu, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hsum : ((1 - Aᴴ * A) + (1 - Bᴴ * B) + (A - B)ᴴ * (A - B)).PosDef :=
    (hA.add hB).add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _)
  have heq : (1 - Aᴴ * A) + (1 - Bᴴ * B) + (A - B)ᴴ * (A - B)
      = (1 - Aᴴ * B) + (1 - Aᴴ * B)ᴴ := by
    simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
      conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [heq] at hsum
  have hpos := hsum.dotProduct_mulVec_pos hu
  have h2 : star u ⬝ᵥ ((1 - Aᴴ * B)ᴴ *ᵥ u) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, h0]
    simp
  rw [Matrix.add_mulVec, dotProduct_add, h0, h2] at hpos
  simp at hpos

end GlobalTheory
