module

public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise {n r t : ℕ} (hn : n = r + t) (a : Fin n) :
    Formalism.L2.DIV.blkOf r t a = Formalism.L2.Col.coarse r [t] a.val ∧
      Formalism.L2.DIV.blk2 r a = Formalism.L2.Col.coarse r [t] a.val := by
  have ha := a.isLt
  by_cases h : a.val < r
  · rw [Formalism.L2.Col.coarse_of_lt h]
    simp [Formalism.L2.DIV.blkOf, Formalism.L2.DIV.blk2, h]
  · have h' : r ≤ a.val := Nat.not_lt.mp h
    rw [Formalism.L2.Col.coarse_of_le h']
    have hlt : a.val - r < t := by omega
    have hd : (a.val - r) / t = 0 := Nat.div_eq_of_lt hlt
    simp [Formalism.L2.DIV.blkOf, Formalism.L2.DIV.blk2, h, hd, Formalism.L2.Col.blkIdx, hlt]

theorem blockTriangular_blockIndexOf_iff_colBlockUT_twoBlocks :
    ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ g : GL (Fin n) κ,
      (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) ∧
        (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) := by
  intro κ _ n r t hn g
  rw [Formalism.L2.DIV.mem_blockTri, Formalism.L2.DIV.mem_blockTri, Formalism.L2.Col.mem_btG]
  refine ⟨?_, ?_⟩
  · simp only [(blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise hn _).1]
  · simp only [(blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise hn _).2]

end GlobalTheory
