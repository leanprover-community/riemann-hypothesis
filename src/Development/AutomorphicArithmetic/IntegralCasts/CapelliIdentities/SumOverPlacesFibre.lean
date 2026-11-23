module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open scoped Classical

theorem UpperTheory.Reformulated.B.SumOverPlacesFibre.sum_fibre_place :
    ∀ (F : Type) [inst : Field F]
    [inst_1 : NumberField F] [NumberField.IsTotallyComplex F] (x : F) (v : NumberField.InfinitePlace F),
    ∑ φ : F →+* ℂ with NumberField.InfinitePlace.mk φ = v, (φ : F → ℂ) x =
      (↑((2 : ℝ) * ((v.embedding : F → ℂ) x).re) : ℂ) := by
  intro F _ _ _ x v
  have hc : v.IsComplex := NumberField.IsTotallyComplex.isComplex v
  have hne : v.embedding ≠ NumberField.ComplexEmbedding.conjugate v.embedding := by
    intro h
    exact (NumberField.InfinitePlace.isComplex_iff.mp hc)
      (NumberField.ComplexEmbedding.isReal_iff.mpr h.symm)
  have hset : (Finset.univ.filter fun φ : F →+* ℂ => NumberField.InfinitePlace.mk φ = v) =
      {v.embedding, NumberField.ComplexEmbedding.conjugate v.embedding} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      have h' : NumberField.InfinitePlace.mk v.embedding = NumberField.InfinitePlace.mk φ := by
        rw [NumberField.InfinitePlace.mk_embedding, h]
      rcases NumberField.InfinitePlace.mk_eq_iff.mp h' with h1 | h1
      · exact Or.inl h1.symm
      · exact Or.inr h1.symm
    · rintro (h | h)
      · rw [h, NumberField.InfinitePlace.mk_embedding]
      · rw [h, NumberField.InfinitePlace.mk_conjugate_eq, NumberField.InfinitePlace.mk_embedding]
  rw [hset, Finset.sum_pair hne, NumberField.ComplexEmbedding.conjugate_coe_eq,
    Complex.add_conj]
