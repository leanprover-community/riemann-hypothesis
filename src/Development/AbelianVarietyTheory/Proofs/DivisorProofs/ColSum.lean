module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Span.Defs
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
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

namespace GlobalTheory.ColumnSumLemma
open Matrix
theorem colSum {A : Type} [CommRing A] {n r : ℕ} (C : Matrix (Fin n) (Fin r) A) (a : Fin r → A) :
    Matrix.mulVec C a = ∑ i, a i • Matrix.transpose C i := by
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem main : ∀ {A : Type} [inst : CommRing A] {n r : ℕ} (C : Matrix (Fin n) (Fin r) A) (I : Set (Fin r)) (y : Fin n → A), y ∈ Submodule.span A ((fun (i : Fin r) ↦ Matrix.transpose C i) '' I) ↔ ∃ (a : Fin r → A), (∀ l ∉ I, a l = (0 : A)) ∧ Matrix.mulVec C a = y := by
  intro A _ n r C I y
  rw [Finsupp.mem_span_image_iff_linearCombination]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l, fun k hk => ?_, ?_⟩
    · exact Finsupp.notMem_support_iff.mp (fun h => hk (hl h))
    · rw [colSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      intro i; simp
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Finsupp.equivFunOnFinite.symm a, fun k hk => ?_, ?_⟩
    · by_contra h
      exact (Finsupp.mem_support_iff.mp hk) (ha k h)
    · rw [colSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      · rfl
      · intro i; simp
end GlobalTheory.ColumnSumLemma
