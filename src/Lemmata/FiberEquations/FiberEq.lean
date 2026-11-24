module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section

open Finset NumberField Module
open scoped ComplexConjugate

namespace Bl.FiberEquations

theorem goal1 (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ w : InfinitePlace E, 2 * (w.embedding x).re := by
  classical
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := x)
  rw [eq_ratCast] at h
  rw [← Complex.ratCast_re, h, Complex.re_sum]
  refine ((RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm.sum_comp
    (fun φ => (φ x).re)).trans ?_
  rw [← sum_fiberwise univ InfinitePlace.mk (fun φ : E →+* ℂ => (φ x).re)]
  refine sum_congr rfl fun w _ => (sum_eq_card_nsmul (b := (w.embedding x).re) fun φ hφ => ?_).trans ?_
  · rcases InfinitePlace.mk_eq_iff.mp ((InfinitePlace.mk_embedding w).trans (mem_filter.mp hφ).2.symm) with rfl | rfl
    · rfl
    · exact Complex.conj_re _
  · rw [InfinitePlace.card_filter_mk_eq, IsTotallyComplex.mult_eq, two_nsmul, two_mul]

end Bl.FiberEquations
