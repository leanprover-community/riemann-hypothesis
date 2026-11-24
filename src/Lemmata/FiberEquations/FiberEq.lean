module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section

open Finset NumberField Module
open scoped ComplexConjugate nonZeroDivisors

namespace Bl.FiberEquations

theorem goal1 (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ w : InfinitePlace E, 2 * (w.embedding x).re := by
  classical
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := x)
  rw [eq_ratCast] at h
  have h' : ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ φ : E →+* ℂ, φ x :=
    h.trans (Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ fun _ => rfl)
  rw [← Complex.ratCast_re, h', Complex.re_sum,
    ← sum_fiberwise univ InfinitePlace.mk (fun φ : E →+* ℂ => (φ x).re)]
  refine sum_congr rfl fun w _ => ?_
  calc
    _ = ∑ φ with InfinitePlace.mk φ = w, (w.embedding x).re := by
      refine sum_congr rfl fun φ hφ => ?_
      rw [← (mem_filter.mp hφ).2]
      rcases InfinitePlace.embedding_mk_eq φ with h | h
      · rw [h]
      · rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
    _ = _ := by
      rw [sum_const, InfinitePlace.card_filter_mk_eq, IsTotallyComplex.mult_eq, two_nsmul, two_mul]

end Bl.FiberEquations
