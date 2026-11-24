module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section

open Finset NumberField Module
open scoped ComplexConjugate nonZeroDivisors

namespace Bl.FiberEquations

theorem goal1 (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : E) :
  classical
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := x)
  rw [eq_ratCast] at h
  rw [← Complex.ratCast_re, h, Complex.re_sum,
    Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm
      (fun σ => (σ x).re) (fun φ => (φ x).re) (fun _ => rfl),
    ← sum_fiberwise univ InfinitePlace.mk (fun φ : E →+* ℂ => (φ x).re)]
  refine sum_congr rfl fun w _ => ?_
  refine (sum_eq_card_nsmul (b := (w.embedding x).re) ?_).trans ?_
  · intro φ hφ
    rw [← (mem_filter.mp hφ).2]
    rcases InfinitePlace.embedding_mk_eq φ with h | h <;>
      rw [h] ; rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  · rw [InfinitePlace.card_filter_mk_eq, IsTotallyComplex.mult_eq, two_nsmul, two_mul]

end Bl.FiberEquations
