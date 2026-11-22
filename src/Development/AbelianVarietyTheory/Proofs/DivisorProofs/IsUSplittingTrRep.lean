module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Matrix

namespace GlobalTheory.WeilTr

open GlobalTheory.WeilM

variable {R : Type} [CommRing R] {κ : Type} [Fintype κ]

variable [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R}

section Dbl

variable {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β]

end Dbl

theorem symp_transpose {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [Fintype β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix β α E) :
    symp c ξ JB JA x y = symp c ξ JA JB xᵀ yᵀ := by
  unfold symp hTens
  congr 2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.transpose_apply]
  ring

end GlobalTheory.WeilTr

end
