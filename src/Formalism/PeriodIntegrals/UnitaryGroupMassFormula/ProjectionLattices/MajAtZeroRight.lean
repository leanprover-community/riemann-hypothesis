import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice

noncomputable section

namespace PI.Dv.GLP

open Formalism.HermitianLatticesTheory NumberField

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)

theorem fcoord_smul' (c : K) (x : V) : fcoord b X v (c • x) = v.embedding c • fcoord b X v x := by
  unfold fcoord vecAt
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

private theorem fcoord_add_projection_lattices (x y : V) : fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  unfold fcoord vecAt
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp


theorem majAt_add_right' (x y y' : V) : majAt b X v x (y + y') = majAt b X v x y + majAt b X v x y' := by
  unfold majAt
  rw [fcoord_add_projection_lattices]
  simp [mul_add, Finset.sum_add_distrib]

theorem majAt_smul_left' (c : K) (x y : V) :
    majAt b X v (c • x) y = star (v.embedding c) * majAt b X v x y := by
  unfold majAt
  rw [fcoord_smul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring







theorem exists_nonreal [NumberField.IsTotallyComplex K] : ∃ c : K, (v.embedding c).im ≠ 0 := by
  by_contra h
  push_neg at h
  refine (InfinitePlace.not_isReal_iff_isComplex.mpr (NumberField.IsTotallyComplex.isComplex v)) ?_
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  ext c
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.mpr (h c)



end PI.Dv.GLP
