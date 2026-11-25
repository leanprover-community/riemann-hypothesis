module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace MassDataIdxAdA

open Matrix

variable {K : Type*} [Field K] (O : ValuationSubring K) {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_gl_of_left_inv (g : O) (hg : ¬ IsUnit g) (C R N : Matrix ι ι K)
    (hC : ∀ i j, C i j ∈ O) (hR : ∀ i j, R i j ∈ O) (hN : ∀ i j, N i j ∈ O)
    (hRC : R * C = 1 + (g : K) • N) :
    ∃ c : GL ι O, (c : Matrix ι ι O).map (fun x : O => (x : K)) = C := by
  classical
  set C' : Matrix ι ι O := Matrix.of fun i j => (⟨C i j, hC i j⟩ : O) with hC'
  set R' : Matrix ι ι O := Matrix.of fun i j => (⟨R i j, hR i j⟩ : O) with hR'
  set N' : Matrix ι ι O := Matrix.of fun i j => (⟨N i j, hN i j⟩ : O) with hN'
  have key : R' * C' = 1 + g • N' := by
    apply Matrix.map_injective (f := algebraMap O K) Subtype.val_injective
    change (algebraMap O K).mapMatrix (R' * C') = (algebraMap O K).mapMatrix (1 + g • N')
    rw [map_mul, map_add, map_one]
    exact hRC
  have hres : IsLocalRing.residue O g = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hg
  have hone : IsUnit (1 + g • N').det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have : (IsLocalRing.residue O).mapMatrix (1 + g • N') = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [hres]
      · simp [hij, hres]
    rw [this, Matrix.det_one]
    exact one_ne_zero
  have hdet : IsUnit C'.det := by
    rw [← key, Matrix.det_mul] at hone
    exact (IsUnit.mul_iff.mp hone).2
  refine ⟨Matrix.nonsingInvUnit C' hdet, ?_⟩
  ext i j
  rfl

end MassDataIdxAdA
