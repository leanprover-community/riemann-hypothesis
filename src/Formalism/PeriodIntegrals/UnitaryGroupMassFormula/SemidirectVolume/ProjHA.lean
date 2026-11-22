module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.HermitianIsotropicProjComplement
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.SemiDefs

@[expose] public section

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

def datR : PG.Dat (R ⊗[F] E) (Fin M) r where
  σA := sigR R σ
  JA := JR R J
  e a := ratV (F := F) R (P.e a)
  f a := ratV (F := F) R (P.f a)
  z := ratV (F := F) R P.z
  tz := inclR (F := F) R ((algebraMap F E (-T))⁻¹)

theorem sigR_inclR (x : E) : sigR R σ (inclR (F := F) R x) = inclR (F := F) R (σ x) := by
  show Algebra.TensorProduct.map (AlgHom.id F R) σ (Algebra.TensorProduct.includeRight x) =
    Algebra.TensorProduct.includeRight (σ x)
  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem hR_ratV (x y : Fin M → E) :
    hR R σ J (ratV (F := F) R x) (ratV (F := F) R y) = inclR (F := F) R (hE σ J x y) := by
  unfold hR hE Formalism.UG.hform JR ratV
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, map_mul, sigR_inclR, Matrix.map_apply]
  rfl

variable {R σ J P T}

theorem datR_hyp (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) :
    (datR R σ J P T).Hyp := by
  have hT : algebraMap F E (-T) ≠ 0 := by
    rw [map_neg]
    exact neg_ne_zero.mpr ((map_ne_zero _).mpr hP.2.2.2.2.2.2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show sigR R σ (sigR R σ x) = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      show Algebra.TensorProduct.map (AlgHom.id F R) σ
          (Algebra.TensorProduct.map (AlgHom.id F R) σ (a ⊗ₜ b)) = a ⊗ₜ b
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        AlgHom.id_apply, hσσ]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  · intro i j
    show sigR R σ (inclR R (J j i)) = inclR R (J i j)
    rw [sigR_inclR, hJ.1]
  · intro a b
    show hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R (P.e b)) = 0
    rw [hR_ratV, hP.1 a b, map_zero]
  · intro a b
    show hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R (P.f b)) = 0
    rw [hR_ratV, hP.2.1 a b, map_zero]
  · intro a b
    show hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R (P.f b)) = if a = b then 1 else 0
    rw [hR_ratV, hP.2.2.1 a b]
    split_ifs <;> simp
  · intro a
    show hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R P.z) = 0
    rw [hR_ratV, hP.2.2.2.1 a, map_zero]
  · intro a
    show hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R P.z) = 0
    rw [hR_ratV, hP.2.2.2.2.1 a, map_zero]
  · show inclR (F := F) R ((algebraMap F E (-T))⁻¹) * hR R σ J (ratV (F := F) R P.z) (ratV (F := F) R P.z) = 1
    rw [hR_ratV, hP.2.2.2.2.2.1, ← map_mul, inv_mul_cancel₀ hT, map_one]

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

end R

end PI.VolSemiDirect.W
