import Mathlib

namespace PI.SupportDatumW

open Matrix

def CokDet : Prop := ∀ (R : Type) [CommRing R] (n : ℕ) (Z Z' : Matrix (Fin n) (Fin n) R),
  Z.det ∈ nonZeroDivisors R → Z'.det ∈ nonZeroDivisors R →
  Nonempty (((Fin n → R) ⧸ LinearMap.range Z.mulVecLin) ≃ₗ[R]
    ((Fin n → R) ⧸ LinearMap.range Z'.mulVecLin)) →
  ∃ u : Rˣ, Z'.det = u * Z.det

section

variable {R : Type} [CommRing R]

theorem exists_lift {n : ℕ} (Z Z' : Matrix (Fin n) (Fin n) R)
    (φ : ((Fin n → R) ⧸ LinearMap.range Z.mulVecLin) →ₗ[R]
      ((Fin n → R) ⧸ LinearMap.range Z'.mulVecLin)) :
    ∃ A : Matrix (Fin n) (Fin n) R, ∀ x : Fin n → R,
      Submodule.Quotient.mk (p := LinearMap.range Z'.mulVecLin) (A *ᵥ x) =
        φ (Submodule.Quotient.mk x) := by
  obtain ⟨h, hh⟩ := Module.projective_lifting_property (LinearMap.range Z'.mulVecLin).mkQ
    (φ ∘ₗ (LinearMap.range Z.mulVecLin).mkQ) (Submodule.mkQ_surjective _)
  refine ⟨LinearMap.toMatrix' h, fun x => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  exact LinearMap.congr_fun hh x

theorem exists_mul_of_range_le {m : Type} [Fintype m] [DecidableEq m] (P Q : Matrix m m R)
    (h : LinearMap.range P.mulVecLin ≤ LinearMap.range Q.mulVecLin) :
    ∃ G : Matrix m m R, P = Q * G := by
  have hcol : ∀ j, ∃ g : m → R, Q *ᵥ g = P.col j := fun j => by
    obtain ⟨g, hg⟩ := h (LinearMap.mem_range_self P.mulVecLin (Pi.single j 1))
    exact ⟨g, by simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using hg⟩
  choose g hg using hcol
  refine ⟨Matrix.of fun k j => g j k, ?_⟩
  ext i j
  have hij := congr_fun (hg j) i
  simp only [Matrix.col_apply] at hij
  rw [Matrix.mul_apply, ← hij]
  simp [Matrix.mulVec, dotProduct]

end


end PI.SupportDatumW
