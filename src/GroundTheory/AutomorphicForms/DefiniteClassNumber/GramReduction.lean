import Mathlib
import GroundTheory.AutomorphicForms.DefiniteClassNumber.Reduction

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix Submodule
open scoped RealInnerProductSpace

variable {J : Type*} [Fintype J]

def GramSpace (_G : Matrix J J ℝ) : Type _ := J → ℝ

instance (G : Matrix J J ℝ) : AddCommGroup (GramSpace G) := inferInstanceAs (AddCommGroup (J → ℝ))

instance (G : Matrix J J ℝ) : Module ℝ (GramSpace G) := inferInstanceAs (Module ℝ (J → ℝ))

instance (G : Matrix J J ℝ) : FiniteDimensional ℝ (GramSpace G) :=
  inferInstanceAs (FiniteDimensional ℝ (J → ℝ))

def toGram (G : Matrix J J ℝ) : (J → ℝ) ≃ₗ[ℝ] GramSpace G := LinearEquiv.refl ℝ (J → ℝ)

@[instance_reducible]
def gramCore (G : Matrix J J ℝ) (hs : Gᵀ = G) (hpos : ∀ x : J → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x)) :
    InnerProductSpace.Core ℝ (GramSpace G) where
  inner x y := (toGram G).symm x ⬝ᵥ (G *ᵥ (toGram G).symm y)
  conj_inner_symm x y := by
    show (toGram G).symm y ⬝ᵥ (G *ᵥ (toGram G).symm x) = (toGram G).symm x ⬝ᵥ (G *ᵥ (toGram G).symm y)
    rw [dotProduct_mulVec, ← mulVec_transpose, hs, dotProduct_comm]
  re_inner_nonneg x := by
    show 0 ≤ (toGram G).symm x ⬝ᵥ (G *ᵥ (toGram G).symm x)
    by_cases hx : (toGram G).symm x = 0
    · rw [hx]; simp
    · exact (hpos _ hx).le
  add_left x y z := by
    show (toGram G).symm (x + y) ⬝ᵥ _ = (toGram G).symm x ⬝ᵥ _ + (toGram G).symm y ⬝ᵥ _
    rw [map_add, add_dotProduct]
  smul_left x y r := by
    show (toGram G).symm (r • x) ⬝ᵥ _ = r * ((toGram G).symm x ⬝ᵥ _)
    rw [map_smul, smul_dotProduct, smul_eq_mul]
  definite x hx := by
    by_contra h
    have h' : (toGram G).symm x ≠ 0 := by simpa using h
    have := hpos _ h'
    exact (ne_of_gt this) hx



end GroundTheory.Automorphic
