import Formalism.FockGram.StatementTensor

open Matrix LinearMap Module TensorProduct

noncomputable section
namespace Formalism.E


example {R M₁ M₂ : Type} [CommRing R] [StarRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (B₁ : M₁ →ₗ⋆[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ⋆[R] M₂ →ₗ[R] R)
    (a : R) (z w : M₁ ⊗[R] M₂) :
    htmul B₁ B₂ (a • z) w = star a * htmul B₁ B₂ z w ∧ htmul B₁ B₂ z (a • w) = a * htmul B₁ B₂ z w := by
  simp [starRingEnd_apply]



example {R M : Type} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
    (B : M →ₗ⋆[R] M →ₗ[R] R) : B.IsSymm ↔ ∀ x y, star (B x y) = B y x := by
  simp [LinearMap.isSymm_def, starRingEnd_apply]

example (n : ℤ) : star n = n := rfl

end Formalism.E
