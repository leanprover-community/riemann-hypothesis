import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict

section
namespace GlobalTheory.CharInvAtZero

theorem eq_of_eq_zero : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (ℓ : SchwartzMap Y ℂ →L[ℂ] ℂ),
    (∀ L : Y →ₗ[ℝ] ℝ, ∀ f g : SchwartzMap Y ℂ, ⇑g = (fun x => GlobalTheory.ArchSch.ech (L x) * f x) → ℓ g = ℓ f) →
    ∀ f g : SchwartzMap Y ℂ, f 0 = g 0 → ℓ f = ℓ g := by
  intro Y _ _ _ ℓ hinv f g h0
  refine GlobalTheory.SchwartzHadamard.eq_of_eqOn (⊥ : Submodule ℝ Y) ℓ (fun L _ => hinv L) f g ?_
  intro p hp
  rw [Submodule.mem_bot] at hp
  subst hp
  exact h0

end GlobalTheory.CharInvAtZero
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_functional_depends_on_value_at_zero : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (ℓ : SchwartzMap Y ℂ →L[ℂ] ℂ),
    (∀ L : Y →ₗ[ℝ] ℝ, ∀ f g : SchwartzMap Y ℂ, ⇑g = (fun x => GlobalTheory.ArchSch.ech (L x) * f x) → ℓ g = ℓ f) →
    ∀ f g : SchwartzMap Y ℂ, f 0 = g 0 → ℓ f = ℓ g := by
  atlas_forward_decl GlobalTheory.CharInvAtZero.eq_of_eq_zero
