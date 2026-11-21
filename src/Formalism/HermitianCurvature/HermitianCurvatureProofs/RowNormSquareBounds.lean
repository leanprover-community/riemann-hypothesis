import Formalism.HermitianCurvature.LevelRecursionCondNeeded

namespace Formalism.FourierDecayAlt.P.SchurNormSquareBounds

open Finset


lemma row_le {G ι : Type} [AddCommGroup G] [DecidableEq ι] (La : AddSubgroup G) (T : Finset ι)
    (τ : ι → G) (ψ : G → ℝ) (ε : ℝ) (hinj : Set.InjOn τ T)
    (hco : ∀ t ∈ T, ∀ t' ∈ T, τ t - τ t' ∈ La)
    (hS : ∀ S : Finset G, (∀ l ∈ S, l ∈ La ∧ l ≠ 0) → ∑ l ∈ S, ψ l ≤ ε) (t : ι) (ht : t ∈ T) :
    ∑ t' ∈ T.erase t, ψ (τ t - τ t') ≤ ε ∧ ∑ t' ∈ T.erase t, ψ (τ t' - τ t) ≤ ε := by
  classical
  constructor
  · have := hS ((T.erase t).image fun t' => τ t - τ t') (by
      intro l hl
      obtain ⟨t', ht', rfl⟩ := mem_image.1 hl
      obtain ⟨hne, ht'T⟩ := mem_erase.1 ht'
      exact ⟨hco t ht t' ht'T, fun h => hne (hinj ht'T ht (sub_eq_zero.1 h).symm)⟩)
    rwa [sum_image] at this
    intro x hx y hy hxy
    exact hinj (mem_erase.1 hx).2 (mem_erase.1 hy).2 (sub_right_injective hxy)
  · have := hS ((T.erase t).image fun t' => τ t' - τ t) (by
      intro l hl
      obtain ⟨t', ht', rfl⟩ := mem_image.1 hl
      obtain ⟨hne, ht'T⟩ := mem_erase.1 ht'
      exact ⟨hco t' ht'T t ht, fun h => hne (hinj ht'T ht (sub_eq_zero.1 h))⟩)
    rwa [sum_image] at this
    intro x hx y hy hxy
    exact hinj (mem_erase.1 hx).2 (mem_erase.1 hy).2 (sub_left_injective hxy)

end Formalism.FourierDecayAlt.P.SchurNormSquareBounds

namespace Formalism.FourierDecayAlt.P

open Finset SchurNormSquareBounds




end Formalism.FourierDecayAlt.P
