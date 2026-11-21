import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteAndNcardBound
import BuildAid.ForwardExisting

section
open NumberField NumberField.mixedEmbedding Module

namespace GlobalTheory.CompanionTheory.IntCount

theorem finite_and_ncard_le :
    ∀ (E : Type) [Field E] [NumberField E], ∃ (C : ℝ) (N : ℕ), ∀ R : ℝ, 1 ≤ R →
      {r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.Finite ∧
      ({r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.ncard : ℝ) ≤ C * R ^ N :=
  _root_.UpperTheory.Reformulated.B.FiniteAndNcardBound.finite_and_ncard_le

end GlobalTheory.CompanionTheory.IntCount
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integers_bounded_archimedean_count : ∀ (E : Type) [Field E] [NumberField E], ∃ (C : ℝ) (N : ℕ), ∀ R : ℝ, 1 ≤ R →
    {r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.Finite ∧
    ({r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.ncard : ℝ) ≤ C * R ^ N := by
  atlas_forward_decl GlobalTheory.CompanionTheory.IntCount.finite_and_ncard_le
