import Formalism.SubspaceCounting.TopsChoiceSecondBound

noncomputable section

namespace Formalism.G0

namespace ChoiceOfTopsP

lemma not_good {n : ℕ} {T : Finset ℕ} {L₂ K r N₁ G : ℕ} (h : ¬ GoodOrbit n T L₂ K r N₁ G) :
    ¬ CondA n T L₂ K ∨ (¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) ∨ ¬ CondC n T G ∨ T.card < N₁ := by
  unfold GoodOrbit at h
  by_cases hN : N₁ ≤ T.card
  · tauto
  · right; right; right; omega

lemma term_le (p a b c d : Prop) {_ : Decidable p} {_ : Decidable a} {_ : Decidable b}
    {_ : Decidable c} {_ : Decidable d} (w : ℝ) (hw : 0 ≤ w) (h : p → a ∨ b ∨ c ∨ d) :
    (if p then w else 0) ≤
      (if a then w else 0) + (if b then w else 0) + (if c then w else 0) + (if d then w else 0) := by
  by_cases hp : p
  · rcases h hp with h' | h' | h' | h' <;>
      split_ifs <;> linarith
  · split_ifs <;> linarith


end ChoiceOfTopsP


end Formalism.G0
