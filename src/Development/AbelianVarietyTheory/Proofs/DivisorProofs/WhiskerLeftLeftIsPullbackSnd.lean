import Mathlib
import BuildAid.ForwardExisting

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem whiskerLeft_left_isPullback_snd (S : Scheme.{0}) (U T T' : Over S) (f : T' ⟶ T) :
    IsPullback (U ◁ f).left (snd U T').left (snd U T).left f.left := by
  have hw : (U ◁ f).left ≫ (snd U T).left = (snd U T').left ≫ f.left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  refine IsPullback.of_right (h₁₂ := (fst U T).left) (h₂₂ := T.hom) (v₁₃ := U.hom) ?_ hw ?_
  · have h1 : (U ◁ f).left ≫ (fst U T).left = (fst U T').left := by
      rw [← Over.comp_left, whiskerLeft_fst]
    have h2 : f.left ≫ T.hom = T'.hom := Over.w f
    rw [h1, h2, Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback U.hom T'.hom
  · rw [Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback U.hom T.hom

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_whiskerLeft_left_snd : ∀ (S : Scheme.{0}) (U T T' : Over S) (f : T' ⟶ T), IsPullback (U ◁ f).left (snd U T').left (snd U T).left f.left := by
  atlas_forward_decl GlobalTheory.whiskerLeft_left_isPullback_snd
