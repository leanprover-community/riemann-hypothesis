import Formalism.SharpRestriction.GlobalSchurBounds.Joints

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions



def Gram0Def (D : D7) : Prop :=
  letI := D.host.cmStar
  UnusedSlot33.IsDef D.sp.cm.sig D.sp.gram0









theorem _root_.Formalism.MainNotions.StandardLattice.column_lemma_family_of_definite {eps : ℝ} (Fm : FamP eps) (C₄ C₅ : ℝ) (h : UnusedSlot33.ConclusionOnFamily Fm C₄ C₅)
    (hD : ∀ x (i : Fm.Ix x), Gram0Def (Fm.D x i)) : StandardLattice.FamilyLevelConditionAdmitted Fm := by
  intro x hx i
  exact StandardLattice.column_lemma_of_definite_form _ _ (h x hx i).2.2.2.2.2.2.2.1 (hD x i)


theorem _root_.Formalism.MainNotions.flipTwoThree.theta_norm_family_of_linked {eps : ℝ} (Fm : FamP eps) (C : ℝ) (h : TaylorLogMetric.ConclusionOnFamily Fm C)
    (hl : ∀ x (i : Fm.Ix x), ∃ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (Fm.D x i) (Fm.D x i).host.ccK δ ∧
      OmLink (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK δ)) : flipTwoThree.admF1 Fm := by
  intro Cn
  refine ⟨Cn + 4, 0, ?_⟩
  intro x _ _ i
  obtain ⟨δ, hδ, hl'⟩ := hl x i
  have hcc : TaylorLogMetric.IsCurveIdeal (Fm.D x i) (Fm.D x i).host.ccK := by
    refine ⟨(Fm.D x i).host.ccK_ne_bot, Nat.Coprime.mul_right ?_ ?_⟩
    · exact (Fm.D x i).host.ccK_coprime 2 (by simp)
    · exact (Fm.D x i).host.ccK_coprime _ (by simp)
  exact flipTwoThree.first_hypothesis_of_lifting _ Cn x _ ((h x i) _ hcc δ hδ).1 hl'

theorem _root_.Formalism.MainNotions.flipTwoThree.theta_condition_family_of_linked {eps : ℝ} (Fm : FamP eps) (C : ℝ)
    (hfree : ∀ x (i : Fm.Ix x), ThFree (Fm.D x i))
    (hT : ∀ x (i : Fm.Ix x), ExistsTwelfthRootCharacterThetaFamily (Fm.D x i) C) : flipTwoThree.admF2 Fm := by
  intro Cn
  refine ⟨C * (1 + Cn), 0, ?_⟩
  intro x _ _ i
  obtain ⟨δ, -, χ, -, e, hcl, hl⟩ := hT x i
  obtain ⟨-, hth, -⟩ := hcl
  exact flipTwoThree.second_hypothesis_of_lifting _ Cn C x _ e hth (hfree x i) hl

theorem _root_.Formalism.MainNotions.flipTwoThree.stabiliser_family_of_definite {eps : ℝ} (Fm : FamP eps) (C₄ C₅ : ℝ) (h : UnusedSlot33.ConclusionOnFamily Fm C₄ C₅)
    (hD : ∀ x (i : Fm.Ix x), Gram0Def (Fm.D x i))
    (hP : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev)
    (hg : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, StandardLattice.GBig (Fm.D x i)) :
    flipTwoThree.admF3 Fm := by
  obtain ⟨x0, hg⟩ := hg
  exact ⟨x0, fun x hx hx1 i => flipTwoThree.stabiliser_condition_of_level _ (Fm.ex x hx1 i).lev
    (h x hx1 i).2.2.2.2.2.2.2.1 (hD x i) (hP x hx1 i) (hg x hx hx1 i)⟩

def SettingEventually {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word),
    product_first_zeroth_parts.HidaSetting (Fm.D x i) u

theorem _root_.Formalism.MainNotions.flipTwoThree.injectivity_family_of_theorem {eps : ℝ} (Fm : FamP eps) (C : ℝ) (h : product_first_zeroth_parts.ConclusionOnFamily Fm C)
    (hS : SettingEventually Fm) : flipTwoThree.admF4 Fm := by
  obtain ⟨xa, ha⟩ := h
  obtain ⟨xb, hb⟩ := hS
  refine ⟨max xa xb, ?_⟩
  intro x hx hx1 i
  exact flipTwoThree.fourth_hypothesis_of_lifting _ (fun u => (ha x (le_trans (le_max_left _ _) hx) i u
    (hb x (le_trans (le_max_right _ _) hx) hx1 i u)).2.2.2.2.2.1)

theorem _root_.Formalism.MainNotions.flipTwoThree.norm_bound_family_of_theorem {eps : ℝ} (Fm : FamP eps) (C : ℝ) (h : product_first_zeroth_parts.ConclusionOnFamily Fm C)
    (hS : SettingEventually Fm) : flipTwoThree.admF6 Fm := by
  obtain ⟨xa, ha⟩ := h
  obtain ⟨xb, hb⟩ := hS
  refine ⟨max xa xb, ?_⟩
  intro x hx hx1 i
  exact flipTwoThree.restriction_dimension_of_division _ (fun u => (ha x (le_trans (le_max_left _ _) hx) i u
    (hb x (le_trans (le_max_right _ _) hx) hx1 i u)).2.2.2.2.2.1)

theorem _root_.Formalism.MainNotions.TaylorLogMetric.AdmF_of {eps : ℝ} (Fm : FamP eps)
    (h : ∀ x (i : Fm.Ix x), UnusedSlot33.Conclusion1 (Fm.D x i)) : TaylorLogMetric.AdmF Fm := by
  intro x i
  exact TaylorLogMetric.first_hypothesis_of_lifting _ (h x i)


end Formalism.MainNotions.GlobalTheoryTheory

end
