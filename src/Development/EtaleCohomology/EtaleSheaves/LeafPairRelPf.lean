import Development.EtaleCohomology.EtaleSheaves.LeafDescendFPPf

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.LeafTripleFPPf

theorem toR_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R') :
    toR R' ≫ incl h = toR R := by
  rw [← Spec.map_comp]
  rfl

theorem pb_lift {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R')
    {C D : Scheme.{0}} {c : C ⟶ Sp Ω} {f : D ⟶ Sp R} {v : C ⟶ D} (hs : IsPullback v c f (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w)) c
      (pullback.snd f (incl h)) (toR R') := by
  have e1 : pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) ≫ pullback.fst f (incl h) = v :=
    pullback.lift_fst _ _ _
  have t : IsPullback (pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) ≫
      pullback.fst f (incl h)) c f (toR R' ≫ incl h) := by rw [e1, toR_incl]; exact hs
  exact IsPullback.of_right t (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (incl h))

theorem fp_snd {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (hf : FP f) : FP (pullback.snd f g) := by
  obtain ⟨h1, h2, h3⟩ := hf
  exact ⟨inferInstance, inferInstance, inferInstance⟩

def LeafPairRel : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0), FP (γ1 ≫ c0) →
    ∀ {D0 : Scheme.{0}} (q : D0 ⟶ Sp R) (v0 : C0 ⟶ D0), FP q → ∀ (hs : IsPullback v0 c0 q (toR R)),
    ∃ (R' : Subalgebra k Ω) (h : R ≤ R'), R'.FG ∧ ∃ (E1 : Scheme.{0}) (e1 : E1 ⟶ pullback q (incl h)) (w1 : C1 ⟶ E1),
      FP (e1 ≫ pullback.snd q (incl h)) ∧ IsPullback w1 (γ1 ≫ c0) (e1 ≫ pullback.snd q (incl h)) (toR R') ∧
      γ1 ≫ pullback.lift v0 (c0 ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) = w1 ≫ e1

theorem tripleDescent_of_pairRelation (hR : LeafPairRel) : LeafTripleFP := by
  intro k _ Ω _ _ R hRfg C0 C1 C2 c0 γ1 γ2 h2 D0 D1 q d1 v0 v1 hq hq1 hs0 hs1 hc
  obtain ⟨R', h, hR', E2, e2, w2, hf2, hs2, hc2⟩ :=
    hR k Ω R hRfg (γ1 ≫ c0) γ2 h2 (d1 ≫ q) v1 hq1 hs1
  have hsnd : pullback.map (d1 ≫ q) (incl h) q (incl h) d1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]) (by rw [Category.id_comp, Category.comp_id]) ≫
      pullback.snd q (incl h) = pullback.snd (d1 ≫ q) (incl h) := by
    simp only [pullback.map, pullback.lift_snd, Category.comp_id]
  refine ⟨R', hR', _, _, _, pullback.snd q (incl h),
    pullback.map (d1 ≫ q) (incl h) q (incl h) d1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]) (by rw [Category.id_comp, Category.comp_id]), e2,
    pullback.lift v0 (c0 ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs0.w),
    pullback.lift v1 ((γ1 ≫ c0) ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs1.w), w2, ?_⟩
  refine ⟨fp_snd _ _ hq, ?_, ?_, pb_lift h hs0, ?_, ?_, ?_, hc2⟩
  · rw [hsnd]; exact fp_snd _ _ hq1
  · rw [hsnd]; exact hf2
  · rw [hsnd]; exact pb_lift h hs1
  · rw [hsnd]; exact hs2
  · apply pullback.hom_ext
    · simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hc]
    · simp only [pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]

end LateralTheory.E.LeafTripleFPPf

end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafTripleFPPf

namespace LateralTheory.E.LeafPairRelPf

theorem incl_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' R'' : Subalgebra k Ω} (h : R ≤ R')
    (h' : R' ≤ R'') : incl h' ≫ incl h = incl (h.trans h') := by
  rw [← Spec.map_comp]
  rfl

def LeafFactorStage : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C E Y : Scheme.{0}} (c : C ⟶ Sp Ω) (p : E ⟶ Sp R) (w : C ⟶ E), FP p → ∀ (hs : IsPullback w c p (toR R))
    (f : Y ⟶ Sp R), LocallyOfFinitePresentation f → ∀ (a : C ⟶ Y), a ≫ f = c ≫ toR R →
    ∃ (R' : Subalgebra k Ω) (h : R ≤ R'), R'.FG ∧ ∃ (g : pullback p (incl h) ⟶ Y),
      g ≫ f = pullback.snd p (incl h) ≫ incl h ∧
      pullback.lift w (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) ≫ g = a

theorem LeafPairRel_of (hO : LeafObjFP) (hF : LeafFactorStage) : LeafPairRel := by
  intro k _ Ω _ _ R hRfg C0 C1 c0 γ1 h1fp D0 q v0 hq hs
  obtain ⟨R1, hR1, E, p1, w, hp1, hsE⟩ := hO k Ω (γ1 ≫ c0) h1fp
  have h0 : R ≤ R ⊔ R1 := le_sup_left
  have h1 : R1 ≤ R ⊔ R1 := le_sup_right
  have hfg : (R ⊔ R1).FG := hRfg.sup hR1
  have hsE' := pb_lift h1 hsE
  have hlfp : LocallyOfFinitePresentation (pullback.snd q (incl h0)) := (fp_snd q (incl h0) hq).1
  obtain ⟨S, h, hS, g, hg1, hg2⟩ := hF k Ω (R ⊔ R1) hfg (γ1 ≫ c0) (pullback.snd p1 (incl h1)) _
    (fp_snd _ _ hp1) hsE' (pullback.snd q (incl h0)) hlfp
    (γ1 ≫ pullback.lift v0 (c0 ≫ toR (R ⊔ R1)) (by rw [Category.assoc, toR_incl]; exact hs.w))
    (by simp only [Category.assoc, pullback.lift_snd])
  refine ⟨S, h0.trans h, hS, pullback (pullback.snd p1 (incl h1)) (incl h),
    pullback.lift (g ≫ pullback.fst q (incl h0)) (pullback.snd _ _) ?_,
    pullback.lift (pullback.lift w ((γ1 ≫ c0) ≫ toR (R ⊔ R1)) (by rw [Category.assoc, toR_incl]; exact hsE.w))
      ((γ1 ≫ c0) ≫ toR S) (by simp only [Category.assoc, toR_incl, pullback.lift_snd]), ?_, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hg1, Category.assoc, incl_incl]
  · rw [pullback.lift_snd]; exact fp_snd _ _ (fp_snd _ _ hp1)
  · convert pb_lift h hsE' using 2; exact pullback.lift_snd _ _ _
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hg2,
        Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]

end LateralTheory.E.LeafPairRelPf

end
end
