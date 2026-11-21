import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareActionSectionsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullByCompAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraFiniteProjectiveRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraBaseChangeIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorsResidueBasis

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RigPull

theorem hasGen_pull_of_comm {X₀ X Y Y₀ : Scheme.{0}} {L : LB X₀} (hL : L.IsLB) (F : X ⟶ X₀) {a : Y₀ ⟶ X₀}
    {a' : Y ⟶ X} {ψ : Y ⟶ Y₀} (e : a' ≫ F = ψ ≫ a) (h : HasGen (L.pull a)) : HasGen ((L.pull F).pull a') := by
  refine (CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hL F) a')).1 ?_
  have h0 : CechPic.cls _ (pull_isLB hL a) = 0 := (CechPic.cls_eq_zero_iff (pull_isLB hL a)).2 h
  rw [CechPic.cls_pull (pull_isLB hL F) a', CechPic.cls_pull hL F, ← CechPic.pull_comp, e, CechPic.pull_comp,
    ← CechPic.cls_pull hL a (pull_isLB hL a), h0, map_zero]

end GlobalTheory.RigPull

namespace GlobalTheory

open RigPull SiegelDescent

theorem hasGen_pull_rig_of_isGrpPullback : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ c : 𝔠.elt, HasGen (((X.P c).pull φ₂).pull (lift (1 : A' ⟶ A') (𝟙 A')).left) ∧
      HasGen (((X.P c).pull φ₂).pull (lift (𝟙 A') (1 : A' ⟶ A')).left) := by
  intro F _ _ 𝔠 S S' X b A' _ _ φ hp φ₂ sq c
  have hφ : φ ≫ X.A.hom = A'.hom ≫ b := hp.1.w
  have one := one_comp hp A' X.A φ hφ
  have idφ : (𝟙 A' : A' ⟶ A').left ≫ φ = φ ≫ (𝟙 X.A : X.A ⟶ X.A).left := by simp
  exact ⟨hasGen_pull_of_comm (X.isLB c) φ₂ (lift_square sq one idφ) (X.rig₁ c),
    hasGen_pull_of_comm (X.isLB c) φ₂ (lift_square sq idφ one) (X.rig₂ c)⟩

end GlobalTheory
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_square_diagonal_sections_generated : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ c : 𝔠.elt, HasGen (((X.P c).pull φ₂).pull (lift (1 : A' ⟶ A') (𝟙 A')).left) ∧
      HasGen (((X.P c).pull φ₂).pull (lift (𝟙 A') (1 : A' ⟶ A')).left) := by
  atlas_forward_decl GlobalTheory.hasGen_pull_rig_of_isGrpPullback
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.PullPol

theorem swap_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (hs : IsSquare φ φ₂) :
    (lift (snd G' G') (fst G' G')).left ≫ φ₂ = φ₂ ≫ (lift (snd G G) (fst G G)).left := by
  apply pullback.hom_ext
  · change _ ≫ φ₂ ≫ (fst G G).left = φ₂ ≫ (lift (snd G G) (fst G G)).left ≫ (fst G G).left
    rw [hs.1, ← Over.comp_left, lift_fst, hs.2, ← Category.assoc, ← Over.comp_left, lift_fst]
  · change _ ≫ φ₂ ≫ (snd G G).left = φ₂ ≫ (lift (snd G G) (fst G G)).left ≫ (snd G G).left
    rw [hs.2, ← Over.comp_left, lift_snd, hs.1, ← Category.assoc, ← Over.comp_left, lift_snd]

theorem act_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (hs : IsSquare φ φ₂) (u' : G' ⟶ G') (u : G ⟶ G)
    (hu : u'.left ≫ φ = φ ≫ u.left) :
    (lift (fst G' G') (snd G' G' ≫ u')).left ≫ φ₂ = φ₂ ≫ (lift (fst G G) (snd G G ≫ u)).left := by
  apply pullback.hom_ext
  · change _ ≫ φ₂ ≫ (fst G G).left = φ₂ ≫ (lift (fst G G) (snd G G ≫ u)).left ≫ (fst G G).left
    rw [hs.1, ← Category.assoc, ← Over.comp_left, lift_fst, ← Over.comp_left, lift_fst, hs.1]
  · change _ ≫ φ₂ ≫ (snd G G).left = φ₂ ≫ (lift (fst G G) (snd G G ≫ u)).left ≫ (snd G G).left
    rw [hs.2, ← Category.assoc, ← Over.comp_left, lift_snd, ← Over.comp_left, lift_snd, Over.comp_left,
      Over.comp_left, Category.assoc, hu, ← Category.assoc, ← hs.2, Category.assoc]

end GlobalTheory.RealMult.PullPol

namespace GlobalTheory.RealMult.PullPol

open GlobalTheory.CechPic in

theorem pol_pull : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (rm' : OAct (𝓞 F) A'),
    (∀ a, (rm'.act a).left ≫ φ = φ ≫ (X.rm.act a).left) → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ (c c' : 𝔠.elt) (a : 𝓞 F),
      LBIso ((X.P c).pull φ₂) (((X.P c).pull φ₂).pull (lift (snd A' A') (fst A' A')).left) ∧
      LBIso ((X.P c').pull φ₂) (LB.div ((X.P (c + c')).pull φ₂) ((X.P c).pull φ₂)) ∧
      LBIso ((X.P (a • c)).pull φ₂) (((X.P c).pull φ₂).pull (lift (fst A' A') (snd A' A' ≫ rm'.act a)).left) := by
  intro F _ _ 𝔠 S S' X b A' _ _ φ _ rm' hact φ₂ hs c c' a
  have hP := X.isLB
  refine ⟨(cls_eq_iff (pull_isLB (hP c) φ₂) (pull_isLB (pull_isLB (hP c) φ₂) _)).1 ?_,
    (cls_eq_iff (pull_isLB (hP c') φ₂) (LB.isLB_div (pull_isLB (hP _) φ₂) (pull_isLB (hP c) φ₂))).1 ?_,
    (cls_eq_iff (pull_isLB (hP _) φ₂) (pull_isLB (pull_isLB (hP c) φ₂) _)).1 ?_⟩
  · have h := (cls_eq_iff (hP c) (pull_isLB (hP c) _)).2 (X.symm c)
    rw [cls_pull (hP c)] at h
    rw [cls_pull (pull_isLB (hP c) φ₂), cls_pull (hP c), ← GlobalTheory.CechPic.pull_comp, swap_comp hs,
      GlobalTheory.CechPic.pull_comp, ← h]
  · have h := (cls_eq_iff (hP c') (LB.isLB_div (hP _) (hP c))).2 (X.add c c')
    rw [cls_div (pull_isLB (hP _) φ₂) (pull_isLB (hP c) φ₂), cls_pull (hP c'), cls_pull (hP _), cls_pull (hP c), h,
      cls_div (hP _) (hP c), map_sub]
  · have h := (cls_eq_iff (hP _) (pull_isLB (hP c) _)).2 (X.smul a c)
    rw [cls_pull (hP c)] at h
    rw [cls_pull (pull_isLB (hP c) φ₂), cls_pull (hP c), ← GlobalTheory.CechPic.pull_comp, act_comp hs _ _ (hact a),
      GlobalTheory.CechPic.pull_comp, ← h, cls_pull (hP _)]

end GlobalTheory.RealMult.PullPol
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_square_action_bundle_iso : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (rm' : OAct (𝓞 F) A'),
    (∀ a, (rm'.act a).left ≫ φ = φ ≫ (X.rm.act a).left) → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ (c c' : 𝔠.elt) (a : 𝓞 F),
      LBIso ((X.P c).pull φ₂) (((X.P c).pull φ₂).pull (lift (snd A' A') (fst A' A')).left) ∧
      LBIso ((X.P c').pull φ₂) (LB.div ((X.P (c + c')).pull φ₂) ((X.P c).pull φ₂)) ∧
      LBIso ((X.P (a • c)).pull φ₂) (((X.P c).pull φ₂).pull (lift (fst A' A') (snd A' A' ≫ rm'.act a)).left) := by
  atlas_forward_decl GlobalTheory.RealMult.PullPol.pol_pull
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.Obj

theorem relAmple_diag_of_isGrpPullback : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ c : 𝔠.elt, IsTotPos (c : F) → Out.RelAmple A' (((X.P c).pull φ₂).pull (lift (𝟙 A') (𝟙 A')).left) := by
  intro F _ _ 𝔠 S S' X b A' _ _ φ hg φ₂ hsq c hc
  haveI : IsProper X.A.hom := X.ab.proper
  have hP : IsPullback φ A'.hom X.A.hom b := hg.1
  haveI : IsProper A'.hom := MorphismProperty.of_isPullback (P := @IsProper) hP inferInstance
  have hM := pull_isLB (X.isLB c) (lift (𝟙 X.A) (𝟙 X.A)).left
  have h1 : Out.RelAmple A' (((X.P c).pull (lift (𝟙 X.A) (𝟙 X.A)).left).pull φ) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hM (X.pos c hc) hP
  have hL := pull_isLB (pull_isLB (X.isLB c) φ₂) (lift (𝟙 A') (𝟙 A')).left
  have hM' := pull_isLB hM φ
  have key : (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply pullback.hom_ext
    · show ((lift (𝟙 A') (𝟙 A')).left ≫ φ₂) ≫ (fst X.A X.A).left =
        (φ ≫ (lift (𝟙 X.A) (𝟙 X.A)).left) ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
        ← Over.comp_left, lift_fst, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
    · show ((lift (𝟙 A') (𝟙 A')).left ≫ φ₂) ≫ (snd X.A X.A).left =
        (φ ≫ (lift (𝟙 X.A) (𝟙 X.A)).left) ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
        ← Over.comp_left, lift_snd, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  refine GlobalTheory.PosDefAmple.relAmple_of_nsmul hL hM' (N := 1) le_rfl ?_ h1
  rw [one_smul]
  show GlobalTheory.CechPic.pull _ (GlobalTheory.CechPic.pull _ (GlobalTheory.CechPic.cls _ (X.isLB c))) =
    GlobalTheory.CechPic.pull _ (GlobalTheory.CechPic.pull _ (GlobalTheory.CechPic.cls _ (X.isLB c)))
  rw [← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, key]

end GlobalTheory.RealMult.Obj
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_square_diagonal_rel_ample : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ c : 𝔠.elt, IsTotPos (c : F) → Out.RelAmple A' (((X.P c).pull φ₂).pull (lift (𝟙 A') (𝟙 A')).left) := by
  atlas_forward_decl GlobalTheory.RealMult.Obj.relAmple_diag_of_isGrpPullback
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_square_action_sections_generated : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (rm' : OAct (𝓞 F) A'),
    (∀ a, (rm'.act a).left ≫ φ = φ ≫ (X.rm.act a).left) → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ (c : 𝔠.elt) (T : Over S') (x : T ⟶ A'),
      HasGen (((X.P c).pull φ₂).pull (lift (fst A' T) (snd A' T ≫ x)).left) →
      ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → x ≫ rm'.act a = 1 := by
  first | exact @GlobalTheory.PolKerPull.ker_pull | exact GlobalTheory.PolKerPull.ker_pull | (intros; apply GlobalTheory.PolKerPull.ker_pull <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullBy_comp' : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
    {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left},
    X''.IsPullBy X' b' ψ → X'.IsPullBy X b φ → X''.IsPullBy X (b' ≫ b) (ψ ≫ φ) := by
  first | exact @GlobalTheory.RealMult.Obj.IsPullBy.trans | exact GlobalTheory.RealMult.Obj.IsPullBy.trans | (intros; apply GlobalTheory.RealMult.Obj.IsPullBy.trans <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.Obj

theorem IsPullBy.exists_of_comp {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' S'' : Scheme.{0}}
    {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
    {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {χ : X''.A.left ⟶ X.A.left}
    (h : X''.IsPullBy X (b' ≫ b) χ) (h' : X'.IsPullBy X b φ) :
    ∃ ψ : X''.A.left ⟶ X'.A.left, X''.IsPullBy X' b' ψ ∧ ψ ≫ φ = χ := by
  have hp := h'.grp.1
  let ψ : X''.A.left ⟶ X'.A.left := hp.lift χ (X''.A.hom ≫ b') (by rw [h.grp.1.w, Category.assoc])
  have hψ : ψ ≫ φ = χ := hp.lift_fst _ _ _
  have hw : ψ ≫ X'.A.hom = X''.A.hom ≫ b' := hp.lift_snd _ _ _
  refine ⟨ψ, ⟨IsGrpPullback.cancel h'.grp (by rw [hψ]; exact h.grp) hw, fun a ↦ ?_, ?_⟩, hψ⟩
  · apply hp.hom_ext
    · rw [Category.assoc, hψ, h.act, Category.assoc, h'.act, ← Category.assoc, hψ]
    · have e₁ : (X''.rm.act a).left ≫ X''.A.hom = X''.A.hom := Over.w (X''.rm.act a)
      have e₂ : (X'.rm.act a).left ≫ X'.A.hom = X'.A.hom := Over.w (X'.rm.act a)
      rw [Category.assoc, hw, ← Category.assoc, e₁, Category.assoc, e₂, hw]
  · obtain ⟨φ₂'', hsq'', hP''⟩ := h.pol
    obtain ⟨φ₂', hsq', hP'⟩ := h'.pol
    let ψ₂ : (G2 X''.A).left ⟶ (G2 X'.A).left :=
      (lift (pushPt hw (fst X''.A X''.A)) (pushPt hw (snd X''.A X''.A))).left
    have hsq : IsSquare ψ ψ₂ := by
      constructor
      · change (lift (pushPt hw (fst X''.A X''.A)) (pushPt hw (snd X''.A X''.A)) ≫ fst X'.A X'.A).left = _
        rw [lift_fst]; rfl
      · change (lift (pushPt hw (fst X''.A X''.A)) (pushPt hw (snd X''.A X''.A)) ≫ snd X'.A X'.A).left = _
        rw [lift_snd]; rfl
    have hcomp : ψ₂ ≫ φ₂' = φ₂'' := by
      apply pullback.hom_ext
      · change ψ₂ ≫ φ₂' ≫ (fst X.A X.A).left = φ₂'' ≫ (fst X.A X.A).left
        rw [hsq'.1, ← Category.assoc, hsq.1, Category.assoc, hψ, hsq''.1]
      · change ψ₂ ≫ φ₂' ≫ (snd X.A X.A).left = φ₂'' ≫ (snd X.A X.A).left
        rw [hsq'.2, ← Category.assoc, hsq.2, Category.assoc, hψ, hsq''.2]
    refine ⟨ψ₂, hsq, fun c ↦ ?_⟩
    have hX := X.isLB c
    have hX' := X'.isLB c
    refine (GlobalTheory.CechPic.cls_eq_iff (X''.isLB c) (pull_isLB hX' ψ₂)).1 ?_
    rw [(GlobalTheory.CechPic.cls_eq_iff (X''.isLB c) (pull_isLB hX φ₂'')).2 (hP'' c),
      GlobalTheory.CechPic.cls_pull hX' ψ₂, GlobalTheory.CechPic.cls_pull hX φ₂'', ← hcomp, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull hX φ₂' (pull_isLB hX φ₂'),
      ← (GlobalTheory.CechPic.cls_eq_iff hX' (pull_isLB hX φ₂')).2 (hP' c)]

end GlobalTheory.RealMult.Obj
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullBy_factor_through : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
    {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {χ : X''.A.left ⟶ X.A.left},
    X''.IsPullBy X (b' ≫ b) χ → X'.IsPullBy X b φ →
    ∃ ψ : X''.A.left ⟶ X'.A.left, X''.IsPullBy X' b' ψ ∧ ψ ≫ φ = χ := by
  atlas_forward_decl GlobalTheory.RealMult.Obj.IsPullBy.exists_of_comp
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.LevelPull

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem toUnit_left {S : Scheme.{0}} {T : Over S} (u : T ⟶ 𝟙_ (Over S)) : u.left = T.hom := by
  simpa using Over.w u

theorem push_inj {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (hg : IsGrpPullback X'.A X.A b φ) {T : Over S'} {x y : T ⟶ X'.A}
    (e : pushPt hg.1.w x = pushPt hg.1.w y) : x = y := by
  apply Over.OverMorphism.ext
  apply hg.1.hom_ext
  · exact congrArg (fun z => z.left) e
  · rw [Over.w, Over.w]

def liftPt {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (hg : IsGrpPullback X'.A X.A b φ) (p : 𝟙_ (Over S) ⟶ X.A) :
    𝟙_ (Over S') ⟶ X'.A :=
  Over.homMk (hg.1.lift (b ≫ p.left) (𝟙_ (Over S')).hom (by
    rw [Category.assoc, Over.w p]; simp)) (hg.1.lift_snd _ _ _)

theorem liftPt_push {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (hg : IsGrpPullback X'.A X.A b φ) (p : 𝟙_ (Over S) ⟶ X.A) :
    (liftPt hg p).left ≫ φ = b ≫ p.left :=
  hg.1.lift_fst _ _ _

theorem push_liftPt_act {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X b φ) (p : 𝟙_ (Over S) ⟶ X.A) {T : Over S'}
    (u : T ⟶ 𝟙_ (Over S')) (a : 𝓞 F) :
    pushPt h.grp.1.w (u ≫ liftPt h.grp p ≫ X'.rm.act a) =
      toUnit (Over.mk (T.hom ≫ b)) ≫ p ≫ X.rm.act a := by
  apply Over.OverMorphism.ext
  show (u ≫ liftPt h.grp p ≫ X'.rm.act a).left ≫ φ = (toUnit (Over.mk (T.hom ≫ b)) ≫ p ≫ X.rm.act a).left
  simp only [Over.comp_left, Category.assoc]
  rw [h.act a, ← Category.assoc (liftPt h.grp p).left, liftPt_push, toUnit_left, toUnit_left]
  simp

section
variable {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (hg : IsGrpPullback X'.A X.A b φ) {T : Over S'}

theorem push_mul (x y : T ⟶ X'.A) : pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y :=
  map_mul (pushHom hg T) x y

theorem push_one : pushPt hg.1.w (1 : T ⟶ X'.A) = 1 := map_one (pushHom hg T)

theorem push_pow (x : T ⟶ X'.A) (n : ℕ) : pushPt hg.1.w (x ^ n) = pushPt hg.1.w x ^ n :=
  map_pow (pushHom hg T) x n
end

theorem exists_level_pull : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X b φ → ∀ {N : ℕ} (α : X.Level N),
    ∃ α' : X'.Level N, ∀ i, (α'.pt i).left ≫ φ = b ≫ (α.pt i).left := by
  intro F _ _ 𝔠 S S' X X' b φ h N α
  refine ⟨⟨fun i => liftPt h.grp (α.pt i), ?_, ?_, ?_⟩, fun i => liftPt_push h.grp _⟩
  · intro i
    apply push_inj h.grp
    have e2 : pushPt h.grp.1.w (liftPt h.grp (α.pt i)) =
        toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ b)) ≫ α.pt i := by
      apply Over.OverMorphism.ext
      show (liftPt h.grp (α.pt i)).left ≫ φ = (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ b)) ≫ α.pt i).left
      rw [liftPt_push, Over.comp_left, toUnit_left]
      simp
    have e3 : (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ b)) ≫ α.pt i) ^ N =
        toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ b)) ≫ α.pt i ^ N :=
      (map_pow (preHom (G := X.A) (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ b)))) (α.pt i) N).symm
    rw [push_pow h.grp, e2, e3, α.tors i, push_one h.grp]
    exact MonObj.comp_one _
  · intro Ω _ _ t a c hyp
    apply α.inj Ω (t ≫ b) a c
    have e := congrArg (pushPt h.grp.1.w) hyp
    rw [push_mul h.grp, push_one h.grp, push_liftPt_act h (α.pt 0), push_liftPt_act h (α.pt 1)] at e
    exact e
  · intro Ω _ _ t y hy
    obtain ⟨a, c, hac⟩ := α.surj Ω (t ≫ b) (pushPt h.grp.1.w y) (by
      rw [← push_pow h.grp, hy, push_one h.grp])
    refine ⟨a, c, push_inj h.grp ?_⟩
    rw [push_mul h.grp, push_liftPt_act h (α.pt 0), push_liftPt_act h (α.pt 1)]
    exact hac

end GlobalTheory.RealMult.LevelPull
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_structure_pullback_exists : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X b φ → ∀ {N : ℕ} (α : X.Level N),
    ∃ α' : X'.Level N, ∀ i, (α'.pt i).left ≫ φ = b ≫ (α.pt i).left := by
  first | exact @GlobalTheory.RealMult.LevelPull.exists_level_pull | exact GlobalTheory.RealMult.LevelPull.exists_level_pull | (intros; apply GlobalTheory.RealMult.LevelPull.exists_level_pull <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace AltBaseChange

section General

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  {X W : Type} [AddCommGroup X] [Module R X] [AddCommGroup W] [Module R W] [Module R' W]
  [IsScalarTower R R' W] {j : X →ₗ[R] W} (hj : IsBaseChange R' j) (n : ℕ)

def bc (g : X [⋀^Fin n]→ₗ[R] R) : W [⋀^Fin n]→ₗ[R'] R' :=
  exteriorPower.alternatingMapLinearEquiv.symm
    ((TopForm.isBaseChange_exteriorPower hj n).toDual
      (exteriorPower.alternatingMapLinearEquiv g))

theorem bc_apply (g : X [⋀^Fin n]→ₗ[R] R) (v : Fin n → X) :
    bc hj n g (fun i => j (v i)) = algebraMap R R' (g v) := by
  unfold bc
  rw [← exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, LinearEquiv.apply_symm_apply,
    ← exteriorPowerMapOver_ιMulti (B := R'), IsBaseChange.toDual_comp_apply,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

include hj in
theorem ext_tuples {ω₁ ω₂ : W [⋀^Fin n]→ₗ[R'] R'}
    (h : ∀ v : Fin n → X, ω₁ (fun i => j (v i)) = ω₂ (fun i => j (v i))) : ω₁ = ω₂ := by
  apply exteriorPower.alternatingMapLinearEquiv.injective
  apply (TopForm.isBaseChange_exteriorPower hj n).algHom_ext
  intro x
  have key : ((exteriorPower.alternatingMapLinearEquiv ω₁).restrictScalars R).comp
        (exteriorPowerMapOver R' n j) =
      ((exteriorPower.alternatingMapLinearEquiv ω₂).restrictScalars R).comp
        (exteriorPowerMapOver R' n j) := by
    apply exteriorPower.linearMap_ext
    ext v
    simp [h]
  exact LinearMap.congr_fun key x

theorem bc_smul (r : R) (g : X [⋀^Fin n]→ₗ[R] R) :
    bc hj n (r • g) = algebraMap R R' r • bc hj n g :=
  ext_tuples hj n fun v => by simp [bc_apply]

theorem mem_span_bc_of_free [Module.Free R X] [Module.Finite R X]
    (ω : W [⋀^Fin n]→ₗ[R'] R') : ω ∈ Submodule.span R' (Set.range (bc hj n)) := by
  obtain ⟨L, rfl⟩ := exteriorPower.alternatingMapLinearEquiv.symm.surjective ω
  have hD := (TopForm.isBaseChange_exteriorPower hj n).dual
  induction L using hD.inductionOn with
  | zero => simp
  | tmul m =>
    refine Submodule.subset_span ⟨exteriorPower.alternatingMapLinearEquiv.symm m, ?_⟩
    simp [bc]
  | smul s L h => rw [map_smul]; exact Submodule.smul_mem _ _ h
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

end General

end AltBaseChange

end GlobalTheory

namespace GlobalTheory

namespace AltBaseChange

section Projective

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  {M : Type} [AddCommGroup M] [Module R M] (n : ℕ)

theorem exists_smul_bc_eq [Module.Finite R M] [Module.Projective R M]
    (δ : M [⋀^Fin n]→ₗ[R] R) (hδ : Submodule.span R {δ} = ⊤)
    (ω : (R' ⊗[R] M) [⋀^Fin n]→ₗ[R'] R') :
    ω ∈ Submodule.span R' {bc (TensorProduct.isBaseChange R M R') n δ} := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hF := TensorProduct.isBaseChange R (Fin k → R) R'
  have hM := TensorProduct.isBaseChange R M R'
  have hfs (x : R' ⊗[R] M) : f.baseChange R' (s.baseChange R' x) = x := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hs, LinearMap.baseChange_id,
      LinearMap.id_apply]
  let Φ : ((R' ⊗[R] (Fin k → R)) [⋀^Fin n]→ₗ[R'] R') →ₗ[R'] ((R' ⊗[R] M) [⋀^Fin n]→ₗ[R'] R') :=
    { toFun := fun t => t.compLinearMap (s.baseChange R')
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun _ _ => by ext; simp }
  have hω : Φ (ω.compLinearMap (f.baseChange R')) = ω := by
    ext v
    simp [Φ, hfs]
  have hη := mem_span_bc_of_free hF n (ω.compLinearMap (f.baseChange R'))
  rw [← hω]
  have hmap := Submodule.mem_map_of_mem (f := Φ) hη
  rw [Submodule.map_span] at hmap
  refine Submodule.span_le.mpr ?_ hmap
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  have hg : g.compLinearMap s ∈ Submodule.span R {δ} := hδ ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hg
  have : Φ (bc hF n g) = algebraMap R R' r • bc hM n δ := by
    rw [← bc_smul, hr]
    refine ext_tuples hM n fun v => ?_
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, AlternatingMap.compLinearMap_apply]
    rw [bc_apply hM n]
    have h1 : (fun i => s.baseChange R' (TensorProduct.mk R R' M 1 (v i))) =
        fun i => TensorProduct.mk R R' (Fin k → R) 1 (s (v i)) := by
      funext i
      simp
    rw [h1, bc_apply hF n]
    rfl
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Projective

end AltBaseChange

end GlobalTheory

namespace GlobalTheory

namespace AltBaseChange

theorem exists_unique_baseChange_generator : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (N : Type) [AddCommGroup N] [Module R' N] (e : R' ⊗[R] M ≃ₗ[R'] N)
    (n : ℕ) (δ : M [⋀^Fin n]→ₗ[R] R), Submodule.span R {δ} = ⊤ →
    ∃! δ' : N [⋀^Fin n]→ₗ[R'] R', Submodule.span R' {δ'} = ⊤ ∧
      ∀ v : Fin n → M, δ' (fun i ↦ e (1 ⊗ₜ v i)) = algebraMap R R' (δ v) := by
  intro R R' _ _ _ M _ _ _ _ N _ _ e n δ hδ
  have hM := TensorProduct.isBaseChange R M R'
  let δ' : N [⋀^Fin n]→ₗ[R'] R' := (bc hM n δ).compLinearMap e.symm.toLinearMap
  have hval (v : Fin n → M) : δ' (fun i ↦ e (1 ⊗ₜ v i)) = algebraMap R R' (δ v) := by
    simp only [δ', AlternatingMap.compLinearMap_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact bc_apply hM n δ v
  refine ⟨δ', ⟨?_, hval⟩, ?_⟩
  · rw [Submodule.eq_top_iff']
    intro ω
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (exists_smul_bc_eq n δ hδ (ω.compLinearMap e.toLinearMap))
    refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
    ext x
    have := congrArg (fun t => t (fun i => e.symm (x i))) ha
    simpa [δ'] using this
  · rintro y ⟨-, hy⟩
    have key : y.compLinearMap e.toLinearMap = bc hM n δ := by
      refine ext_tuples hM n fun v => ?_
      simp only [AlternatingMap.compLinearMap_apply, LinearEquiv.coe_coe]
      rw [bc_apply hM n]
      exact hy v
    ext x
    have := congrArg (fun t => t (fun i => e.symm (x i))) key
    simpa [δ'] using this

end AltBaseChange

end GlobalTheory
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_base_change_volume_form : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (N : Type) [AddCommGroup N] [Module R' N] (e : R' ⊗[R] M ≃ₗ[R'] N)
    (n : ℕ) (δ : M [⋀^Fin n]→ₗ[R] R), Submodule.span R {δ} = ⊤ →
    ∃! δ' : N [⋀^Fin n]→ₗ[R'] R', Submodule.span R' {δ'} = ⊤ ∧
      ∀ v : Fin n → M, δ' (fun i ↦ e (1 ⊗ₜ v i)) = algebraMap R R' (δ v) := by
  atlas_forward_decl GlobalTheory.AltBaseChange.exists_unique_baseChange_generator
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvertibleTopExteriorPower

theorem invertible_exteriorPower_top (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (n : ℕ)
    (hn : ∀ p, Module.rankAtStalk (R := R) M p = n) : Module.Invertible R (⋀[R]^n M) := by
  let s : Set R := {a | Module.Free (Localization.Away a) (LocalizedModule.Away a M)}
  have hs : Ideal.span s = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨a, ha, hfree⟩ := Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant M m
      (fun m' _ => by rw [hn, hn])
    exact ha (hsm (Ideal.subset_span hfree))
  have hloc : ∀ r : s, IsLocalizedModule.Away r.1 (exteriorPowerMapOver (Localization.Away r.1) n
      (LocalizedModule.mkLinearMap (Submonoid.powers r.1) M)) := fun r =>
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers r.1) (Localization.Away r.1) _).2
      (GlobalTheory.TopForm.isBaseChange_exteriorPower
        (LocalizedModule.isBaseChange (Submonoid.powers r.1) M) n)
  refine GlobalTheory.invertible_of_isLocalizedModule_span s hs (fun r => Localization.Away r.1)
    (fun r => ⋀[Localization.Away r.1]^n (LocalizedModule.Away r.1 M))
    (fun r => exteriorPowerMapOver (Localization.Away r.1) n
      (LocalizedModule.mkLinearMap (Submonoid.powers r.1) M)) fun r => ?_
  have hfree : Module.Free (Localization.Away r.1) (LocalizedModule.Away r.1 M) := r.2
  rcases subsingleton_or_nontrivial (Localization.Away r.1) with hB | hB
  · haveI : Subsingleton (⋀[Localization.Away r.1]^n (LocalizedModule.Away r.1 M)) :=
      Module.subsingleton (Localization.Away r.1) _
    exact Module.Invertible.congr (LinearEquiv.ofSubsingleton (Localization.Away r.1)
      (⋀[Localization.Away r.1]^n (LocalizedModule.Away r.1 M)))
  · obtain ⟨q⟩ : Nonempty (PrimeSpectrum (Localization.Away r.1)) := inferInstance
    have hfr : Module.finrank (Localization.Away r.1) (LocalizedModule.Away r.1 M) = n := by
      have h1 := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := Localization.Away r.1)
        (M := LocalizedModule.Away r.1 M)) q
      rw [Module.rankAtStalk_isBaseChange
        (LocalizedModule.isBaseChange (Submonoid.powers r.1) M), hn] at h1
      exact h1.symm
    let b := Module.finBasisOfFinrankEq (Localization.Away r.1) (LocalizedModule.Away r.1 M) hfr
    have hb := GlobalTheory.TopForm.isFreeGen_ιMulti b
    exact Module.Invertible.congr (LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ _) hb)

theorem invertible_alternatingMap_top : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (n : ℕ),
    (∀ p, Module.rankAtStalk (R := R) M p = n) → Module.Invertible R (M [⋀^Fin n]→ₗ[R] R) := by
  intro R _ M _ _ _ _ n hn
  haveI := invertible_exteriorPower_top R M n hn
  exact Module.Invertible.congr
    (exteriorPower.alternatingMapLinearEquiv (R := R) (M := M) (N := R) (n := n)).symm

end GlobalTheory.InvertibleTopExteriorPower
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_exterior_dual_invertible : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (n : ℕ), (∀ p, Module.rankAtStalk (R := R) M p = n) → Module.Invertible R (M [⋀^Fin n]→ₗ[R] R) := by
  atlas_forward_decl GlobalTheory.InvertibleTopExteriorPower.invertible_alternatingMap_top
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory

theorem invertible_of_baseChange_tensor_int :
    ∀ (R R' O : Type) [CommRing R] [CommRing R'] [Algebra R R'] [CommRing O] (M : Type) [AddCommGroup M]
    [Module R M] [Module O M] [SMulCommClass R O M] (N : Type) [AddCommGroup N] [Module R' N] [Module O N]
    [SMulCommClass R' O N] (e : R' ⊗[R] M ≃ₗ[R'] N), (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    letI : Module (R' ⊗[ℤ] O) N := TensorProduct.Algebra.module
    Module.Invertible (R ⊗[ℤ] O) M → Module.Invertible (R' ⊗[ℤ] O) N := by
  intro R R' O _ _ _ _ M _ _ _ _ N _ _ _ _ e he hM
  letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
  letI : Module (R' ⊗[ℤ] O) N := TensorProduct.Algebra.module
  let f : R ⊗[ℤ] O →ₐ[ℤ] R' ⊗[ℤ] O :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℤ R R') (AlgHom.id ℤ O)
  letI : Algebra (R ⊗[ℤ] O) (R' ⊗[ℤ] O) := f.toRingHom.toAlgebra
  letI : Module (R ⊗[ℤ] O) N := Module.compHom N f.toRingHom
  haveI : IsScalarTower (R ⊗[ℤ] O) (R' ⊗[ℤ] O) N := ⟨fun a x n => mul_smul (f a) x n⟩
  have hf : ∀ (r : R) (o : O), f (r ⊗ₜ o) = algebraMap R R' r ⊗ₜ o := fun r o => rfl
  have hj : ∀ (a : R ⊗[ℤ] O) (m : M), e (1 ⊗ₜ (a • m)) = f a • e (1 ⊗ₜ m) := by
    intro a m
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r o =>
      rw [hf, TensorProduct.Algebra.smul_def, TensorProduct.Algebra.smul_def, ← he,
        TensorProduct.tmul_smul, ← algebraMap_smul R', map_smul]
    | add a b ha hb => rw [add_smul, tmul_add, map_add, ha, hb, map_add, add_smul]
  let j : M →ₗ[R ⊗[ℤ] O] N :=
    { toFun := fun m => e (1 ⊗ₜ m)
      map_add' := fun x y => by simp [tmul_add]
      map_smul' := fun a m => hj a m }
  let Φ : (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M →ₗ[R' ⊗[ℤ] O] N := LinearMap.liftBaseChange _ j
  let g : R' →+ M →+ (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M :=
    AddMonoidHom.mk' (fun r' => (TensorProduct.mk (R ⊗[ℤ] O) (R' ⊗[ℤ] O) M
      (r' ⊗ₜ[ℤ] (1 : O))).toAddMonoidHom) (by intro a b; ext m; simp [add_tmul])
  let ψ : R' ⊗[R] M →+ (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M := TensorProduct.liftAddHom g (by
    intro r r' m
    have hr : r • m = ((r ⊗ₜ[ℤ] (1 : O)) : R ⊗[ℤ] O) • m := by
      rw [TensorProduct.Algebra.smul_def, one_smul]
    simp only [g, AddMonoidHom.mk'_apply, LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
    rw [hr, ← TensorProduct.smul_tmul, Algebra.smul_def]
    congr 1
    change _ = f (r ⊗ₜ 1) * _
    simp only [hf, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, Algebra.smul_def])
  have h1 : ∀ y, Φ (ψ y) = e y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r' m =>
      simp only [ψ, TensorProduct.liftAddHom_tmul, g, AddMonoidHom.mk'_apply,
        LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply, Φ, LinearMap.liftBaseChange_tmul]
      change (r' ⊗ₜ[ℤ] (1 : O)) • e (1 ⊗ₜ m) = _
      rw [TensorProduct.Algebra.smul_def, one_smul, ← map_smul, TensorProduct.smul_tmul',
        smul_eq_mul, _root_.mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have h2 : ∀ z, ψ (e.symm (Φ z)) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x m =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r' o =>
        have hΦ : Φ ((r' ⊗ₜ[ℤ] o) ⊗ₜ m) = e (r' ⊗ₜ (o • m)) := by
          simp only [Φ, LinearMap.liftBaseChange_tmul]
          change (r' ⊗ₜ[ℤ] o) • e (1 ⊗ₜ m) = _
          rw [TensorProduct.Algebra.smul_def, ← he, ← map_smul, TensorProduct.smul_tmul',
            smul_eq_mul, _root_.mul_one]
        rw [hΦ, LinearEquiv.symm_apply_apply]
        simp only [ψ, TensorProduct.liftAddHom_tmul, g, AddMonoidHom.mk'_apply,
          LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
        have ho : o • m = (((1 : R) ⊗ₜ[ℤ] o) : R ⊗[ℤ] O) • m := by
          rw [TensorProduct.Algebra.smul_def, one_smul]
        rw [ho, ← TensorProduct.smul_tmul, Algebra.smul_def]
        congr 1
        change f (1 ⊗ₜ o) * _ = _
        rw [hf, map_one, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one]
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hinj : Function.Injective Φ := fun a b hab => by rw [← h2 a, ← h2 b, hab]
  have hsurj : Function.Surjective Φ := fun n =>
    ⟨ψ (e.symm n), by rw [h1, LinearEquiv.apply_symm_apply]⟩
  haveI := hM
  exact Module.Invertible.congr (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩)

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_module_tensor_action : ∀ (R R' O : Type) [CommRing R] [CommRing R'] [Algebra R R'] [CommRing O] (M : Type) [AddCommGroup M]
    [Module R M] [Module O M] [SMulCommClass R O M] (N : Type) [AddCommGroup N] [Module R' N] [Module O N]
    [SMulCommClass R' O N] (e : R' ⊗[R] M ≃ₗ[R'] N), (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    letI : Module (R' ⊗[ℤ] O) N := TensorProduct.Algebra.module
    Module.Invertible (R ⊗[ℤ] O) M → Module.Invertible (R' ⊗[ℤ] O) N := by
  atlas_forward_decl GlobalTheory.invertible_of_baseChange_tensor_int
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.exists_fibre_generator_basis : ∀ (R O : Type) [CommRing R] [CommRing O] (J : Type) [Fintype J] (b : Module.Basis J ℤ O)
    (M : Type) [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M]
    (K : Type) [Field K] [Algebra R K],
    (∀ k : K, ∃ a s : R, algebraMap R K s ≠ 0 ∧ algebraMap R K s * k = algebraMap R K a) →
    ∀ (N : Type) [AddCommGroup N] [Module K N] [Module O N] [SMulCommClass K O N]
    (e : K ⊗[R] M ≃ₗ[K] N),
    (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) →
    (letI : Module (K ⊗[ℤ] O) N := TensorProduct.Algebra.module;
      Module.Invertible (K ⊗[ℤ] O) N) →
    ∃ m : M, Function.Bijective
      (Finsupp.linearCombination K (fun i => (1 : K) ⊗ₜ[R] (b i • m))) := by
  intro R O _ _ J _ b M _ _ _ _ K _ _ hfrac N _ _ _ _ e he hinv
  letI : Module (K ⊗[ℤ] O) N := TensorProduct.Algebra.module
  let B := Algebra.TensorProduct.basis K b
  haveI : Module.Finite K (K ⊗[ℤ] O) := Module.Finite.of_basis B
  haveI : IsArtinianRing (K ⊗[ℤ] O) := IsArtinianRing.of_finite K _
  haveI : Finite (MaximalSpectrum (K ⊗[ℤ] O)) := IsArtinianRing.instFiniteMaximalSpectrum _
  obtain ⟨n₀, hn₀⟩ :=
    GlobalTheory.exists_bijective_toSpanSingleton_of_finite_maximalSpectrum (K ⊗[ℤ] O) N
  have hsc : ∀ (r : R) (m : M), algebraMap R K r • ((1 : K) ⊗ₜ[R] m) = (1 : K) ⊗ₜ[R] (r • m) := by
    intro r m
    rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  have key : ∀ θ : K ⊗[R] M, ∃ s : R, algebraMap R K s ≠ 0 ∧
      ∃ m : M, algebraMap R K s • θ = (1 : K) ⊗ₜ[R] m := by
    intro θ
    induction θ using TensorProduct.induction_on with
    | zero => exact ⟨1, by simp, 0, by simp⟩
    | tmul k m =>
      obtain ⟨a, s, hs, hk⟩ := hfrac k
      refine ⟨s, hs, a • m, ?_⟩
      rw [TensorProduct.smul_tmul', smul_eq_mul, hk, ← hsc, TensorProduct.smul_tmul', smul_eq_mul,
        _root_.mul_one]
    | add x y hx hy =>
      obtain ⟨s, hs, m, hm⟩ := hx
      obtain ⟨t, ht, m', hm'⟩ := hy
      refine ⟨s * t, by rw [map_mul]; exact mul_ne_zero hs ht, t • m + s • m', ?_⟩
      rw [smul_add, map_mul, mul_comm, mul_smul, hm, mul_comm, mul_smul, hm', hsc, hsc,
        TensorProduct.tmul_add]
  obtain ⟨s, hs, m, hm⟩ := key (e.symm n₀)
  refine ⟨m, ?_⟩
  set k : K := algebraMap R K s with hk
  have hn : e ((1 : K) ⊗ₜ[R] m) = (k ⊗ₜ[ℤ] (1 : O)) • n₀ := by
    rw [← hm, map_smul, e.apply_symm_apply, TensorProduct.Algebra.smul_def, one_smul]
  have hu : IsUnit (k ⊗ₜ[ℤ] (1 : O)) := by
    refine ⟨⟨k ⊗ₜ[ℤ] (1 : O), k⁻¹ ⊗ₜ[ℤ] (1 : O), ?_, ?_⟩, rfl⟩ <;>
      simp [Algebra.TensorProduct.tmul_mul_tmul, hs, Algebra.TensorProduct.one_def]
  set n := e ((1 : K) ⊗ₜ[R] m) with hndef
  have hcomp : ∀ c : J →₀ K, e (Finsupp.linearCombination K (fun i => (1 : K) ⊗ₜ[R] (b i • m)) c)
      = (B.repr.symm c) • n := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, add_smul]
    | single i a =>
      rw [Finsupp.linearCombination_single, map_smul, he, B.repr_symm_single,
        Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one,
        TensorProduct.Algebra.smul_def]
  have hfun : ⇑(Finsupp.linearCombination K (fun i => (1 : K) ⊗ₜ[R] (b i • m)))
      = e.symm ∘ (fun x : K ⊗[ℤ] O => x • n) ∘ B.repr.symm := by
    funext c
    simp only [Function.comp_apply, ← hcomp c, e.symm_apply_apply]
  have hg : Function.Bijective (fun x : K ⊗[ℤ] O => x • n) := by
    have h1 : (fun x : K ⊗[ℤ] O => x • n)
        = (LinearMap.toSpanSingleton (K ⊗[ℤ] O) N n₀) ∘ (fun x => x * hu.unit) := by
      funext x
      simp [hn, mul_smul]
    rw [h1]
    exact hn₀.comp (Units.mulRight hu.unit).bijective
  rw [hfun]
  exact e.symm.bijective.comp (hg.comp B.repr.symm.bijective)
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_action_fraction_field : ∀ (R O : Type) [CommRing R] [CommRing O] (J : Type) [Fintype J] (b : Module.Basis J ℤ O)
    (M : Type) [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M]
    (K : Type) [Field K] [Algebra R K],
    (∀ k : K, ∃ a s : R, algebraMap R K s ≠ 0 ∧ algebraMap R K s * k = algebraMap R K a) →
    ∀ (N : Type) [AddCommGroup N] [Module K N] [Module O N] [SMulCommClass K O N]
    (e : K ⊗[R] M ≃ₗ[K] N),
    (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) →
    (letI : Module (K ⊗[ℤ] O) N := TensorProduct.Algebra.module;
      Module.Invertible (K ⊗[ℤ] O) N) →
    ∃ m : M, Function.Bijective
      (Finsupp.linearCombination K (fun i => (1 : K) ⊗ₜ[R] (b i • m))) := by
  atlas_forward_decl GlobalTheory.exists_fibre_generator_basis
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_generators_residue_basis : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (J : Type) [Fintype J] (v : J → M) (p : Ideal R) [p.IsPrime],
    Function.Bijective (Finsupp.linearCombination p.ResidueField (fun i => (1 : p.ResidueField) ⊗ₜ[R] v i)) →
    ∃ g : R, g ∉ p ∧ (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R v c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R v c = 0 → ∃ n : ℕ, g ^ n • c = 0) := by
  first | exact @GlobalTheory.FibreBasisSpread.exists_away_linearCombination_bijective | exact GlobalTheory.FibreBasisSpread.exists_away_linearCombination_bijective | (intros; apply GlobalTheory.FibreBasisSpread.exists_away_linearCombination_bijective <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvGlue

theorem bijective_localized {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (r : A) (m : M)
    (hsurj : ∀ x : M, ∃ (n : ℕ) (a : A), r ^ n • x = a • m)
    (hinj : ∀ a : A, a • m = 0 → ∃ n : ℕ, r ^ n * a = 0) :
    Function.Bijective (LinearMap.toSpanSingleton (Localization.Away r)
      (LocalizedModule (Submonoid.powers r) M) (LocalizedModule.mk m 1)) := by
  let pw : ℕ → Submonoid.powers r := fun n => ⟨r ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers r) n⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    induction y using Localization.induction_on with
    | H p =>
      obtain ⟨a, s⟩ := p
      simp only [LinearMap.toSpanSingleton_apply] at hy
      rw [LocalizedModule.mk_smul_mk, _root_.mul_one] at hy
      rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq] at hy
      obtain ⟨u, hu⟩ := hy
      simp only [smul_zero] at hu
      have : ((u : A) * (s : A) * a) • m = 0 := by
        rw [mul_smul, mul_smul]; simpa [Submonoid.smul_def] using hu
      obtain ⟨n, hn⟩ := hinj _ this
      rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
      exact ⟨pw n * u * s, by simpa [pw, _root_.mul_assoc] using hn⟩
  · intro z
    induction z using LocalizedModule.induction_on with
    | h x s =>
      obtain ⟨n, a, hn⟩ := hsurj x
      refine ⟨Localization.mk a (pw n * s), ?_⟩
      simp only [LinearMap.toSpanSingleton_apply]
      rw [LocalizedModule.mk_smul_mk, _root_.mul_one, ← hn,
        ← LocalizedModule.mk_cancel_common_left (pw n) s x]
      rfl

theorem invertible_of_locally_singly_generated : ∀ (R O : Type) [CommRing R] [CommRing O] (J : Type) [Fintype J] (b : Module.Basis J ℤ O)
    (M : Type) [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M],
    (∀ p : Ideal R, p.IsMaximal → ∃ g : R, g ∉ p ∧ ∃ m : M,
      (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R (fun i => b i • m) c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R (fun i => b i • m) c = 0 → ∃ n : ℕ, g ^ n • c = 0)) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    Module.Invertible (R ⊗[ℤ] O) M := by
  intro R O _ _ J _ b M _ _ _ _ hyp
  letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
  let B := Algebra.TensorProduct.basis R b
  have hL : ∀ (m : M) (c : J →₀ R),
      (B.repr.symm c) • m = Finsupp.linearCombination R (fun i => b i • m) c := by
    intro m c
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => rw [map_add, add_smul, hc, hd, map_add]
    | single i x =>
      rw [Module.Basis.repr_symm_single, Finsupp.linearCombination_single]
      simp only [B, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul,
        _root_.mul_one]
      exact TensorProduct.Algebra.smul_def x (b i) m
  have hr : ∀ (g : R) (x : M), (algebraMap R (R ⊗[ℤ] O) g) • x = g • x := by
    intro g x
    rw [Algebra.TensorProduct.algebraMap_apply, TensorProduct.Algebra.smul_def, one_smul]
    simp
  let G : Set R := {g | ∃ m : M,
      (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R (fun i => b i • m) c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R (fun i => b i • m) c = 0 → ∃ n : ℕ, g ^ n • c = 0)}
  have hG : Ideal.span G = ⊤ := by
    by_contra h
    obtain ⟨p, hp, hGp⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨g, hg, hgG⟩ := hyp p hp
    exact hg (hGp (Ideal.subset_span hgG))
  let s : Set (R ⊗[ℤ] O) := algebraMap R (R ⊗[ℤ] O) '' G
  have hs : Ideal.span s = ⊤ := by
    rw [← Ideal.map_span, hG, Ideal.map_top]
  refine GlobalTheory.invertible_of_isLocalizedModule_span s hs (fun r => Localization.Away r.1)
    (fun r => LocalizedModule (Submonoid.powers r.1) M)
    (fun r => LocalizedModule.mkLinearMap (Submonoid.powers r.1) M) fun r => ?_
  obtain ⟨g, ⟨m, h1, h2⟩, hg⟩ := r.2
  refine GlobalTheory.invertible_of_bijective_toSpanSingleton (e := LocalizedModule.mk m 1)
    (bijective_localized r.1 m ?_ ?_)
  · intro x
    obtain ⟨n, c, hc⟩ := h1 x
    exact ⟨n, B.repr.symm c, by rw [← hg, ← map_pow, hr, hL, hc]⟩
  · intro a ha
    have ha' : a = B.repr.symm (B.repr a) := (B.repr.symm_apply_apply a).symm
    obtain ⟨n, hn⟩ := h2 (B.repr a) (by rw [← hL, ← ha', ha])
    refine ⟨n, ?_⟩
    rw [← hg, ← map_pow, ← Algebra.smul_def, ha', ← map_smul, hn, map_zero]

end GlobalTheory.InvGlue
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_free_of_maximal_ideal_generator : ∀ (R O : Type) [CommRing R] [CommRing O] (J : Type) [Fintype J] (b : Module.Basis J ℤ O)
    (M : Type) [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M],
    (∀ p : Ideal R, p.IsMaximal → ∃ g : R, g ∉ p ∧ ∃ m : M,
      (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R (fun i => b i • m) c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R (fun i => b i • m) c = 0 → ∃ n : ℕ, g ^ n • c = 0)) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    Module.Invertible (R ⊗[ℤ] O) M := by
  atlas_forward_decl GlobalTheory.InvGlue.invertible_of_locally_singly_generated
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem residueField_exists_algebraMap_mul_eq (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime]
    (k : p.ResidueField) : ∃ a s : R, algebraMap R p.ResidueField s ≠ 0 ∧
      algebraMap R p.ResidueField s * k = algebraMap R p.ResidueField a := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective k
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
  refine ⟨a, s, ?_, ?_⟩
  · rw [Ne, Ideal.algebraMap_residueField_eq_zero]; exact s.2
  · rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime p) p.ResidueField,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime p) p.ResidueField a]
    simp only [IsLocalRing.ResidueField.algebraMap_eq]
    rw [← map_mul, IsLocalization.mk'_spec']

theorem invertible_of_fibres_invertible : ∀ (R O : Type) [CommRing R] [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] (M : Type)
    [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M] [Module.Finite R M] [Module.Projective R M],
    (∀ (K : Type) [Field K] [Algebra R K], ∃ (N : Type) (_ : AddCommGroup N) (_ : Module K N) (_ : Module O N)
      (_ : SMulCommClass K O N) (e : K ⊗[R] M ≃ₗ[K] N),
      (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) ∧
      letI : Module (K ⊗[ℤ] O) N := TensorProduct.Algebra.module
      Module.Invertible (K ⊗[ℤ] O) N) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    Module.Invertible (R ⊗[ℤ] O) M := by
  intro R O _ _ _ _ M _ _ _ _ _ _ hK
  let b := Module.Free.chooseBasis ℤ O
  refine GlobalTheory.T.locally_free_of_maximal_ideal_generator R O _ b M fun p hp => ?_
  obtain ⟨N, _, _, _, _, e, he, hinv⟩ := hK p.ResidueField
  obtain ⟨m, hm⟩ := GlobalTheory.T.module_action_fraction_field R O _ b M p.ResidueField
    (residueField_exists_algebraMap_mul_eq R p) N e he hinv
  obtain ⟨g, hg, h1, h2⟩ := GlobalTheory.T.exists_local_generators_residue_basis R M _ (fun i => b i • m) p hm
  exact ⟨g, hg, m, h1, h2⟩

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_action_of_field_fibres : ∀ (R O : Type) [CommRing R] [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] (M : Type)
    [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M] [Module.Finite R M] [Module.Projective R M],
    (∀ (K : Type) [Field K] [Algebra R K], ∃ (N : Type) (_ : AddCommGroup N) (_ : Module K N) (_ : Module O N)
      (_ : SMulCommClass K O N) (e : K ⊗[R] M ≃ₗ[K] N),
      (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) ∧
      letI : Module (K ⊗[ℤ] O) N := TensorProduct.Algebra.module
      Module.Invertible (K ⊗[ℤ] O) N) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    Module.Invertible (R ⊗[ℤ] O) M := by
  atlas_forward_decl GlobalTheory.invertible_of_fibres_invertible
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

open GlobalTheory.CechPic

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem exists_isPullBy {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) :
    ∃ (X' : Obj F 𝔠 S') (φ : X'.A.left ⟶ X.A.left), X'.IsPullBy X b φ := by
  letI : GrpObj ((Over.pullback b).obj X.A) := Functor.grpObjObj
  haveI : IsCommMonObj ((Over.pullback b).obj X.A) := Functor.isCommMonObj_obj
  have hg : IsGrpPullback ((Over.pullback b).obj X.A) X.A b (pullback.fst X.A.hom b) := isGrpPullback_pullback X.A b
  obtain ⟨rm', hrm'⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback X.rm hg
  let A' := (Over.pullback b).obj X.A
  let φ₂ : (G2 A').left ⟶ (G2 X.A).left := (lift (pushPt hg.1.w (fst A' A')) (pushPt hg.1.w (snd A' A'))).left
  have hsq : IsSquare (pullback.fst X.A.hom b) φ₂ := by
    constructor
    · change (lift (pushPt hg.1.w (fst A' A')) (pushPt hg.1.w (snd A' A')) ≫ fst X.A X.A).left = _
      rw [lift_fst]; rfl
    · change (lift (pushPt hg.1.w (fst A' A')) (pushPt hg.1.w (snd A' A')) ≫ snd X.A X.A).left = _
      rw [lift_snd]; rfl
  refine ⟨{ A := A'
            ab := GlobalTheory.isAbelianScheme_pullback_obj b X.A X.ab
            dim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hg.1 X.dim
            rm := rm'
            P := fun c ↦ (X.P c).pull φ₂
            isLB := fun c ↦ pull_isLB (X.isLB c) _
            rig₁ := fun c ↦ (GlobalTheory.T.pullback_square_diagonal_sections_generated X b A' _ hg φ₂ hsq c).1
            rig₂ := fun c ↦ (GlobalTheory.T.pullback_square_diagonal_sections_generated X b A' _ hg φ₂ hsq c).2
            symm := fun c ↦ (GlobalTheory.T.pullback_square_action_bundle_iso X b A' _ hg rm' hrm' φ₂ hsq c c 1).1
            add := fun c c' ↦ (GlobalTheory.T.pullback_square_action_bundle_iso X b A' _ hg rm' hrm' φ₂ hsq c c' 1).2.1
            smul := fun a c ↦ (GlobalTheory.T.pullback_square_action_bundle_iso X b A' _ hg rm' hrm' φ₂ hsq c c a).2.2
            pos := GlobalTheory.T.pullback_square_diagonal_rel_ample X b A' _ hg φ₂ hsq
            ker := GlobalTheory.T.pullback_square_action_sections_generated X b A' _ hg rm' hrm' φ₂ hsq }, pullback.fst X.A.hom b, ⟨hg, hrm', φ₂, hsq, fun c ↦ ?_⟩⟩
  exact (cls_eq_iff (pull_isLB (X.isLB c) φ₂) (pull_isLB (X.isLB c) φ₂)).1 rfl

theorem IsPullBy.comp {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
    {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    (h' : X''.IsPullBy X' b' ψ) (h : X'.IsPullBy X b φ) : X''.IsPullBy X (b' ≫ b) (ψ ≫ φ) :=
  GlobalTheory.T.isPullBy_comp' h' h

theorem IsPullBy.cancel {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
    {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {χ : X''.A.left ⟶ X.A.left}
    (h : X''.IsPullBy X (b' ≫ b) χ) (h' : X'.IsPullBy X b φ) :
    ∃ ψ : X''.A.left ⟶ X'.A.left, X''.IsPullBy X' b' ψ ∧ ψ ≫ φ = χ :=
  GlobalTheory.T.isPullBy_factor_through h h'

theorem IsPullBy.exists_level {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X b φ) {N : ℕ} (α : X.Level N) :
    ∃ α' : X'.Level N, IsLevelPull α' α b := by
  obtain ⟨α', hα'⟩ := GlobalTheory.T.level_structure_pullback_exists h α
  exact ⟨α', φ, h, hα'⟩

theorem exists_isLevelPull {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {N : ℕ} (α : X.Level N) (b : S' ⟶ S) :
    ∃ (X' : Obj F 𝔠 S') (α' : X'.Level N), IsLevelPull α' α b := by
  obtain ⟨X', φ, h⟩ := exists_isPullBy X b
  obtain ⟨α', hα'⟩ := h.exists_level α
  exact ⟨X', α', hα'⟩

variable {R R' : Type} [CommRing R] [CommRing R']

theorem lieCorr_smul {σ : R →+* R'} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap σ) φ) {v : X.Lie} {v' : X'.Lie} (hv : LieCorr σ φ v v')
    (a : 𝓞 F) : LieCorr σ φ (a • v) (a • v') := by
  change (v'.hom ≫ X'.rm.act a).left ≫ φ = spMap (Chart.dualMapR σ) ≫ (v.hom ≫ X.rm.act a).left
  rw [Over.comp_left, Over.comp_left, Category.assoc, h.act a, ← Category.assoc, hv, Category.assoc]

theorem exists_lieEquiv [Algebra R R'] {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap (algebraMap R R')) φ) :
    ∃ e : R' ⊗[R] X.Lie ≃ₗ[R'] X'.Lie, (∀ v v', LieCorr (algebraMap R R') φ v v' ↔ v' = e (1 ⊗ₜ v)) ∧
      ∀ (a : 𝓞 F) (v : X.Lie), e (1 ⊗ₜ (a • v)) = a • e (1 ⊗ₜ v) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.lie_algebra_base_change_iso (R := R) (R' := R') h
  refine ⟨e, he, fun a v ↦ ?_⟩
  exact ((he _ _).1 (lieCorr_smul h ((he v _).2 rfl) a)).symm

theorem IsPullBy.existsUnique_detGen (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap σ) φ) (δ : X.DetGen) :
    ∃! δ' : X'.DetGen, DetCorr σ φ δ.1 δ'.1 := by
  letI := σ.toAlgebra
  obtain ⟨e, he, -⟩ := exists_lieEquiv (R' := R') h
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank X
  have key : ∀ δ' : X'.DetOmega, DetCorr σ φ δ.1 δ' ↔ ∀ v : Fin (Module.finrank ℚ F) → X.Lie,
      δ' (fun i ↦ e (1 ⊗ₜ v i)) = algebraMap R R' (δ.1 v) := fun δ' ↦ by
    refine ⟨fun H v ↦ H v _ fun i ↦ (he _ _).2 rfl, fun H v v' hv ↦ ?_⟩
    obtain rfl : v' = fun i ↦ e (1 ⊗ₜ v i) := funext fun i ↦ (he _ _).1 (hv i)
    exact H v
  obtain ⟨δ', ⟨hs, hv⟩, hu⟩ := GlobalTheory.T.exists_unique_base_change_volume_form R R' X.Lie X'.Lie e _ δ.1 δ.2
  refine ⟨⟨δ', hs⟩, (key δ').2 hv, fun δ'' hδ'' ↦ Subtype.ext (hu δ''.1 ⟨δ''.2, (key δ''.1).1 hδ''⟩)⟩

theorem invertible_detOmega (X : Obj F 𝔠 (Sp R)) : Module.Invertible R X.DetOmega := by
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank X
  exact GlobalTheory.T.top_exterior_dual_invertible R X.Lie _ hrk

theorem IsPullBy.isRapoport (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap σ) φ) (hX : X.IsRapoport) : X'.IsRapoport := by
  letI := σ.toAlgebra
  obtain ⟨e, -, he⟩ := exists_lieEquiv (R' := R') h
  exact GlobalTheory.T.base_change_module_tensor_action R R' (𝓞 F) X.Lie X'.Lie e he hX

theorem isRapoport_iff (X : Obj F 𝔠 (Sp R)) : X.IsRapoport ↔ X.rapLocus = Set.univ := by
  constructor
  · intro hX
    refine Set.eq_univ_of_forall fun s K _ t _ Y φ hY ↦ ?_
    obtain ⟨σ, rfl⟩ : ∃ σ : R →+* K, spMap σ = t := ⟨(Spec.preimage t).hom, Spec.map_preimage t⟩
    exact hY.isRapoport σ hX
  · intro hX
    obtain ⟨hfin, hproj, -⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank X
    refine GlobalTheory.T.module_action_of_field_fibres R (𝓞 F) X.Lie fun K _ _ ↦ ?_
    obtain ⟨Y, φ, hY⟩ := exists_isPullBy X (spMap (algebraMap R K))
    obtain ⟨x⟩ : Nonempty (Sp K) := inferInstance
    have hYr : Y.IsRapoport := (hX ▸ Set.mem_univ (spMap (algebraMap R K) x) : _ ∈ X.rapLocus) K _ ⟨x, rfl⟩ Y φ hY
    obtain ⟨e, -, he⟩ := exists_lieEquiv (R' := K) hY
    exact ⟨Y.Lie, _, _, _, _, e, he, hYr⟩

theorem pullback_facts :
    (∀ {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S), ∃ (X' : Obj F 𝔠 S') (φ : X'.A.left ⟶ X.A.left),
      X'.IsPullBy X b φ) ∧
    (∀ {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
      {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left},
      X''.IsPullBy X' b' ψ → X'.IsPullBy X b φ → X''.IsPullBy X (b' ≫ b) (ψ ≫ φ)) ∧
    (∀ {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
      {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {χ : X''.A.left ⟶ X.A.left},
      X''.IsPullBy X (b' ≫ b) χ → X'.IsPullBy X b φ →
      ∃ ψ : X''.A.left ⟶ X'.A.left, X''.IsPullBy X' b' ψ ∧ ψ ≫ φ = χ) ∧
    (∀ {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S} {φ : X'.A.left ⟶ X.A.left},
      X'.IsPullBy X b φ → ∀ {N : ℕ} (α : X.Level N), ∃ α' : X'.Level N, IsLevelPull α' α b) ∧
    (∀ {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
      {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X (spMap σ) φ →
      (∀ δ : X.DetGen, ∃! δ' : X'.DetGen, DetCorr σ φ δ.1 δ'.1) ∧ Module.Invertible R X.DetOmega ∧
        (X.IsRapoport → X'.IsRapoport)) ∧
    (∀ {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport ↔ X.rapLocus = Set.univ) :=
  ⟨exists_isPullBy, fun h' h ↦ h'.comp h, fun h h' ↦ h.cancel h', fun h _ α ↦ h.exists_level α,
    fun σ _ _ _ h ↦ ⟨h.existsUnique_detGen σ, invertible_detOmega _, h.isRapoport σ⟩, isRapoport_iff⟩

end GlobalTheory.RealMult.Obj
end
end
