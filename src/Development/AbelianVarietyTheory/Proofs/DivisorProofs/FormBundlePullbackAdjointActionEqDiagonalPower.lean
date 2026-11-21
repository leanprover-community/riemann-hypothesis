import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBiextensionHypPullbackOfGroupPullback

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CasimirPull

open GlobalTheory.CechPic

theorem main : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∀ (act : O → (A ⟶ A)), IsRAct A act → Adj A Q bar act → ∀ (G : Over S) [GrpObj G] (pr : Fin r → (G ⟶ A)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin r → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → ∀ Φ : A ⟶ G, (∀ u, Φ ≫ pr u = act (e u)) → LBIso ((LB.LinComb Q (K := Fin r × Fin r) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)).pull Φ.left) (LB.LinComb Q (K := Fin 1) (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => (d : ℤ))) := by
  intro S A _ _ Q hA hQ h₁ h₂ _ hamp O _ bar r e W d _ _ _ _ hsum act hact hadj G _ pr _ _ Φ hΦ
  have hbi := GlobalTheory.Biadditive.biadditive_of_triv_axes GlobalTheory.globalFns_holds S A
    (Q.pull (lift (𝟙 A) (𝟙 A)).left) hA (pull_isLB hQ _) hamp Q hQ h₁ h₂

  have add2 : ∀ (T : Over S) (y x x' : T ⟶ A), pull (lift y (x * x')).left (cls Q hQ) =
      pull (lift y x).left (cls Q hQ) + pull (lift y x').left (cls Q hQ) := by
    intro T y x x'
    have z := (cls_eq_zero_iff (LB.isLB_linComb hQ _ _)).2 (hbi T x x' y).2
    rw [cls_linComb hQ, Fin.sum_univ_three] at z
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
    rw [← sub_eq_zero, ← z]
    abel

  have adjB : ∀ (T : Over S) (x y : T ⟶ A) (a : O), pull (lift (x ≫ act a) y).left (cls Q hQ) =
      pull (lift x (y ≫ act (bar a))).left (cls Q hQ) := by
    intro T x y a
    have h := (cls_eq_iff (pull_isLB hQ _) (pull_isLB hQ _)).2 (hadj a)
    rw [cls_pull hQ, cls_pull hQ] at h
    have k₁ : (lift x y).left ≫ (lift (fst A A ≫ act a) (snd A A)).left = (lift (x ≫ act a) y).left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd]
    have k₂ : (lift x y).left ≫ (lift (fst A A) (snd A A ≫ act (bar a))).left = (lift x (y ≫ act (bar a))).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
    rw [← k₁, ← k₂, pull_comp, pull_comp, h]
  let f : O →+ Pic A.left := AddMonoidHom.mk' (fun a => pull (lift (𝟙 A) (act a)).left (cls Q hQ))
    (fun a b => by simp only [hact.2.2.2 a b]; exact add2 A (𝟙 A) _ _)
  have term : ∀ i j : Fin r, pull Φ.left (pull (lift (pr i) (pr j)).left (cls Q hQ)) =
      f (e j * bar (e i)) := by
    intro i j
    rw [← pull_comp, ← Over.comp_left, comp_lift, hΦ, hΦ]
    have := adjB A (𝟙 A) (act (e j)) (e i)
    rw [Category.id_comp] at this
    rw [this, ← hact.2.2.1]
    rfl
  refine (cls_eq_iff (pull_isLB (LB.isLB_linComb hQ _ _) _) (LB.isLB_linComb hQ _ _)).1 ?_
  rw [cls_pull (LB.isLB_linComb hQ _ _), cls_linComb hQ, cls_linComb hQ, map_sum, Fin.sum_univ_one]
  simp only [map_zsmul, term]
  rw [Fintype.sum_prod_type]
  simp only [← map_zsmul, ← map_sum, hsum]
  rw [← nsmul_one, map_nsmul, natCast_zsmul]
  rw [map_nsmul]
  show d • pull (lift (𝟙 A) (act 1)).left (cls Q hQ) = _
  rw [hact.2.1]

end GlobalTheory.CasimirPull
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ElRep

theorem sq_ext {S : Scheme.{0}} (A : Over S) {X : Scheme.{0}} (f g : X ⟶ (A ⊗ A).left)
    (h₁ : f ≫ (fst A A).left = g ≫ (fst A A).left) (h₂ : f ≫ (snd A A).left = g ≫ (snd A A).left) : f = g :=
  pullback.hom_ext h₁ h₂

theorem main : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (B' : Over T) [GrpObj B'] (φB : B'.left ⟶ (Out.powObj A r).left) (pr' : Fin r → (B' ⟶ A')), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → IsGrpPullback B' (Out.powObj A r) t φB → (∀ u, IsMonHom (pr' u)) → (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ (act : O → (A' ⟶ A')), IsRAct A' act → Adj A' (Q.pull φ₂') bar act → ∀ Φ : A' ⟶ B', (∀ u, Φ ≫ pr' u = act (e u)) → LBIso ((diagPow A Q d).pull φ') (((formLB A Q (Out.powPr A (n := r)) W).pull φB).pull Φ.left) := by
  intro S A _ _ Q hQ O _ bar r e W d hbar hspan hW hd hsum T t A' _ _ φ' φ₂' B' _ φB pr' hApb hsq hBpb hpr' hprφ
    huniq act hact hadj Φ hΦ
  have hQ' : QHyp A' (Q.pull φ₂') := GlobalTheory.T.symmetricBiextensionHyp_pullback_of_groupPullback S T t A A' φ' φ₂' Q hApb hsq hQ
  obtain ⟨hA', hL', g₁, g₂, hsym', hamp'⟩ := hQ'
  have C := GlobalTheory.CasimirPull.main T A' (Q.pull φ₂') hA' hL' g₁ g₂ hsym' hamp' O bar r e W d hbar hspan hW hd hsum
    act hact hadj B' pr' hpr' huniq Φ hΦ
  have hQL : Q.IsLB := hQ.2.1
  have e₁ : ∀ u v : Fin r, (lift (pr' u) (pr' v)).left ≫ φ₂' =
      φB ≫ (lift (Out.powPr A (n := r) u) (Out.powPr A (n := r) v)).left := fun u v => by
    apply sq_ext A
    · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, hprφ, Category.assoc,
        ← Over.comp_left, lift_fst]
    · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, hprφ, Category.assoc,
        ← Over.comp_left, lift_snd]
  have e₂ : (lift (𝟙 A') (𝟙 A')).left ≫ φ₂' = φ' ≫ (lift (𝟙 A) (𝟙 A)).left := by
    apply sq_ext A
    · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.id_comp,
        Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id]
    · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp,
        Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.comp_id]
  have C' := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB (LB.isLB_linComb hL' _ _) _) (LB.isLB_linComb hL' _ _)).2 C
  rw [GlobalTheory.CechPic.cls_pull (LB.isLB_linComb hL' _ _), GlobalTheory.CechPic.cls_linComb hL', GlobalTheory.CechPic.cls_linComb hL',
    GlobalTheory.CechPic.cls_pull hQL] at C'
  simp only [map_sum, map_zsmul, ← GlobalTheory.CechPic.pull_comp, Category.assoc, e₁, e₂] at C'
  unfold diagPow formLB
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB (LB.isLB_linComb hQL _ _) _)
    (pull_isLB (pull_isLB (LB.isLB_linComb hQL _ _) _) _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull (LB.isLB_linComb hQL _ _), GlobalTheory.CechPic.cls_pull (pull_isLB (LB.isLB_linComb hQL _ _) _),
    GlobalTheory.CechPic.cls_pull (LB.isLB_linComb hQL _ _), GlobalTheory.CechPic.cls_linComb hQL, GlobalTheory.CechPic.cls_linComb hQL]
  simp only [map_sum, map_zsmul, ← GlobalTheory.CechPic.pull_comp, Category.assoc]
  exact C'.symm

end GlobalTheory.ElRep
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formBundle_pullback_adjointAction_eq_diagonalPower : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (B' : Over T) [GrpObj B'] (φB : B'.left ⟶ (Out.powObj A r).left) (pr' : Fin r → (B' ⟶ A')), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → IsGrpPullback B' (Out.powObj A r) t φB → (∀ u, IsMonHom (pr' u)) → (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ (act : O → (A' ⟶ A')), IsRAct A' act → Adj A' (Q.pull φ₂') bar act → ∀ Φ : A' ⟶ B', (∀ u, Φ ≫ pr' u = act (e u)) → LBIso ((diagPow A Q d).pull φ') (((formLB A Q (Out.powPr A (n := r)) W).pull φB).pull Φ.left) := by
  atlas_forward_decl GlobalTheory.ElRep.main
end
