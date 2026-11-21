import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassMulLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsDualPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiadditiveClassEqPoincarePullbackUniqueHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareClassAdditiveInDualVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMumfordClassEqZeroAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfIsFiniteOfDimEqAbelianVarietyHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInverseIsogeny

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

variable {K : Type} [Field K]

theorem pull_lam_av {A : AbVar K} (c : Pic A.X.left) {Y Z : Over (Sp K)} (u : Z ⟶ Y) (x y : Y ⟶ A.X) :
    CechPic.pull u.left (AbVar.lam c x y) = AbVar.lam c (u ≫ x) (u ≫ y) := by
  simp only [AbVar.lam, map_sub, ← pull_comp, ← Over.comp_left, MonObj.comp_mul]

theorem pull_one_eq_zero {A : AbVar K} (c : Pic A.X.left) (Y : Over (Sp K)) :
    CechPic.pull (1 : Y ⟶ A.X).left c = 0 := by
  rw [CategoryTheory.Hom.one_def, Over.comp_left, pull_comp]
  obtain ⟨V, hV, hc⟩ := AbDual.exists_pull_eq_zero (CechPic.pull (η[A.X]).left c) (IsLocalRing.closedPoint K)
  exact AbDual.pull_eq_zero_of_mem V _ (fun z => by
    have : (toUnit Y).left z = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact hV) hc

theorem exists_phi : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left)
    (hP : AbDual.IsDual A.X A'.X P), A'.dim = A.dim → ∀ c : Pic A.X.left, ∃ φ : A ⟶ A',
    AbVar.lam c (fst A.X A.X) (snd A.X A.X) = AbDual.evc hP.isLB (fst A.X A.X) (snd A.X A.X ≫ φ.hom) ∧
      (IsAmpleCls c → IsIsogeny φ) := by
  intro K _ A A' P hP hdim c
  set β : Pic (A.X ⊗ A.X).left := AbVar.lam c (fst A.X A.X) (snd A.X A.X) with hβ
  have hpull : ∀ {Y : Over (Sp K)} (x y : Y ⟶ A.X),
      CechPic.pull (lift x y).left β = AbVar.lam c x y := fun x y => by
    rw [hβ, pull_lam_av, lift_fst, lift_snd]
  have hadd : ∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ A.X),
      CechPic.pull (lift (a * a') t).left β = CechPic.pull (lift a t).left β + CechPic.pull (lift a' t).left β := by
    intro Y a a' t
    rw [hpull, hpull, hpull]
    exact GlobalTheory.T.abelianVarietyMumfordClass_mul_left K A c Y a a' t
  have hnorm : CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ A.X)).left β = 0 := by
    rw [hpull, AbVar.lam, _root_.mul_one, pull_one_eq_zero, sub_self, sub_zero]
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.T.biadditiveClass_eq_poincarePullback_unique_hom K A A' A P hP β hadd hnorm
  refine ⟨ψ, hψ, fun hc => ?_⟩
  have hfin : IsFinite ψ.hom.left := by
    refine (GlobalTheory.T.isFinite_iff_finite_ker' K A A' ψ).2 ?_
    have hF := GlobalTheory.T.finite_mumfordClass_eq_zero_ample K A c hc
    refine Finite.of_injective (β := {x : A.Pt // AbVar.lam c (fst A.X (ptOver K (AlgebraicClosure K)))
      (snd A.X _ ≫ x) = 0}) (fun x => ⟨x.1, ?_⟩) ?_
    · have hx : x.1 ≫ ψ.hom = 1 := by
        have := x.2
        rw [MonoidHom.mem_ker, ptMap_apply] at this
        exact this
      rw [← hpull, hψ, AbDual.pull_evc, lift_fst, lift_snd_assoc, Category.assoc, hx, MonObj.comp_one]
      exact AbDual.evc_one_right hP.isLB hP.zero _
    · intro x y h
      exact Subtype.ext (Subtype.mk.inj h)
  exact ⟨hfin, GlobalTheory.T.surjective_of_isFinite_of_dim_eq_abelianVarietyHom K A A' ψ hdim.symm hfin⟩

end GlobalTheory.AV.AbVar
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_to_dual_of_mumfordClass : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P), A'.dim = A.dim → ∀ c : Pic A.X.left, ∃ φ : A ⟶ A', AbVar.lam c (fst A.X A.X) (snd A.X A.X) = AbDual.evc hP.isLB (fst A.X A.X) (snd A.X A.X ≫ φ.hom) ∧ (IsAmpleCls c → IsIsogeny φ) := by
  first | (exact @GlobalTheory.AV.AbVar.exists_phi) | (exact GlobalTheory.AV.AbVar.exists_phi) | (intros; apply GlobalTheory.AV.AbVar.exists_phi  <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_isAdj : ∀ (K : Type) [Field K] (A B : AbVar K) (c : Pic A.X.left) (d : Pic B.X.left),
    IsAmpleCls c → ∀ f : A ⟶ B, ∃ (n : ℕ) (h : B ⟶ A), 0 < n ∧ IsAdj c d f n h := by
  intro K _ A B c d hc f
  obtain ⟨A', P, ⟨hP, -⟩, hdim⟩ := GlobalTheory.T.abelianVariety_exists_dual_pair K A
  obtain ⟨φ, hφ, hiso⟩ := GlobalTheory.T.exists_hom_to_dual_of_mumfordClass K A A' P hP hdim c
  obtain ⟨n, v, hn, -, -, hvφ⟩ := exists_quasiInverse_isogeny K A A' φ (hiso hc)
  have hadd : ∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ B.X),
      CechPic.pull (lift (a * a') t).left (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) =
      CechPic.pull (lift a t).left (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) +
      CechPic.pull (lift a' t).left (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) := by
    intro Y a a' t
    simp only [lam_eq, CechPic.pull_lam, lift_fst_assoc, lift_snd, MonObj.mul_comp]
    simp only [← lam_eq]
    exact GlobalTheory.T.abelianVarietyMumfordClass_mul_left K B d Y _ _ t
  have hzero : CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ B.X)).left
      (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) = 0 := by
    rw [lam_eq, CechPic.pull_lam, lift_snd, CechPic.lam_one_right]
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.T.biadditiveClass_eq_poincarePullback_unique_hom K A A' B P hP _ hadd hzero
  have hpow : ∀ (Y : Over (Sp K)) (a : Y ⟶ A.X) (b : Y ⟶ A'.X) (m : ℕ),
      AbDual.evc hP.isLB a (b ^ m) = m • AbDual.evc hP.isLB a b := by
    intro Y a b m
    induction m with
    | zero => rw [pow_zero, zero_smul, AbDual.evc_one_right hP.isLB hP.zero a]
    | succ m ih => rw [pow_succ, GlobalTheory.T.poincareClass_additive_in_dual_variable K A A' P hP Y a, ih, succ_nsmul]
  refine ⟨n, ψ ≫ v, hn, ?_⟩
  have e1 := congrArg (CechPic.pull (lift (fst A.X B.X) (snd A.X B.X ≫ (ψ ≫ v).hom)).left) hφ
  rw [lam_eq, CechPic.pull_lam, AbDual.pull_evc, lift_fst, lift_snd_assoc, lift_snd, ← lam_eq] at e1
  unfold IsAdj
  rw [e1]
  simp only [comp_hom, Category.assoc]
  rw [← comp_hom v φ, hvφ, nsmul_hom, id_hom, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, hpow, ← hψ,
    natCast_zsmul]

end GlobalTheory.AV.AbVar
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjoint_up_to_integer : ∀ (K : Type) [Field K] (A B : AbVar K) (c : Pic A.X.left) (d : Pic B.X.left), IsAmpleCls c → ∀ f : A ⟶ B, ∃ (n : ℕ) (h : B ⟶ A), 0 < n ∧ IsAdj c d f n h := by
  first | (exact @GlobalTheory.AV.AbVar.exists_isAdj) | (exact GlobalTheory.AV.AbVar.exists_isAdj) | (intros; apply GlobalTheory.AV.AbVar.exists_isAdj  <;> assumption)
end
