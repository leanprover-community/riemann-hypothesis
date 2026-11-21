import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIsPerfectOfAdditive

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.Model

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem fam_ev {U T : Over S} {M : LB (A ⊗ U).left} (h : Fam A M) (u : T ⟶ U) :
    Fam A (ev M (fst A T) (snd A T ≫ u)) := by
  have hM : (ev M (fst A T) (snd A T ≫ u)).IsLB := pull_isLB h.isLB _
  refine ⟨hM, (isAdditive_iff hM).2 fun Y a a' t ↦ ?_⟩
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add Y a a' _

theorem rep_ext {B S' Y : Over S} {b : B ⟶ S'} {P : LB (A ⊗ B).left} (h : Rep A b P) {u u' : Y ⟶ B}
    (hb : u ≫ b = u' ≫ b) (e : Same A P P u u') : u = u' := by
  have hu := fam_ev h.fam u
  exact (h.univ Y (u ≫ b) _ hu).unique ⟨rfl, (cls_eq_iff hu.isLB hu.isLB).1 rfl⟩ ⟨hb.symm, e⟩

theorem isChart_of_rep {B : Over S} {P : LB (A ⊗ B).left} (h : Rep A (toUnit B) P) : IsChart A P where
  fam := h.fam
  inj _ _ _ e := rep_ext h (toUnit_unique _ _) e
  chart T N hN := ⟨⊤, fun Y y ↦ ⟨fun _ _ ↦ trivial, fun _ ↦ by
    obtain ⟨x, hx, -⟩ := h.univ Y (toUnit Y) _ (fam_ev hN y)
    exact ⟨x, hx.2⟩⟩⟩

theorem rep_baseChange {B : Over S} {P : LB (A ⊗ B).left} (h : Rep A (toUnit B) P) (S' : Over S) :
    Rep A (snd B S') (ev P (fst A _) (snd A _ ≫ fst B S')) where
  fam := fam_ev h.fam _
  univ T t N hN := by
    have hQ := (fam_ev h.fam (fst B S')).isLB
    have key : ∀ y : T ⟶ B ⊗ S', LBIso N (ev (ev P (fst A _) (snd A _ ≫ fst B S')) (fst A T) (snd A T ≫ y)) ↔
        LBIso N (ev P (fst A T) (snd A T ≫ y ≫ fst B S')) := fun y ↦ by
      rw [← cls_eq_iff hN.isLB (pull_isLB hQ _), ← cls_eq_iff hN.isLB (pull_isLB h.fam.isLB _), cls_ev hQ,
        cls_ev h.fam.isLB, evc_ev h.fam.isLB, lift_fst, lift_snd_assoc, Category.assoc]
    obtain ⟨x, hx, hu⟩ := h.univ T (toUnit T) N hN
    refine ⟨lift x t, ⟨lift_snd _ _, (key _).2 (by rw [lift_fst]; exact hx.2)⟩, fun y hy ↦ ?_⟩
    ext1
    · rw [lift_fst]
      exact hu _ ⟨toUnit_unique _ _, (key y).1 hy.2⟩
    · rw [lift_snd, hy.1]







theorem inj_of_isPerfect {B : Over S} [GrpObj B] {P : LB (A ⊗ B).left} (h : IsPerfect A B P)
    (ha : IsAdditive (swap P)) : Inj A P := fun Y u u' e ↦ by
  have hs : (swap P).IsLB := pull_isLB h.isLB _
  have e' := (same_iff h.isLB h.isLB _ _).1 e
  have a := (isAdditive_iff hs).1 ha _ (snd A Y ≫ (u * u'⁻¹)) (snd A Y ≫ u') (fst A Y)
  rw [← MonObj.comp_mul, inv_mul_cancel_right, evc_swap h.isLB, evc_swap h.isLB, evc_swap h.isLB, e'] at a
  have t := h.ker_right Y (u * u'⁻¹) ((triv_ev_iff h.isLB _ _).2 (right_eq_add.1 a))
  rwa [mul_inv_eq_one] at t

omit [GrpObj A] in

theorem fibInj_of_inj {U : Over S} {M : LB (A ⊗ U).left} (h : Inj A M) : FibInj A M :=
  fun _ _ _ _ Y _ u u' e ↦ h Y u u' e

omit [GrpObj A] in

theorem eq_of_inj_triv {U Y : Over S} (h : Inj A (LB.triv (A ⊗ U).left)) (u u' : Y ⟶ U) : u = u' :=
  h Y u u' ((same_iff (LB.isLB_triv _) (LB.isLB_triv _) _ _).2 ((map_zero _).trans (map_zero _).symm))

omit [GrpObj A] in

theorem dimLe_self : DimLe A A := fun _ _ _ h ↦ h

theorem ell {R : Type} [CommRing R] [IsNoetherianRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    haveI := (WeierstrassCurve.ellPolAV W).isAb.comm
    Fam (WeierstrassCurve.ellPolAV W).A (abelian₂ _ (WeierstrassCurve.ellPolAV W).L) ∧
      Inj (WeierstrassCurve.ellPolAV W).A (abelian₂ _ (WeierstrassCurve.ellPolAV W).L) ∧
      Good 1 (WeierstrassCurve.ellPolAV W).A.hom := by
  have hA := (WeierstrassCurve.ellPolAV W).isAb
  have h := isPerfect_ell W
  exact ⟨⟨h.isLB, CubeNoeth.isAdditive_of_triv_axes hA hA h.isLB h.zero_left h.zero_right⟩,
    inj_of_isPerfect h (CubeNoeth.isAdditive_swap_of_triv_axes hA hA h.isLB h.zero_left h.zero_right),
    hA.proper, (WeierstrassCurve.ellPolAV W).smoothDim, hA.geomConnected⟩







end GlobalTheory.DualCon.Model
