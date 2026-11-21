import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeBundleTrivialGeometricFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedLineBundleTrivialOfTorsionGeometricFibStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_bundle_trivial_geometric_fibre : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).pull (pullback.fst o.A.hom y)).Gen, t.IsGen := by
  first | (exact @GlobalTheory.HeckeFibre.fibre_triv) | (exact GlobalTheory.HeckeFibre.fibre_triv) | (intros; apply GlobalTheory.HeckeFibre.fibre_triv <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPel.HT.Hecke.KerPol
open GlobalTheory.UPel.HT.Hecke

theorem hecke_sections_triv : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (𝟙 o.A) (toUnit o.A ≫ h)).left).Gen, t.IsGen) := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o h hh
  have hfib := GlobalTheory.T.hecke_bundle_trivial_geometric_fibre p D R b g c k N hc hk hN hNp hEF hg hck S s o h hh
  obtain ⟨x, rfl⟩ := hh
  have hP := o.isLB
  have clsPow : ∀ {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) (h' : (GlobalTheory.UPel.HT.Hecke.lbPow L n).IsLB),
      GlobalTheory.CechPic.cls (GlobalTheory.UPel.HT.Hecke.lbPow L n) h' = n • GlobalTheory.CechPic.cls L hL := by
    intro X L hL n h'
    unfold GlobalTheory.UPel.HT.Hecke.lbPow at h' ⊢
    rw [GlobalTheory.CechPic.cls_linComb hL]
    simp [GlobalTheory.CechPic.pull_id]
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb hP _ _
  have hadd := (GlobalTheory.AbDual.additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab hP o.rig₁ o.rig₂).1
  have evcCls : ∀ {M : LB (o.A ⊗ o.A).left} (hM : M.IsLB) {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hM a t = GlobalTheory.CechPic.pull (lift a t).left (GlobalTheory.CechPic.cls M hM) := by
    intro M hM Y a t
    rw [← GlobalTheory.AbDual.cls_ev hM a t (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM]
  have evcQ : ∀ {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hQ a t = (k ^ 2 / c) • GlobalTheory.AbDual.evc hP a t := by
    intro Y a t
    rw [evcCls hQ, evcCls hP, clsPow hP _ hQ, map_nsmul]
  have hpow : ∀ (a : o.A ⟶ o.A) (n : ℕ),
      GlobalTheory.AbDual.evc hP (a ^ n) (𝟙 o.A) = n • GlobalTheory.AbDual.evc hP a (𝟙 o.A) := by
    intro a n
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
    | succ n ih => rw [pow_succ, (GlobalTheory.AbDual.isAdditive_iff hP).1 hadd, ih, succ_nsmul]
  have etaPow : ∀ (n : ℕ) (z : D.La), (o.eta z) ^ n = o.eta (n • z) := by
    intro n z
    induction n with
    | zero => rw [pow_zero, zero_smul, eta_zero]
    | succ n ih => rw [pow_succ, ih, succ_nsmul, o.eta_add]
  set th : o.A ⟶ o.A := toUnit o.A ≫ o.eta (N • g x) with hth
  have hk1 : th ^ k = 1 := by
    rw [hth, ← MonObj.comp_pow, etaPow, smul_smul, show k * N = N * k from mul_comm _ _, o.eta_ker, MonObj.comp_one]
  have htors : k • GlobalTheory.AbDual.evc hP th (𝟙 o.A) = 0 := by
    rw [← hpow, hk1]; exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
  have hQth : GlobalTheory.AbDual.evc hQ th (𝟙 o.A) = 0 := by
    have hM : (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)).IsLB := pull_isLB hQ _
    have hunit : IsUnit ((k : Γ(S, ⊤))) := by
      have hR := b.unit k hk
      have e := hR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      have e2 := e.map (s.appTop.hom)
      simpa using e2
    have hrig : ∃ t : ((GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)).pull
        (1 : 𝟙_ (Over S) ⟶ o.A).left).Gen, t.IsGen := by
      rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM, GlobalTheory.AbDual.cls_ev hQ,
        GlobalTheory.AbDual.pull_evc, evcQ, Category.comp_id, GlobalTheory.AbDual.evc_one_right hP o.rig₂, smul_zero]
    have hpowM : ∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)) k).Gen, t.IsGen := by
      have hMk : (GlobalTheory.UPel.HT.Hecke.lbPow (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)) k).IsLB :=
        LB.isLB_linComb hM _ _
      refine (GlobalTheory.CechPic.cls_eq_zero_iff hMk).1 ?_
      rw [clsPow hM k hMk, GlobalTheory.AbDual.cls_ev hQ, evcQ,
        smul_comm, htors, smul_zero]
    obtain ⟨t, ht⟩ := GlobalTheory.T.rigidified_lineBundle_trivial_of_torsion_geometricFibres S o.A o.ab _ hM hrig k hunit hpowM hfib
    exact (GlobalTheory.AbDual.triv_ev_iff hQ _ _).1 ⟨t, ht⟩
  have hsw : GlobalTheory.CechPic.cls o.P hP = GlobalTheory.CechPic.cls (GlobalTheory.AbDual.swap o.P) (pull_isLB hP _) :=
    (GlobalTheory.CechPic.cls_eq_iff _ _).2 o.symm
  refine ⟨(GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 hQth, (GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 ?_⟩
  rw [evcQ, evcCls hP, hsw, ← evcCls (pull_isLB hP _), GlobalTheory.AbDual.evc_swap hP, ← evcQ]
  exact hQth

end GlobalTheory.UPel.HT.Hecke.KerPol
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeSections_linearSimilitude_mem_kernel_polarisation : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (𝟙 o.A) (toUnit o.A ≫ h)).left).Gen, t.IsGen) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.KerPol.hecke_sections_triv) | (exact GlobalTheory.UPel.HT.Hecke.KerPol.hecke_sections_triv) | (intros; apply GlobalTheory.UPel.HT.Hecke.KerPol.hecke_sections_triv <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeWeilLift

open GlobalTheory.CechPic

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB (A ⊗ A).left} (hL : L.IsLB)

def qc {T : Over S} (a b : T ⟶ A) : Pic T.left := pull (lift a b).left (cls L hL)

theorem pull_eq_qc {T : Over S} (f : T ⟶ A ⊗ A) :
    pull f.left (cls L hL) = qc hL (f ≫ fst A A) (f ≫ snd A A) := by
  unfold qc; rw [lift_comp_fst_snd]

omit [IsCommMonObj A] in
theorem translPt_fst {T : Over S} (x : T ⟶ A ⊗ A) :
    Out.translPt (A ⊗ A) x ≫ fst A A = (fst T (A ⊗ A) ≫ x ≫ fst A A) * (snd T (A ⊗ A) ≫ fst A A) := by
  have e : Out.translPt (A ⊗ A) x = (fst T (A ⊗ A) ≫ x) * snd T (A ⊗ A) := rfl
  rw [e, MonObj.mul_comp, Category.assoc]

omit [IsCommMonObj A] in
theorem translPt_snd {T : Over S} (x : T ⟶ A ⊗ A) :
    Out.translPt (A ⊗ A) x ≫ snd A A = (fst T (A ⊗ A) ≫ x ≫ snd A A) * (snd T (A ⊗ A) ≫ snd A A) := by
  have e : Out.translPt (A ⊗ A) x = (fst T (A ⊗ A) ≫ x) * snd T (A ⊗ A) := rfl
  rw [e, MonObj.mul_comp, Category.assoc]

variable {hL}

include hL in

theorem exists_theta_left
    (hB : ∀ (T : Over S) (x x' y : T ⟶ A), qc hL (x * x') y = qc hL x y + qc hL x' y)
    {T : Over S} (t : T ⟶ 𝟙_ (Over S)) (h : 𝟙_ (Over S) ⟶ A)
    (ht : ∃ u : (L.pull (lift (toUnit A ≫ h) (𝟙 A)).left).Gen, u.IsGen) :
    ∃ θ : Out.ThetaGrp (A ⊗ A) L 1 T, θ.pt = t ≫ lift h 1 := by
  have z : pull (lift (toUnit A ≫ h) (𝟙 A)).left (cls L hL) = 0 := by
    rw [← cls_pull hL _ (pull_isLB hL _)]; exact (cls_eq_zero_iff _).2 ht
  set b := snd T (A ⊗ A) ≫ snd A A
  have e1 : fst T (A ⊗ A) ≫ (t ≫ lift h 1) ≫ fst A A = b ≫ toUnit A ≫ h := by
    rw [Category.assoc, lift_fst, ← Category.assoc, ← Category.assoc,
      toUnit_unique (fst T (A ⊗ A) ≫ t) (b ≫ toUnit A)]
  have e2 : fst T (A ⊗ A) ≫ (t ≫ lift h 1) ≫ snd A A = 1 := by
    rw [Category.assoc, lift_snd, MonObj.comp_one, MonObj.comp_one]
  have e3 : qc hL (b ≫ toUnit A ≫ h) b = 0 := by
    unfold qc
    rw [show lift (b ≫ toUnit A ≫ h) b = b ≫ lift (toUnit A ≫ h) (𝟙 A) by
      rw [comp_lift, Category.comp_id], Over.comp_left, pull_comp, z, map_zero]
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (Out.thetaLB (A ⊗ A) L 1 (t ≫ lift h 1)), u.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
    rw [cls_linComb hL, Fin.sum_univ_two]
    show (1 : ℤ) • pull (snd T (A ⊗ A)).left _ + (-1 : ℤ) • pull (Out.translPt (A ⊗ A) (t ≫ lift h 1)).left _ = 0
    rw [pull_eq_qc, pull_eq_qc, translPt_fst, translPt_snd, e1, e2, _root_.one_mul, hB, e3]
    simp
  exact ⟨⟨_, u, hu⟩, rfl⟩

include hL in

theorem exists_theta_right
    (hB' : ∀ (T : Over S) (x y y' : T ⟶ A), qc hL x (y * y') = qc hL x y + qc hL x y')
    {T : Over S} (t : T ⟶ 𝟙_ (Over S)) (h : 𝟙_ (Over S) ⟶ A)
    (ht : ∃ u : (L.pull (lift (𝟙 A) (toUnit A ≫ h)).left).Gen, u.IsGen) :
    ∃ θ : Out.ThetaGrp (A ⊗ A) L 1 T, θ.pt = t ≫ lift 1 h := by
  have z : pull (lift (𝟙 A) (toUnit A ≫ h)).left (cls L hL) = 0 := by
    rw [← cls_pull hL _ (pull_isLB hL _)]; exact (cls_eq_zero_iff _).2 ht
  set a := snd T (A ⊗ A) ≫ fst A A
  have e1 : fst T (A ⊗ A) ≫ (t ≫ lift 1 h) ≫ snd A A = a ≫ toUnit A ≫ h := by
    rw [Category.assoc, lift_snd, ← Category.assoc, ← Category.assoc,
      toUnit_unique (fst T (A ⊗ A) ≫ t) (a ≫ toUnit A)]
  have e2 : fst T (A ⊗ A) ≫ (t ≫ lift 1 h) ≫ fst A A = 1 := by
    rw [Category.assoc, lift_fst, MonObj.comp_one, MonObj.comp_one]
  have e3 : qc hL a (a ≫ toUnit A ≫ h) = 0 := by
    unfold qc
    rw [show lift a (a ≫ toUnit A ≫ h) = a ≫ lift (𝟙 A) (toUnit A ≫ h) by
      rw [comp_lift, Category.comp_id], Over.comp_left, pull_comp, z, map_zero]
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (Out.thetaLB (A ⊗ A) L 1 (t ≫ lift 1 h)), u.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
    rw [cls_linComb hL, Fin.sum_univ_two]
    show (1 : ℤ) • pull (snd T (A ⊗ A)).left _ + (-1 : ℤ) • pull (Out.translPt (A ⊗ A) (t ≫ lift 1 h)).left _ = 0
    rw [pull_eq_qc, pull_eq_qc, translPt_fst, translPt_snd, e1, e2, _root_.one_mul, hB', e3]
    simp
  exact ⟨⟨_, u, hu⟩, rfl⟩

end General

end GlobalTheory.HeckeWeilLift

namespace GlobalTheory.HeckeWeilLift

open GlobalTheory.CechPic GlobalTheory.DiagPairing

theorem exists_weilIs_hecke : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∃ u : Γ((𝟙_ (Over S)).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) u := by
  intro p _ D R _ b g c k N hc hk hN hNp hsim hsurj hdiv S s o h₁ hh₁ h₂ hh₂
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ o.A), pc o.isLB (x * x') y = pc o.isLB x y + pc o.isLB x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), pc o.isLB x (y * y') = pc o.isLB x y + pc o.isLB x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hcls : cls _ hQ = (k ^ 2 / c) • cls o.P o.isLB := by
    refine (cls_linComb o.isLB (K := Fin (k ^ 2 / c)) (fun _ => 𝟙 _) (fun _ => 1) hQ).trans ?_
    simp [pull_id]
  have hQB : ∀ (T : Over S) (x x' y : T ⟶ o.A), qc hQ (x * x') y = qc hQ x y + qc hQ x' y :=
    fun T x x' y => by
      unfold qc
      rw [hcls, map_nsmul, map_nsmul, map_nsmul]
      exact (congrArg _ (hB T x x' y)).trans (smul_add _ _ _)
  have hQB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), qc hQ x (y * y') = qc hQ x y + qc hQ x y' :=
    fun T x y y' => by
      unfold qc
      rw [hcls, map_nsmul, map_nsmul, map_nsmul]
      exact (congrArg _ (hB' T x y y')).trans (smul_add _ _ _)
  obtain ⟨t₁, -⟩ := GlobalTheory.T.heckeSections_linearSimilitude_mem_kernel_polarisation p D R b g c k N hc hk hN hNp hsim hsurj hdiv S s o h₁ hh₁
  obtain ⟨-, t₂⟩ := GlobalTheory.T.heckeSections_linearSimilitude_mem_kernel_polarisation p D R b g c k N hc hk hN hNp hsim hsurj hdiv S s o h₂ hh₂
  have hA2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  exact CommutatorPairing.exists_weilIs hG hA2 hQ
    (fun _ => ⟨⊤, trivial, exists_theta_left hQB (Out.overResι ⊤) h₁ t₁⟩)
    (fun _ => ⟨⊤, trivial, exists_theta_right hQB' (Out.overResι ⊤) h₂ t₂⟩)

end GlobalTheory.HeckeWeilLift
end
end
