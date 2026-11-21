import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsDeRhamPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationLiftDeterminesModFilStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationLiftDeterminesModFil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompOfIsFilLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRealiseKodairaSpencerDirectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorKodairaSpencerDirectionsDimStatement

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTSkew

set_option maxHeartbeats 1000000 in

theorem skew_of_isFilLift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (φ : LinearMap.BilinForm k (HdR o₀.A)), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, ∀ y ∈ Fil o₀.A, ∀ x' y' : HdR o₀.A, IsFilLift m'.cart x x' → IsFilLift m'.cart y y' → φ x' y + φ x y' = 0 := by
  intro p _ D R _ b N k _ t o₀ φ hφ o' m' x _ y _ x₁ y₁ hx hy
  have HR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have HD : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  obtain ⟨g', hg'⟩ := GlobalTheory.KSGraph.exists_dim o'.A o'.ab
  obtain ⟨l₁, l₂⟩ := m'.sq
  have C : GlobalTheory.AbDual.CupSquare (epsDP k) (GlobalTheory.DeRham.epsRed k) (o₀.A ⊗ o₀.A) :=
    GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod HR.1 HD.2 (isDPNilpotent_squareZero (SqExt.dual k).sq)
    GlobalTheory.KSBijection.fst_surj rfl o'.ab hg' o'.ab hg' m'.cart m'.cart
  have iso : LBIso (o₀.P.pull (Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A)))) o₀.P :=
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB o₀.isLB _) o₀.isLB).1
      (by rw [GlobalTheory.CechPic.cls_pull o₀.isLB, Over.id_left, GlobalTheory.CechPic.pull_id])
  obtain ⟨φ', hφ', e'⟩ := hφ.pull o₀.isLB (constMor o₀.A) (constMor o₀.A)
    (h := Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A))) (by simp) (by simp) o₀.isLB iso
  have van := GlobalTheory.BirigidLift.vanish_of_lift HR o'.ab hg' o'.ab hg' m'.cart m'.cart l₁ l₂ C o'.isLB o'.rig₁
    o'.rig₂ o₀.isLB (LBIso.symm m'.pol) hφ'
  have hm := GlobalTheory.HTRealise.isBC_constMor o₀.ab
  obtain ⟨xc, hxc⟩ := hm.exists x
  obtain ⟨yc, hyc⟩ := hm.exists y
  obtain ⟨x₁c, hx₁c⟩ := hm.exists x₁
  obtain ⟨y₁c, hy₁c⟩ := hm.exists y₁
  obtain ⟨d, hd, ed⟩ := hx
  obtain ⟨d', hd', ed'⟩ := hy
  have dx : d = xc + (DualNumber.eps : DualNumber k) • x₁c := GlobalTheory.HTRealise.crys_ext o₀.ab fun c ↦ by
    rw [ed c, LinearMap.add_apply, LinearMap.smul_apply, hxc c, hx₁c c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have dy : d' = yc + (DualNumber.eps : DualNumber k) • y₁c := GlobalTheory.HTRealise.crys_ext o₀.ab fun c ↦ by
    rw [ed' c, LinearMap.add_apply, LinearMap.smul_apply, hyc c, hy₁c c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have z : φ' d d' = 0 := van d hd d' hd'
  rw [dx, dy] at z
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    e' _ _ _ _ hxc hyc, e' _ _ _ _ hx₁c hyc, e' _ _ _ _ hxc hy₁c, e' _ _ _ _ hx₁c hy₁c] at z
  have z2 := congrArg TrivSqZeroExt.snd z
  simp [TrivSqZeroExt.algebraMap_eq_inl] at z2
  linear_combination z2

end GlobalTheory.HTSkew
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_firstOrder_deformation_skew : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (φ : LinearMap.BilinForm k (HdR o₀.A)), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, ∀ y ∈ Fil o₀.A, ∀ x' y' : HdR o₀.A, IsFilLift m'.cart x x' → IsFilLift m'.cart y y' → φ x' y + φ x y' = 0 := by
  first | (exact @GlobalTheory.HTSkew.skew_of_isFilLift) | (exact GlobalTheory.HTSkew.skew_of_isFilLift) | (intros; apply GlobalTheory.HTSkew.skew_of_isFilLift  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTCount.LieZFil

theorem omega_sq {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) :
    D.ω * D.ω = (D.tr : 𝓞 D.F) * D.ω - (D.nm : 𝓞 D.F) := by
  rw [← D.tr_eq, ← D.nm_eq]; ring

theorem end_sq {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {C H : Type*} [CommRing C] [AddCommGroup H]
    [Module C H] (act : D.O →+* Module.End C H) (h : H) :
    act (algebraMap (𝓞 D.F) D.O D.ω) (act (algebraMap (𝓞 D.F) D.O D.ω) h) =
      (D.tr : C) • act (algebraMap (𝓞 D.F) D.O D.ω) h - (D.nm : C) • h := by
  have e := congrArg (fun x => act (algebraMap (𝓞 D.F) D.O x) h) (omega_sq D)
  simp only [map_mul, map_sub, map_intCast, Module.End.mul_apply, LinearMap.sub_apply] at e
  rw [e]
  simp [Module.End.intCast_apply, Int.cast_smul_eq_zsmul]

theorem rho_part_eig {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {C H : Type*} [CommRing C] [AddCommGroup H]
    [Module C H] (act : D.O →+* Module.End C H) (ρ : C) (hρ : ρ ^ 2 - D.tr * ρ + D.nm = 0) (y : H) :
    act (algebraMap (𝓞 D.F) D.O D.ω) ((act (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : C) - ρ) • 1) y) -
      ρ • ((act (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : C) - ρ) • 1) y) = 0 := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, end_sq]
  have hn : (D.nm : C) = ρ * (D.tr - ρ) := by linear_combination hρ
  rw [hn]
  module

theorem sum_mem_fil {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    {b : GlobalTheory.UPel.HT.Base D R} {N : ℕ} {C : Type} [CommRing C] [IsLocalRing C] (β : R →+* C)
    {s : Sp C ⟶ Sp R} (hs : s = spMap β) (o : GlobalTheory.UPel.HT.Obj b N s) {r : ℕ} (lam : Fin r → C)
    (c : Fin r → 𝓞 D.F) (hlam : ∀ i, ∑ l, lam l * β (b.t i (c l)) = 0) (y : HdR o.A) :
    ∑ l, lam l • GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act (algebraMap (𝓞 D.F) D.O (c l))
      ((GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act (algebraMap (𝓞 D.F) D.O D.ω) -
        ((D.tr : C) - β b.ρ) • 1) y) ∈ Fil o.A := by
  set act := GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act with hact
  set u := (act (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : C) - β b.ρ) • 1) y with hu
  have hfil : ∀ (x : D.O) {h : HdR o.A}, h ∈ Fil o.A → act x h ∈ Fil o.A := fun x h hh => by
    haveI := o.act.hom x
    exact push_mem_Fil (o.act.act x) hh
  have hρ : β b.ρ ^ 2 - D.tr * β b.ρ + D.nm = 0 := by
    have := congrArg β b.ρ_root
    simpa using this
  have hω : act (algebraMap (𝓞 D.F) D.O D.ω) u - β b.ρ • u ∈ Fil o.A := by
    rw [hu, rho_part_eig act (β b.ρ) hρ y]; exact zero_mem _
  obtain ⟨w, hw, hsum⟩ := GlobalTheory.HTSummand.lie_mod_fil p D R b N C β s hs o u hω
  set c' := fun l => algebraMap (𝓞 D.F) D.O (c l)
  have h1 : ∀ l, act (c' l) u - ∑ i, act (c' l) (w i) ∈ Fil o.A := fun l => by
    rw [← map_sum, ← map_sub]; exact hfil _ hsum
  have h2 : ∀ i, ∑ l, lam l • act (c' l) (w i) ∈ Fil o.A := fun i => by
    have e : ∑ l, lam l • act (c' l) (w i) = ∑ l, lam l • (act (c' l) (w i) - β (b.t i (c l)) • w i) +
        (∑ l, lam l * β (b.t i (c l))) • w i := by
      rw [Finset.sum_smul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_sub, mul_smul]; abel
    rw [e, hlam i, zero_smul, add_zero]
    exact sum_mem fun l _ => Submodule.smul_mem _ _ (hw i (c l))
  have e : ∑ l, lam l • act (c' l) u = ∑ l, lam l • (act (c' l) u - ∑ i, act (c' l) (w i)) +
      ∑ i, ∑ l, lam l • act (c' l) (w i) := by
    rw [Finset.sum_comm (f := fun i l => lam l • act (c' l) (w i)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.smul_sum, ← smul_add, sub_add_cancel]
  show ∑ l, lam l • act (c' l) u ∈ Fil o.A
  rw [e]
  exact add_mem (sum_mem fun l _ => Submodule.smul_mem _ _ (h1 l)) (sum_mem fun i _ => h2 i)

theorem dualNumber_local (k : Type) [Field k] : IsLocalRing (DualNumber k) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by
    by_cases h : TrivSqZeroExt.fst x = 0
    · right
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      simp [h]
    · left
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact isUnit_iff_ne_zero.2 h

end GlobalTheory.HTCount.LieZFil

namespace GlobalTheory.HTCount

open LieZFil in
set_option maxHeartbeats 800000 in

theorem lieZ_mem_fil_and_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ z ∈ GlobalTheory.HTCount.lieZ o₀ β, z ∈ Fil o₀.A ∧ IsFilLift m'.cart z 0 := by
  intro p _ D R _ b N k _ t o₀ β ht o' m' z hz
  constructor
  · induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, lam, c, y, ⟨y', rfl⟩, hlam, rfl⟩ := hx
      exact sum_mem_fil β ht o₀ lam c hlam y'
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact Submodule.smul_mem _ a hx
  · have hbc := GlobalTheory.HTRealise.isBC_constMor o₀.ab
    suffices H : ∀ z ∈ lieZ o₀ β, hbc.bcMap z ∈ liftFil (epsDP k) m'.cart by
      refine ⟨hbc.bcMap z, H z hz, fun c => ?_⟩
      rw [(hbc.corr_iff.2 rfl) c]
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    have hE : ∀ (x : D.O) (h : HdR o₀.A), crysToDR (epsDP k) m'.cart (hbc.bcMap (crysAct o₀ x h)) =
        GlobalTheory.HTSummand.crysAct (dp0 (DualNumber k)) (𝟙 _) o'.act x (crysToDR (epsDP k) m'.cart (hbc.bcMap h)) := by
      intro x h
      haveI := o₀.act.hom x
      haveI := o'.act.hom x
      have e1 : hbc.bcMap (crysAct o₀ x h) =
          push (epsDP k) (GlobalTheory.DeRham.epsRed k) (o₀.act.act x) (hbc.bcMap h) := by
        rw [← hbc.corr_iff]
        exact GrpMor.Corr.push (m := constMor o₀.A) (constMor o₀.A) (o₀.act.act x) (o₀.act.act x) (by rfl)
          (hbc.corr_iff.2 rfl)
      have e2 := crysToDR_push (epsDP k) m'.cart m'.cart (o₀.act.act x) (o'.act.act x) (m'.act x).symm (hbc.bcMap h)
      exact (congrArg (crysToDR (epsDP k) m'.cart) e1).trans e2
    have hs : spMap (algebraMap k (DualNumber k)) ≫ t = spMap ((algebraMap k (DualNumber k)).comp β) := by
      rw [ht]; unfold spMap; rw [← Spec.map_comp]; rfl
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, lam, c, y, ⟨y', rfl⟩, hlam, rfl⟩ := hx
      have hlam' : ∀ i, ∑ l, algebraMap k (DualNumber k) (lam l) *
          ((algebraMap k (DualNumber k)).comp β) (b.t i (c l)) = 0 := fun i => by
        simp only [RingHom.comp_apply, ← map_mul, ← map_sum, hlam i, map_zero]
      haveI : IsLocalRing (DualNumber k) := dualNumber_local k
      have key := sum_mem_fil ((algebraMap k (DualNumber k)).comp β) hs o' (fun l => algebraMap k _ (lam l)) c hlam'
        (crysToDR (epsDP k) m'.cart (hbc.bcMap y'))
      rw [liftFil, Submodule.mem_comap]
      convert key using 2
      simp only [map_sum, map_smulₛₗ, hE, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, map_sub, RingHom.comp_apply, map_intCast, RingHom.id_apply, map_smul]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

end GlobalTheory.HTCount
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieConditionHodgeSubspace_constant_lift_mem_fil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ z ∈ GlobalTheory.HTCount.lieZ o₀ β, z ∈ Fil o₀.A ∧ IsFilLift m'.cart z 0 := by
  first | (exact @GlobalTheory.HTCount.lieZ_mem_fil_and_lift) | (exact GlobalTheory.HTCount.lieZ_mem_fil_and_lift) | (intros; apply GlobalTheory.HTCount.lieZ_mem_fil_and_lift <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section
namespace GlobalTheory.HTNecessary

variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀] {A' : Over (Sp (DualNumber k))} [GrpObj A']
  {i : A₀.left ⟶ A'.left} {h : IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i}

theorem isFilLift_add {x y x' y' : HdR A₀} (e : IsFilLift h x y) (e' : IsFilLift h x' y') :
    IsFilLift h (x + x') (y + y') := by
  obtain ⟨d, hd, e⟩ := e
  obtain ⟨d', hd', e'⟩ := e'
  refine ⟨d + d', add_mem hd hd', fun c ↦ ?_⟩
  rw [LinearMap.add_apply, e, e']
  ext <;> simp

theorem isFilLift_smul {x y : HdR A₀} (e : IsFilLift h x y) (r : k) :
    IsFilLift h (r • x) (r • y) := by
  obtain ⟨d, hd, e⟩ := e
  refine ⟨algebraMap k (DualNumber k) r • d, Submodule.smul_mem _ _ hd, fun c ↦ ?_⟩
  rw [LinearMap.smul_apply, e]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem isFilLift_zero : IsFilLift h (0 : HdR A₀) 0 :=
  ⟨0, zero_mem _, fun c ↦ by
    simp only [LinearMap.zero_apply, TrivSqZeroExt.inl_zero, TrivSqZeroExt.inr_zero, add_zero]⟩

theorem isFilLift_push (f₀ : A₀ ⟶ A₀) (f : A' ⟶ A') [IsMonHom f₀] [IsMonHom f] (e : i ≫ f.left = f₀.left ≫ i)
    {x y : HdR A₀} (hxy : IsFilLift h x y) :
    IsFilLift h (push (dp0 k) (𝟙 _) f₀ x) (push (dp0 k) (𝟙 _) f₀ y) := by
  obtain ⟨d, hd, e'⟩ := hxy
  have hmem := push_mem_liftFil (epsDP k) h h f₀ f e hd
  refine ⟨_, hmem, fun c ↦ ?_⟩
  have k1 := (homMor (dp0 k) (𝟙 _) f₀).comp (constMor A₀)
  have e1 := GrpMor.pull_pull (constMor A₀) (homMor (epsDP k) _ f₀) k1 (fun _ ↦ rfl) (by simp) c
  have e2 := GrpMor.pull_pull (homMor (dp0 k) (𝟙 _) f₀) (constMor A₀) k1 (fun _ ↦ rfl) rfl c
  rw [push_apply]
  show d (primPull _ _ f₀ _) = _
  erw [primPull, e1, ← e2, e']
  rfl

theorem exists_isFilLift (hA' : IsAbelianScheme A') {x : HdR A₀} (hx : x ∈ Fil A₀) : ∃ y, IsFilLift h x y := by
  obtain ⟨g, hg⟩ := GlobalTheory.KSGraph.exists_dim A' hA'
  obtain ⟨v, ⟨y, hy, -⟩, -⟩ := GlobalTheory.DeRham.ksRegular_of_isAbelianScheme GlobalTheory.T.abelianScheme_firstDeRham_structure h hA' hg x hx
  exact ⟨y, hy⟩

theorem main : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃ g : HdR o₀.A →ₗ[k] HdR o₀.A, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) g ∧ ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (g x) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β hβ φ hφ o' m'
  have hab₀ := o₀.ab
  have hab' := o'.ab
  have hL1 : ∀ x ∈ Fil o₀.A, ∃ y, IsFilLift m'.cart x y := fun x hx ↦ exists_isFilLift hab' hx
  have hG := GlobalTheory.KSGraph.isFilLift_iff_sub_mem k o₀.A o'.A m'.φ m'.cart hab'
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Fil o₀.A)
  let bs := Module.Basis.ofVectorSpace k (Fil o₀.A)
  let f : Fil o₀.A →ₗ[k] HdR o₀.A := bs.constr k fun j ↦ (hL1 _ (bs j).2).choose
  have hf : ∀ x : Fil o₀.A, IsFilLift m'.cart x.1 (f x) := by
    intro x
    have hx : x ∈ Submodule.span k (Set.range bs) := by rw [bs.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [Module.Basis.constr_basis]
      exact (hL1 _ (bs j).2).choose_spec
    | zero => simpa using isFilLift_zero
    | add x y _ _ hx hy => simpa using isFilLift_add hx hy
    | smul r x _ hx => simpa using isFilLift_smul hx r
  let g : HdR o₀.A →ₗ[k] HdR o₀.A := f ∘ₗ Submodule.linearProjOfIsCompl _ _ hC
  have hg : ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (g x) := fun x hx ↦ by
    have : Submodule.linearProjOfIsCompl _ _ hC x = ⟨x, hx⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨x, hx⟩
    simpa [g, this] using hf ⟨x, hx⟩
  refine ⟨g, ⟨fun a x hx ↦ ?_, fun z hz ↦ ?_, fun x hx y hy ↦ ?_⟩, hg⟩
  · haveI := o₀.act.hom a
    haveI := o'.act.hom a
    have hax : GlobalTheory.HTCount.crysAct o₀ a x ∈ Fil o₀.A := by
      rw [GlobalTheory.HTCount.crysAct_apply]; exact push_mem_Fil _ hx
    have e1 : IsFilLift m'.cart (GlobalTheory.HTCount.crysAct o₀ a x) (GlobalTheory.HTCount.crysAct o₀ a (g x)) := by
      rw [GlobalTheory.HTCount.crysAct_apply]
      exact isFilLift_push (o₀.act.act a) (o'.act.act a) (m'.act a).symm (hg x hx)
    exact (hG _ hax _ _ e1).1 (hg _ hax)
  · obtain ⟨hz₀, hz⟩ := GlobalTheory.T.lieConditionHodgeSubspace_constant_lift_mem_fil p D R b N k t o₀ β hβ o' m' z hz
    simpa using (hG _ hz₀ _ _ hz).1 (hg _ hz₀)
  · exact GlobalTheory.T.harrisTaylor_firstOrder_deformation_skew p D R b N k t o₀ φ hφ o' m' x hx y hy _ _ (hg x hx) (hg y hy)

end GlobalTheory.HTNecessary
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_firstOrder_hodge_eq_kodairaSpencer_graph : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃ g : HdR o₀.A →ₗ[k] HdR o₀.A, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) g ∧ ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (g x) := by
  first | (exact @GlobalTheory.HTNecessary.main) | (exact GlobalTheory.HTNecessary.main) | (intros; apply GlobalTheory.HTNecessary.main <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTCount

theorem count : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ f : Fin (D.a * (D.n - 1)) → (HdR o₀.A →ₗ[k] HdR o₀.A), (∀ j, ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f j x)) ∧ ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃! c : Fin (D.a * (D.n - 1)) → k, ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (∑ j, c j • f j x) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀
  obtain ⟨β, hβ⟩ : ∃ β : R →+* k, t = spMap β := ⟨(Spec.preimage t).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.harrisTaylor_exists_deRham_pairing p D R b N hN hNp k t o₀
  obtain ⟨f, hfKS, huniq⟩ := GlobalTheory.T.harrisTaylor_kodairaSpencer_directions_dim p D R b N hN hNp k t o₀ β hβ φ hφ
  refine ⟨f, fun j => GlobalTheory.T.harrisTaylor_realise_kodairaSpencer_direction p D R b N hN hNp k t o₀ β hβ φ hφ (f j) (hfKS j), fun o' m' => ?_⟩
  obtain ⟨g, hgKS, hg⟩ := GlobalTheory.T.harrisTaylor_firstOrder_hodge_eq_kodairaSpencer_graph p D R b N hN hNp k t o₀ β hβ φ hφ o' m'
  obtain ⟨c, hc, hcu⟩ := huniq g hgKS
  refine ⟨c, fun x hx => ?_, fun c' hc' => hcu c' fun x hx => ?_⟩
  · refine (GlobalTheory.T.hodgeFiltration_lift_determines_mod_fil k o₀.A o'.A m'.φ m'.cart o'.ab x hx (g x) _ (hg x hx)).2 ?_
    rw [← neg_sub]; exact neg_mem (hc x hx)
  · have := (GlobalTheory.T.hodgeFiltration_lift_determines_mod_fil k o₀.A o'.A m'.φ m'.cart o'.ab x hx (g x) _ (hg x hx)).1 (hc' x hx)
    rw [← neg_sub]; exact neg_mem this

end GlobalTheory.HTCount
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_firstOrder_deformations_basis_count : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ f : Fin (D.a * (D.n - 1)) → (HdR o₀.A →ₗ[k] HdR o₀.A), (∀ j, ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f j x)) ∧ ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃! c : Fin (D.a * (D.n - 1)) → k, ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (∑ j, c j • f j x) := by
  first | (exact @GlobalTheory.HTCount.count) | (exact GlobalTheory.HTCount.count) | (intros; apply GlobalTheory.HTCount.count  <;> assumption)
end
