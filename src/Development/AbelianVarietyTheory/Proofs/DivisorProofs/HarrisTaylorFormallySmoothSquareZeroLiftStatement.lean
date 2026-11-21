import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystalReductionSquareZeroArtinian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrysForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomIdPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstDeRhamHomologyProjectiveOverTensorIntegers
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalFiniteFreeReducesToDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilLagrangianOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianLiftLieSquareZeroHarrisTaylor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftOrderActionHodgeSummandStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsPolarisationBundleLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftLieOfHodgeSummandLieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieMultiplicitySquareZeroLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPrimeToPLevelLiftSquareZeroStatement

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open GlobalTheory.AbDual GlobalTheory.AbLaw GlobalTheory.CechPic

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTPerf

theorem bijective_deRham (HR : GlobalTheory.Published.AbelianDeRham) (HD : GlobalTheory.Published.AbelianDualCrystal) {K : Type} [CommRing K]
    [IsNoetherianRing K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) (g : ℕ)
    (hg : SmoothOfRelativeDimension g A.hom) (P : LB (A ⊗ A).left) (hP : P.IsLB)
    (r₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (r₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (hsym : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    (amp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)) (e : ℕ) (he0 : 0 < e) (he : IsUnit (e : K))
    (hker : ∀ (T : Over (Sp K)) (x : T ⟶ A),
      (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1)
    (ψ : HdR A →ₗ[K] HdR A →ₗ[K] K) (hψ : IsCorrForm (dp0 K) (𝟙 _) A A P ψ) : Function.Bijective ψ := by

  have hsw : (swap P).IsLB := pull_isLB hP _
  have ec : cls P hP = cls _ hsw := (cls_eq_iff hP hsw).2 hsym
  have key : ∀ (Y : Over (Sp K)) (a b : Y ⟶ A), evc hP a b = evc hP b a := fun Y a b ↦ by
    rw [← evc_swap hP hsw a b]
    show CechPic.pull _ (cls P hP) = CechPic.pull _ (cls _ hsw)
    rw [ec]

  obtain ⟨B, _, Q, hB, hBg, hd, hd'⟩ := HD.1 (Sp K) A hA
  have hBg := hBg _ hg
  haveI : IsCommMonObj B := hB.comm

  have hL := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  obtain ⟨H, hH, hamp⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod hA hA hL amp hL amp
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_of_triv hA hA hH hamp hP r₁ r₂
  obtain ⟨lam, hlam, hcls⟩ := GlobalTheory.BirigidLift.exists_hom hd hd'.additive hP a₁ a₂

  have hkerl : ∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ lam = 1 → x ^ e = 1 := by
    intro T x hx
    have tr : Triv (ev P (fst A T) (snd A T ≫ x)) := by
      rw [triv_ev_iff hP, GlobalTheory.BirigidLift.evc_of_cls hd.isLB hP hcls, Category.assoc, hx, comp_one]
      exact evc_one_right hd.isLB hd.zero _
    refine hker T x ((triv_ev_iff hP _ _).2 ?_)
    rw [key]
    exact (triv_ev_iff hP _ _).1 tr
  obtain ⟨μ', hμ', e₁, e₂⟩ := GlobalTheory.IsogenyQuasiInverse.exists_quasiInverse K A B g hA hB hg hBg lam hlam e he0 hkerl
  haveI := hlam
  haveI := hμ'
  have hpush := GlobalTheory.PolPrimeTo.bijective_push (dp0 K) (𝟙 _) lam μ' e he e₁ e₂

  obtain ⟨⟨φ, hφ, -⟩, hperf⟩ := GlobalTheory.Published.AbelianDualCrystal.duality HR hA hg hB hBg (hd.isPerfect hd')
  have C := cupSquare_of_free HR.1 (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_prod hg hg)
  have e' : LBIso (ev Q (fst A A) (snd A A ≫ lam)) (ev P (fst A A ≫ 𝟙 A) (snd A A)) := by
    refine (cls_eq_iff (pull_isLB hd.isLB _) (pull_isLB hP _)).1 ?_
    rw [cls_ev hd.isLB, cls_ev hP, GlobalTheory.BirigidLift.evc_of_cls hd.isLB hP hcls, Category.comp_id]
  have hadj : ∀ x y, φ x (push (dp0 K) (𝟙 _) lam y) = ψ x y := fun x y ↦ by
    have k := IsCorrForm.adjoint C hd.isLB hP hφ hψ (𝟙 A) lam e' x y
    rwa [push_id] at k
  haveI := (hperf φ hφ).1
  have hφb : Function.Bijective φ := LinearMap.IsPerfPair.bijective_left φ
  let E := LinearEquiv.ofBijective _ hpush
  have : ⇑ψ = ⇑E.dualMap ∘ ⇑φ := by
    funext x
    refine LinearMap.ext fun y ↦ ?_
    rw [Function.comp_apply, LinearEquiv.dualMap_apply, ← hadj]
    rfl
  rw [this]
  exact E.dualMap.bijective.comp hφb

end GlobalTheory.HTPerf

namespace GlobalTheory.HTPerf

open GlobalTheory.Published.GrothendieckMessing IsLocalRing

set_option maxHeartbeats 1600000 in

theorem skew_bijective : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → (∀ x y, φ x y = -φ y x) ∧ Function.Bijective φ := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ φ hφ
  have hI2 : RingHom.ker π ^ 2 = ⊥ := hsq
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hI2] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  haveI : IsNoetherianRing C₀ := isNoetherianRing_of_surjective C C₀ π hπ
  let κ := divided₂ hsq
  have hκ : IsNilDP κ := isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  have GD : GlobalTheory.Published.GrothendieckDeformation :=
    GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.abelianDeRham GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers
  have hA₀ := o₀.ab
  have hP₀ := o₀.isLB
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.AbelianDim.exists_relDim C₀ o₀.A hA₀
  obtain ⟨A', _, i', h', hA'⟩ := GlobalTheory.UnobTop.abelianUnobstructed C (RingHom.ker π) hsq C₀ π hπ rfl o₀.A hA₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C A' hA'
  have Cs := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl hA' hg hA' hg h' h'

  have hsw : (swap o₀.P).IsLB := pull_isLB hP₀ _
  have hs : LBIso (swap o₀.P) o₀.P := (cls_eq_iff hsw hP₀).1 ((cls_eq_iff hP₀ hsw).2 o₀.symm).symm
  have skew : ∀ x y, φ x y = -φ y x := GlobalTheory.SymmPoincare.skew_of_symm Cs hP₀ hs hφ
  refine ⟨skew, ?_⟩

  have HC := (GD C (RingHom.ker π) κ hκ C₀ π hπ rfl).1
  obtain ⟨bij, -, -⟩ := HC g o₀.A A' i' h' hA' hg
  let e := LinearEquiv.ofBijective (crysToDR κ h') (HC.crysToDR_bijective h' hA' hg)
  have ee : ∀ xA, crysToDR κ h' (e.symm xA) = xA := e.apply_symm_apply
  letI : Algebra C C₀ := π.toAlgebra
  have hBC := (ADR.2.2.1 C A' g hA' hg C₀ o₀.A i' h').1
  obtain ⟨hfinA, hprojA, -⟩ := ADR.1.prim hA' hg
  haveI := hfinA
  haveI := hprojA
  haveI : Module.Finite C (Crys κ (spMap π) o₀.A) := Module.Finite.equiv e.symm
  haveI : Module.Projective C (Crys κ (spMap π) o₀.A) := Module.Projective.of_equiv e.symm

  let red : Crys κ (spMap π) o₀.A →ₛₗ[π] HdR o₀.A := hBC.bcMap.comp (crysToDR κ h')
  have hm : ∀ x, (crysRedMor κ rfl o₀.A).Corr x (red x) := fun x ↦
    (corr_crysToDR_iff rfl h' bij.2 x (red x)).1 (by exact hBC.corr_iff.2 rfl)
  have iso : LBIso (o₀.P.pull (Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A)))) o₀.P :=
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP₀ _) hP₀).1
      (by rw [GlobalTheory.CechPic.cls_pull hP₀, Over.id_left, GlobalTheory.CechPic.pull_id])
  obtain ⟨φ', hφ', e'⟩ := hφ.pull hP₀ (crysRedMor κ rfl o₀.A) (crysRedMor κ rfl o₀.A)
    (h := Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A))) (by simp) (by simp) hP₀ iso
  have hrel : ∀ x y, φ' (red x) (red y) = π (φ x y) := fun x y ↦ e' x (red x) y (red y) (hm x) (hm y)
  have hred : Function.Surjective red := by
    intro y
    let l : primDR A' →ₗ[C] C₀ :=
      { toFun c := y ((redMor h').pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨xA, hx⟩ := Module.projective_lifting_property (Algebra.linearMap C C₀) l hπ
    refine ⟨e.symm xA, ?_⟩
    show hBC.bcMap (crysToDR κ h' (e.symm xA)) = y
    rw [ee]
    exact hBC.corr_iff.1 fun c ↦ (LinearMap.congr_fun hx c).symm
  have hker : ∀ x, red x = 0 → x ∈ (RingHom.ker π) • (⊤ : Submodule C (Crys κ (spMap π) o₀.A)) := by
    intro x hx
    have hc := hBC.corr_iff.2 hx
    have hmem := GlobalTheory.BirigLift.mem_smul_top_of_forall_mem (RingHom.ker π) (crysToDR κ h' x) fun c ↦
      RingHom.mem_ker.2 ((hc c).symm.trans (LinearMap.zero_apply _))
    have := Submodule.mem_map_of_mem (f := e.symm.toLinearMap) hmem
    rw [Submodule.map_smul''] at this
    have ex : e.symm.toLinearMap (crysToDR κ h' x) = x := e.symm_apply_apply x
    rw [ex] at this
    exact Submodule.smul_mono le_rfl le_top this

  obtain ⟨k, hkp, hkerP⟩ := o₀.kerP
  have hk0 : 0 < k := by
    refine Nat.pos_of_ne_zero fun h0 ↦ ?_
    rw [h0, Nat.coprime_zero_left] at hkp
    exact (Fact.out : p.Prime).one_lt.ne' hkp
  have hku : IsUnit (k : C₀) := by
    have := (b.unit k hkp).map (π.comp tR)
    rwa [map_natCast] at this
  have hψb : Function.Bijective φ' :=
    bijective_deRham ADR ADC o₀.A hA₀ g₀ hg₀ o₀.P hP₀ o₀.rig₁ o₀.rig₂ o₀.symm o₀.ample k hk0 hku hkerP φ' hφ'
  have skew' : ∀ u v, φ' u v = -φ' v u := fun u v ↦ by
    obtain ⟨x, rfl⟩ := hred u
    obtain ⟨y, rfl⟩ := hred v
    rw [hrel, hrel, skew, map_neg]
  have hψf : Function.Surjective φ'.flip := fun l ↦ by
    obtain ⟨x, hx⟩ := hψb.2 (-l)
    exact ⟨x, LinearMap.ext fun y ↦ by rw [LinearMap.flip_apply, skew', hx, LinearMap.neg_apply, neg_neg]⟩
  have hperf := GlobalTheory.BirigLift.exists_perfect_mod π red φ φ' hπ hψf hred hker hrel

  have htop : (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C)) ≤ LinearMap.range φ.flip ⊔ RingHom.ker π • ⊤ := fun l _ ↦ by
    obtain ⟨z, hz⟩ := hperf l
    have hmem := GlobalTheory.BirigLift.mem_smul_top_of_forall_mem (RingHom.ker π) (l - φ.flip z) fun c ↦ by
      simpa only [LinearMap.sub_apply, LinearMap.flip_apply] using hz c
    exact Submodule.mem_sup.2 ⟨φ.flip z, ⟨z, rfl⟩, l - φ.flip z, hmem, add_sub_cancel _ _⟩
  have hIle : RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C)) ≤ LinearMap.range φ.flip := by
    calc RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C)) ≤ RingHom.ker π • (LinearMap.range φ.flip ⊔ RingHom.ker π • ⊤) :=
          Submodule.smul_mono le_rfl htop
      _ = RingHom.ker π • LinearMap.range φ.flip ⊔ RingHom.ker π • RingHom.ker π • ⊤ := Submodule.smul_sup _ _ _
      _ ≤ LinearMap.range φ.flip := by
          refine sup_le Submodule.smul_le_right ?_
          rw [← Submodule.mul_smul, ← pow_two, hI2, Submodule.bot_smul]
          exact bot_le
  have hsurj : Function.Surjective φ.flip :=
    LinearMap.range_eq_top.1 (top_le_iff.1 (htop.trans (sup_le le_rfl hIle)))
  haveI : Module.Free C (Crys (divided₂ hsq) (spMap π) o₀.A) := Module.free_of_flat_of_isLocalRing
  let bs := Module.finBasis C (Crys (divided₂ hsq) (spMap π) o₀.A)
  have hinj : Function.Injective φ.flip := by
    have hs' : Function.Surjective (bs.toDualEquiv.symm.toLinearMap ∘ₗ φ.flip) :=
      bs.toDualEquiv.symm.surjective.comp hsurj
    have hi := OrzechProperty.injective_of_surjective_endomorphism _ hs'
    exact fun x y hxy ↦ hi (by simp only [LinearMap.coe_comp, Function.comp_apply, hxy])
  have hneg : ∀ x, φ x = -φ.flip x := fun x ↦
    LinearMap.ext fun y ↦ by rw [LinearMap.neg_apply, LinearMap.flip_apply, skew]
  refine ⟨fun x x' hxx ↦ hinj (neg_injective ?_), fun l ↦ ?_⟩
  · rw [← hneg, ← hneg, hxx]
  · obtain ⟨z, hz⟩ := hsurj (-l)
    exact ⟨z, by rw [hneg, hz, neg_neg]⟩

end GlobalTheory.HTPerf
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystal_reduction_squareZero_artinian : ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [Ring O] (a : GlobalTheory.UPel.HT.OActN O A₀), ∃ red : Crys (divided₂ hsq) (spMap π) A₀ →ₛₗ[π] HdR A₀, Module.Finite C (Crys (divided₂ hsq) (spMap π) A₀) ∧ Module.Projective C (Crys (divided₂ hsq) (spMap π) A₀) ∧ Function.Surjective red ∧ (∀ x, red x = 0 → x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) A₀))) ∧ (∀ d y, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl A₀).Corr d y ↔ red d = y) ∧ (∀ (c : O) d, red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a c d) = GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) a c (red d)) ∧ ∃ E' M : Submodule C (Crys (divided₂ hsq) (spMap π) A₀), IsCompl E' M ∧ ∀ y, y ∈ Fil A₀ ↔ ∃ d ∈ E', red d = y := by
  first | exact @GlobalTheory.CrysRed.exists_crysRed | exact GlobalTheory.CrysRed.exists_crysRed | (intros; apply GlobalTheory.CrysRed.exists_crysRed <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstDeRhamHomology_projective_over_tensor_integers : ∀ (F : Type) [Field F] [NumberField F] (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (dp0 k) (𝟙 _) a; Module.Projective (k ⊗[ℤ] 𝓞 F) (HdR A₀) := by
  first | exact @GlobalTheory.CrysProj.hdR_projective | exact GlobalTheory.CrysProj.hdR_projective | (intros; apply GlobalTheory.CrysProj.hdR_projective <;> assumption)
end

section
section
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HTSummand

theorem isNilpotent_matrix_of_entries_mem {R : Type*} [CommRing R] {n : ℕ} (I : Ideal R) (N : ℕ)
    (hN : I ^ N = ⊥) (M : Matrix (Fin n) (Fin n) R) (hM : ∀ i j, M i j ∈ I) : IsNilpotent M := by
  have key : ∀ j : ℕ, ∀ a b, (M ^ j) a b ∈ I ^ j := by
    intro j
    induction j with
    | zero => intro a b; rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    | succ j ih =>
      intro a b
      rw [pow_succ M, Matrix.mul_apply, pow_succ I]
      exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_mul (ih a c) (hM c b)
  refine ⟨N, ?_⟩
  ext a b
  have := key N a b
  rw [hN, Ideal.mem_bot] at this
  simpa using this

theorem le_pow_smul_of_le_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (K : Submodule R M) (hK : K ≤ I • K) (j : ℕ) : K ≤ (I ^ j) • K := by
  induction j with
  | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  | succ j ih =>
    rw [pow_succ', Submodule.mul_smul]
    exact hK.trans (Submodule.smul_mono le_rfl ih)

end GlobalTheory.HTSummand

namespace GlobalTheory.HTSummand

theorem projective_tensor_of_fibre_projective :
    ∀ (C k B : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Field k] [CommRing B] (σ : C →+* k),
      Function.Surjective σ → ∀ (H V : Type 1) [AddCommGroup H] [Module C H] [AddCommGroup V] [Module k V]
      (ρ : B →+* Module.End C H) (ρ' : B →+* Module.End k V) (f : H →ₛₗ[σ] V), Module.Finite C H →
      Module.Projective C H → Function.Surjective f →
      (∀ h, f h = 0 → h ∈ RingHom.ker σ • (⊤ : Submodule C H)) → (∀ x h, f (ρ x h) = ρ' x (f h)) →
      (letI := GlobalTheory.HTSummand.tensorModOf ρ'; Module.Projective (k ⊗[ℤ] B) V) →
      letI := GlobalTheory.HTSummand.tensorModOf ρ; Module.Projective (C ⊗[ℤ] B) H := by
  intro C k B _ _ _ _ _ σ hσ H V _ _ _ _ ρ ρ' f hfin hproj hf hker hcomm hV
  letI mH : Module (C ⊗[ℤ] B) H := tensorModOf ρ
  letI mV : Module (k ⊗[ℤ] B) V := tensorModOf ρ'

  set m : Ideal C := RingHom.ker σ with hm_def
  have hmtop : m ≠ ⊤ := by
    intro h
    have : (1 : C) ∈ m := h ▸ Submodule.mem_top
    rw [hm_def, RingHom.mem_ker, map_one] at this
    exact one_ne_zero this
  have hmjac : m ≤ (⊥ : Ideal C).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hmtop
  obtain ⟨N, hN⟩ : ∃ N : ℕ, m ^ N = ⊥ := by
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
    exact ⟨N, le_bot_iff.1 ((Ideal.pow_right_mono hmjac N).trans (le_of_eq hN))⟩

  let τa := Algebra.TensorProduct.map σ.toIntAlgHom (AlgHom.id ℤ B)
  let τ : C ⊗[ℤ] B →+* k ⊗[ℤ] B := τa.toRingHom
  have hτ : Function.Surjective τ :=
    Algebra.TensorProduct.map_surjective σ.toIntAlgHom (AlgHom.id ℤ B) hσ Function.surjective_id
  have hτtmul : ∀ (c : C) (b : B), τ (c ⊗ₜ b) = σ c ⊗ₜ b := fun _ _ => rfl
  have hkerτ : RingHom.ker τ ≤ Ideal.map (algebraMap C (C ⊗[ℤ] B)) m := by
    have h1 : RingHom.ker τ = Ideal.map Algebra.TensorProduct.includeLeft m :=
      Algebra.TensorProduct.rTensor_ker σ.toIntAlgHom hσ
    rw [h1]
    exact Ideal.map_le_iff_le_comap.2 fun c hc => Ideal.mem_map_of_mem (algebraMap C (C ⊗[ℤ] B)) hc
  have hJm : ∀ x ∈ RingHom.ker τ, x ∈ (m • ⊤ : Submodule C (C ⊗[ℤ] B)) := by
    intro x hx
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    exact hkerτ hx
  have hJN : (RingHom.ker τ) ^ N = ⊥ := by
    refine le_bot_iff.1 ((Ideal.pow_right_mono hkerτ N).trans ?_)
    rw [← Ideal.map_pow, hN, Ideal.map_bot]

  haveI tC : IsScalarTower C (C ⊗[ℤ] B) H := IsScalarTower.of_algebraMap_smul fun c h => by
    show ((c ⊗ₜ[ℤ] (1 : B) : C ⊗[ℤ] B)) • h = c • h
    rw [tensorModOf_tmul, map_one]
    rfl
  letI mRV : Module (C ⊗[ℤ] B) V := Module.compHom V τ
  let fR : H →ₗ[C ⊗[ℤ] B] V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r h => by
        show f (r • h) = τ r • f h
        induction r using TensorProduct.induction_on with
        | zero => rw [zero_smul, map_zero, map_zero, zero_smul]
        | tmul c b =>
          rw [hτtmul, tensorModOf_tmul, tensorModOf_tmul, f.map_smulₛₗ, hcomm]
        | add x y hx hy => rw [add_smul, map_add, hx, hy, map_add, add_smul] }
  have hfR : Function.Surjective fR := hf
  haveI : Module.Finite (C ⊗[ℤ] B) H := Module.Finite.of_restrictScalars_finite C (C ⊗[ℤ] B) H
  haveI : Module.Finite (C ⊗[ℤ] B) V := Module.Finite.of_surjective fR hfR
  haveI finSV : Module.Finite (k ⊗[ℤ] B) V := by
    letI : Algebra (C ⊗[ℤ] B) (k ⊗[ℤ] B) := τ.toAlgebra
    haveI : IsScalarTower (C ⊗[ℤ] B) (k ⊗[ℤ] B) V := IsScalarTower.of_algebraMap_smul fun r v => rfl
    exact Module.Finite.of_restrictScalars_finite (C ⊗[ℤ] B) (k ⊗[ℤ] B) V

  obtain ⟨n, pb, hpb⟩ := Module.Finite.exists_fin' (k ⊗[ℤ] B) V
  obtain ⟨sb, hsb⟩ := Module.projective_lifting_property pb LinearMap.id hpb
  have hps : ∀ v, pb (sb v) = v := fun v => LinearMap.congr_fun hsb v
  set eb : Matrix (Fin n) (Fin n) (k ⊗[ℤ] B) := LinearMap.toMatrix' (sb ∘ₗ pb) with heb
  have heb_idem : IsIdempotentElem eb := by
    show eb * eb = eb
    rw [heb, ← LinearMap.toMatrix'_comp]
    congr 1
    apply LinearMap.ext
    intro y
    simp only [LinearMap.comp_apply, hps]
  have heb_apply : ∀ y, eb.mulVec y = sb (pb y) := fun y => by
    rw [heb, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  obtain ⟨E, hE, hEeb⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent (τ.mapMatrix :
      Matrix (Fin n) (Fin n) (C ⊗[ℤ] B) →+* Matrix (Fin n) (Fin n) (k ⊗[ℤ] B))
    (fun x hx => by
      refine isNilpotent_matrix_of_entries_mem (RingHom.ker τ) N hJN x fun i j => ?_
      rw [RingHom.mem_ker] at hx ⊢
      exact congrFun (congrFun hx i) j)
    eb ⟨eb.map (Function.surjInv hτ), by ext i j; simp [Function.surjInv_eq hτ]⟩ heb_idem
  have hEE : ∀ w, E.mulVec (E.mulVec w) = E.mulVec w := fun w => by
    rw [Matrix.mulVec_mulVec, hE.eq]
  have hτE : ∀ w : Fin n → C ⊗[ℤ] B, (fun i => τ (E.mulVec w i)) = sb (pb (fun i => τ (w i))) := by
    intro w
    rw [← heb_apply, ← hEeb]
    funext i
    exact RingHom.map_mulVec τ E w i

  set Q : Submodule (C ⊗[ℤ] B) (Fin n → C ⊗[ℤ] B) := LinearMap.range (Matrix.toLin' E) with hQ
  have hQE : ∀ q : Q, E.mulVec (q : Fin n → C ⊗[ℤ] B) = q := by
    rintro ⟨q, w, rfl⟩
    show E.mulVec (Matrix.toLin' E w) = Matrix.toLin' E w
    rw [Matrix.toLin'_apply, hEE]
  let sQ : (Fin n → C ⊗[ℤ] B) →ₗ[C ⊗[ℤ] B] Q :=
    (Matrix.toLin' E).codRestrict Q fun w => LinearMap.mem_range_self _ w
  have hsQ : ∀ q : Q, sQ q = q := fun q => Subtype.ext (by
    show Matrix.toLin' E (q : Fin n → C ⊗[ℤ] B) = q
    rw [Matrix.toLin'_apply, hQE])
  haveI hQproj : Module.Projective (C ⊗[ℤ] B) Q :=
    Module.Projective.of_split Q.subtype sQ (LinearMap.ext hsQ)
  let φ : Q →ₗ[C ⊗[ℤ] B] V :=
    { toFun := fun q => pb (fun i => τ ((q : Fin n → C ⊗[ℤ] B) i))
      map_add' := fun x y => by
        rw [← map_add]
        congr 1
        funext i
        simp
      map_smul' := fun r x => by
        show pb _ = τ r • pb _
        rw [← map_smul]
        congr 1
        funext i
        simp }
  have hφ : Function.Surjective φ := by
    intro v
    let w : Fin n → C ⊗[ℤ] B := fun i => Function.surjInv hτ (sb v i)
    refine ⟨⟨Matrix.toLin' E w, LinearMap.mem_range_self _ w⟩, ?_⟩
    show pb (fun i => τ (Matrix.toLin' E w i)) = v
    rw [Matrix.toLin'_apply, hτE]
    have : (fun i => τ (w i)) = sb v := funext fun i => Function.surjInv_eq hτ _
    rw [this, hps, hps]
  obtain ⟨g, hg⟩ := Module.projective_lifting_property fR φ hfR
  have hgφ : ∀ q, f (g q) = φ q := fun q => LinearMap.congr_fun hg q

  have hgs : Function.Surjective g := by
    have hle : (⊤ : Submodule C H) ≤ (LinearMap.range g).restrictScalars C ⊔ m • ⊤ := by
      intro h _
      obtain ⟨q, hq⟩ := hφ (f h)
      have h0 : f (h - g q) = 0 := by rw [map_sub, hgφ, hq, sub_self]
      have : h = g q + (h - g q) := by abel
      rw [this]
      exact Submodule.add_mem_sup (LinearMap.mem_range_self g q) (hker _ h0)
    have htop := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hmjac hle
    intro h
    exact htop Submodule.mem_top

  let g' : Q →ₗ[C] H := g.restrictScalars C
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g' LinearMap.id hgs
  have hgs' : ∀ h, g' (s h) = h := fun h => LinearMap.congr_fun hs h
  let P : Q →ₗ[C] Q := LinearMap.id - s ∘ₗ g'
  have hPK : ∀ x, P x ∈ LinearMap.ker g' := fun x => by
    rw [LinearMap.mem_ker]
    show g' (x - s (g' x)) = 0
    rw [map_sub, hgs', sub_self]
  have hKm : ∀ x ∈ LinearMap.ker g', x ∈ (m • ⊤ : Submodule C Q) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hφx : φ x = 0 := by rw [← hgφ]; exact (congrArg f hx).trans (map_zero f)
    have hτx : (fun i => τ ((x : Fin n → C ⊗[ℤ] B) i)) = 0 := by
      have h1 := hτE x
      rw [hQE x] at h1
      rw [h1]
      have : pb (fun i => τ ((x : Fin n → C ⊗[ℤ] B) i)) = 0 := hφx
      rw [this, map_zero]
    have hx1 : (x : Fin n → C ⊗[ℤ] B) ∈ (m • ⊤ : Submodule C (Fin n → C ⊗[ℤ] B)) := by
      rw [← Finset.univ_sum_single (x : Fin n → C ⊗[ℤ] B)]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hi : (x : Fin n → C ⊗[ℤ] B) i ∈ (m • ⊤ : Submodule C (C ⊗[ℤ] B)) :=
        hJm _ (RingHom.mem_ker.2 (congrFun hτx i))
      have := Submodule.mem_map_of_mem (f := LinearMap.single C (fun _ : Fin n => C ⊗[ℤ] B) i) hi
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have := Submodule.mem_map_of_mem (f := sQ.restrictScalars C) hx1
    rw [Submodule.map_smul''] at this
    have hx' : sQ.restrictScalars C x = x := hsQ x
    rw [hx'] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hK : LinearMap.ker g' ≤ m • LinearMap.ker g' := by
    intro x hx
    have hPx : P x = x := by
      show x - s (g' x) = x
      rw [LinearMap.mem_ker.1 hx, map_zero, sub_zero]
    have := Submodule.mem_map_of_mem (f := P) (hKm x hx)
    rw [Submodule.map_smul'', hPx] at this
    exact Submodule.smul_mono le_rfl (fun y hy => by
      obtain ⟨z, _, rfl⟩ := hy
      exact hPK z) this
  have hK0 : LinearMap.ker g' = ⊥ := by
    have := le_pow_smul_of_le_smul m _ hK N
    rw [hN, Submodule.bot_smul] at this
    exact le_bot_iff.1 this
  have hgi : Function.Injective g := by
    have h' : Function.Injective g' := LinearMap.ker_eq_bot.1 hK0
    exact h'
  exact Module.Projective.of_equiv (LinearEquiv.ofBijective g ⟨hgi, hgs⟩)

end GlobalTheory.HTSummand
end
end

open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_tensor_of_fibre_projective' : ∀ (C k B : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Field k] [CommRing B] (σ : C →+* k), Function.Surjective σ → ∀ (H V : Type 1) [AddCommGroup H] [Module C H] [AddCommGroup V] [Module k V] (ρ : B →+* Module.End C H) (ρ' : B →+* Module.End k V) (f : H →ₛₗ[σ] V), Module.Finite C H → Module.Projective C H → Function.Surjective f → (∀ h, f h = 0 → h ∈ RingHom.ker σ • (⊤ : Submodule C H)) → (∀ x h, f (ρ x h) = ρ' x (f h)) → (letI := GlobalTheory.HTSummand.tensorModOf ρ'; Module.Projective (k ⊗[ℤ] B) V) → letI := GlobalTheory.HTSummand.tensorModOf ρ; Module.Projective (C ⊗[ℤ] B) H := by
  atlas_forward_decl GlobalTheory.HTSummand.projective_tensor_of_fibre_projective
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Functor.grpObjObj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HdRFibre

set_option maxHeartbeats 1000000 in

theorem fibre_baseChange : ∀ (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [CommRing O] (a : OAct O A₀), ∃ f : HdR A₀ →ₛₗ[algebraMap C₀ (IsLocalRing.ResidueField C₀)] HdR ((Over.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀)))).obj A₀), Function.Surjective f ∧ (∀ h, f h = 0 → h ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀))) ∧ ∀ (x : O) (h : HdR A₀), f (act (dp0 C₀) (𝟙 _) a x h) = act (dp0 (IsLocalRing.ResidueField C₀)) (𝟙 _) (OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a) x (f h) := by
  intro C₀ _ _ A₀ _ _ hA O _ a
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C₀ A₀ hA
  obtain ⟨hFree, -, hBC, -, -⟩ := GlobalTheory.T.abelianScheme_firstDeRham_structure
  have hh := isGrpPullback_pullback A₀ (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀)))
  have hbc := (hBC C₀ A₀ g hA hg (IsLocalRing.ResidueField C₀) _ _ hh).1
  obtain ⟨hfin, hproj, -⟩ := hFree.prim hA hg
  haveI := Module.finitePresentation_of_projective C₀ (primDR A₀)
  haveI : Module.Free C₀ (primDR A₀) := Module.free_of_flat_of_isLocalRing
  refine ⟨hbc.bcMap, ?_, ?_, ?_⟩
  · intro h'
    let l : primDR A₀ →ₗ[C₀] IsLocalRing.ResidueField C₀ :=
      { toFun c := h' ((Published.AbelianDeRham.bcMor hh).pull c)
        map_add' c d := by rw [map_add, map_add]
        map_smul' r c := by
          rw [map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
    obtain ⟨hh', hhl⟩ := Module.projective_lifting_property (Algebra.linearMap C₀ (IsLocalRing.ResidueField C₀)) l
      IsLocalRing.residue_surjective
    exact ⟨hh', hbc.corr_iff.1 fun c ↦ (LinearMap.congr_fun hhl c).symm⟩
  · intro x hx
    have hc := hbc.corr_iff.2 hx
    refine GlobalTheory.CrysFree.mem_smul_top_of_forall _ x fun c ↦ ?_
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact (hc c).symm.trans (LinearMap.zero_apply _)
  · intro x h
    haveI := a.hom x
    haveI := (OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a).hom x
    refine hbc.corr_iff.1 ?_
    exact GrpMor.Corr.push (m := Published.AbelianDeRham.bcMor hh) (Published.AbelianDeRham.bcMor hh)
      (a.act x) ((OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a).act x)
      (pullback.lift_fst _ _ _).symm (hbc.corr_iff.2 rfl)

end GlobalTheory.HdRFibre
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Functor.grpObjObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamHomology_closedFibre_surjective_kernel : ∀ (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [CommRing O] (a : OAct O A₀), ∃ f : HdR A₀ →ₛₗ[algebraMap C₀ (IsLocalRing.ResidueField C₀)] HdR ((Over.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀)))).obj A₀), Function.Surjective f ∧ (∀ h, f h = 0 → h ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀))) ∧ ∀ (x : O) (h : HdR A₀), f (act (dp0 C₀) (𝟙 _) a x h) = act (dp0 (IsLocalRing.ResidueField C₀)) (𝟙 _) (OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a) x (f h) := by
  first | (exact @GlobalTheory.HdRFibre.fibre_baseChange) | (exact GlobalTheory.HdRFibre.fibre_baseChange) | (intros; apply GlobalTheory.HdRFibre.fibre_baseChange  <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Functor.grpObjObj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTSummand

theorem crys_projective : ∀ (F : Type) [Field F] [NumberField F] (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [Ring O] [Algebra (𝓞 F) O] (a : GlobalTheory.UPel.HT.OActN O A₀), letI := GlobalTheory.HTSummand.tensorModOf ((GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a).comp (algebraMap (𝓞 F) O)); Module.Projective (C ⊗[ℤ] 𝓞 F) (Crys (divided₂ hsq) (spMap π) A₀) := by
  intro F _ _ C C₀ _ _ _ _ π hπ hsq A₀ _ _ hA O _ _ a
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hsq] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  obtain ⟨red, hfin, hproj, hsurj, hker, -, hequiv, -⟩ := GlobalTheory.T.exists_crystal_reduction_squareZero_artinian C C₀ π hπ hsq A₀ hA O a
  let a' : OAct (𝓞 F) A₀ :=
    { act := fun x ↦ a.act (algebraMap (𝓞 F) O x)
      hom := fun x ↦ a.hom _
      one := by rw [map_one]; exact a.one
      mul := fun x y ↦ by rw [mul_comm, map_mul, a.mul]
      add := fun x y ↦ by rw [map_add, a.add] }
  obtain ⟨f, fsurj, fker, fequiv⟩ := GlobalTheory.T.deRhamHomology_closedFibre_surjective_kernel C₀ A₀ hA (𝓞 F) a'
  have hB := GlobalTheory.isAbelianScheme_pullback_obj (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ hA
  have hP := GlobalTheory.T.firstDeRhamHomology_projective_over_tensor_integers F (IsLocalRing.ResidueField C₀) _ hB (OAct.pullback _ A₀ a')
  let σ : C →+* IsLocalRing.ResidueField C₀ := (algebraMap C₀ (IsLocalRing.ResidueField C₀)).comp π
  have hσ : Function.Surjective σ := IsLocalRing.residue_surjective.comp hπ
  haveI : RingHomCompTriple π (algebraMap C₀ (IsLocalRing.ResidueField C₀)) σ := ⟨rfl⟩
  have hle : RingHom.ker π ≤ RingHom.ker σ := fun b hb ↦ by
    rw [RingHom.mem_ker] at hb ⊢
    show algebraMap C₀ (IsLocalRing.ResidueField C₀) (π b) = 0
    rw [hb, map_zero]
  refine GlobalTheory.T.projective_tensor_of_fibre_projective' C (IsLocalRing.ResidueField C₀) (𝓞 F) σ hσ _ _
    ((GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a).comp (algebraMap (𝓞 F) O))
    (act (dp0 (IsLocalRing.ResidueField C₀)) (𝟙 _) (OAct.pullback _ A₀ a')) (f.comp red) hfin hproj
    (fsurj.comp hsurj) ?_ ?_ hP
  · intro h hh
    have h1 : red h ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀)) := fker _ hh
    have h2 : ∀ y ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀)),
        ∃ x ∈ RingHom.ker σ • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) A₀)), red x = y := by
      intro y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro c hc y _
        obtain ⟨b, rfl⟩ := hπ c
        obtain ⟨x, rfl⟩ := hsurj y
        refine ⟨b • x, Submodule.smul_mem_smul ?_ Submodule.mem_top, ?_⟩
        · rw [RingHom.mem_ker]
          show algebraMap C₀ (IsLocalRing.ResidueField C₀) (π b) = 0
          rw [IsLocalRing.ResidueField.algebraMap_eq]
          exact (IsLocalRing.residue_eq_zero_iff _).2 hc
        · exact LinearMap.map_smulₛₗ red b x
      · rintro y y' ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
        exact ⟨x + x', add_mem hx hx', map_add _ _ _⟩
    obtain ⟨x, hx, hxe⟩ := h2 _ h1
    have h3 : h - x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) A₀)) :=
      hker _ (by rw [map_sub, hxe, sub_self])
    have h4 := Submodule.smul_mono_left hle h3
    simpa using add_mem h4 hx
  · intro x h
    show f (red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a (algebraMap (𝓞 F) O x) h)) = _
    rw [hequiv]
    exact fequiv x (red h)

end GlobalTheory.HTSummand
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystal_projective_over_tensor_ringOfIntegers : ∀ (F : Type) [Field F] [NumberField F] (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [Ring O] [Algebra (𝓞 F) O] (a : GlobalTheory.UPel.HT.OActN O A₀), letI := GlobalTheory.HTSummand.tensorModOf ((GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a).comp (algebraMap (𝓞 F) O)); Module.Projective (C ⊗[ℤ] 𝓞 F) (Crys (divided₂ hsq) (spMap π) A₀) := by
  atlas_forward_decl GlobalTheory.HTSummand.crys_projective
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTSummand

theorem exists_summand : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∃ E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E) ∧ (∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ E → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀
  obtain ⟨red, hfin, hproj, hsurj, hker, hcorr, hpush, E', M', hE'M', hE'⟩ :=
    GlobalTheory.CrysRed.exists_crysRed C C₀ π hπ hsq o₀.A o₀.ab D.O o₀.act
  haveI := hfin
  haveI := hproj
  obtain ⟨φ₀, hφ₀, huniq, hadj, φ', hφ', hrel⟩ := GlobalTheory.HTDefLift.exists_crysForm p D R b N C C₀ π hπ hsq tR o₀
  obtain ⟨hskew, hbij⟩ := GlobalTheory.HTPerf.skew_bijective p D R b N C C₀ π hπ hsq tR o₀ φ₀ hφ₀
  haveI : Nontrivial C₀ := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have ht : RingHom.ker π = ⊤ := eq_top_iff.2 fun x _ ↦ RingHom.mem_ker.2 (Subsingleton.elim _ _)
    rw [ht, ← Ideal.one_eq_top, one_pow] at hsq
    exact one_ne_zero hsq
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  have hlagr := GlobalTheory.HTLagr.fil_lagrangian p D R b N C₀ _ o₀ φ' (GlobalTheory.AbelianDim.exists_relDim C₀ o₀.A o₀.ab) hφ'
  have hlie := GlobalTheory.HTSummand.lie_mod_fil p D R b N C₀ (π.comp tR) _ (GlobalTheory.Cris.spMap_comp tR π).symm o₀
  have hprojF := GlobalTheory.T.crystal_projective_over_tensor_ringOfIntegers D.F C C₀ π hπ hsq o₀.A o₀.ab D.O o₀.act
  have hI2 : RingHom.ker π ^ 2 = ⊥ := hsq
  let F : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A) := (Fil o₀.A).comap red
  have hredI : ∀ x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)), red x = 0 := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr n _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · rw [LinearMap.map_smulₛₗ, RingHom.mem_ker.1 hr, zero_smul]
    · rw [map_add, hx, hy, add_zero]
  have hIF : RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)) ≤ F := fun x hx ↦ by
    show red x ∈ Fil o₀.A
    rw [hredI x hx]; exact zero_mem _
  have hFstab : ∀ (c : D.O), ∀ x ∈ F, GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act c x ∈ F := by
    intro c x hx
    show red _ ∈ Fil o₀.A
    rw [hpush]
    haveI := o₀.act.hom c
    exact push_mem_Fil (o₀.act.act c) hx
  have hFiso : ∀ x ∈ F, ∀ y ∈ F, φ₀ x y ∈ RingHom.ker π := by
    intro x hx y hy
    rw [RingHom.mem_ker, ← hrel x (red x) y (red y) ((hcorr _ _).2 rfl) ((hcorr _ _).2 rfl)]
    exact hlagr.1 _ hx _ hy
  have hFlagr : ∀ x, (∀ y ∈ F, φ₀ x y ∈ RingHom.ker π) → x ∈ F := by
    intro x hx
    show red x ∈ Fil o₀.A
    refine hlagr.2 _ fun z hz ↦ ?_
    obtain ⟨y, rfl⟩ := hsurj z
    rw [hrel x (red x) y (red y) ((hcorr _ _).2 rfl) ((hcorr _ _).2 rfl)]
    exact RingHom.mem_ker.1 (hx y hz)
  have hE'F : E' ⊔ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)) = F := by
    refine le_antisymm (sup_le (fun d hd ↦ (hE' _).2 ⟨d, hd, rfl⟩) hIF) fun x hx ↦ ?_
    obtain ⟨d, hd, he⟩ := (hE' (red x)).1 hx
    have hx' : x = d + (x - d) := by abel
    rw [hx']
    exact Submodule.add_mem_sup hd (hker _ (by rw [map_sub, he, sub_self]))
  have hFlie : ∀ d, GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ F →
      ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F),
        GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧
        d - ∑ i, w i ∈ F := by
    intro d hd
    have hd' : red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d)
        ∈ Fil o₀.A := hd
    rw [map_sub, LinearMap.map_smulₛₗ, hpush] at hd'
    obtain ⟨w₀, hw₀, hsum⟩ := hlie (red d) hd'
    choose w hw using fun i ↦ hsurj (w₀ i)
    refine ⟨w, fun i c ↦ ?_, ?_⟩
    · show red _ ∈ Fil o₀.A
      rw [map_sub, LinearMap.map_smulₛₗ, hpush, hw]
      exact hw₀ i c
    · show red _ ∈ Fil o₀.A
      rw [map_sub, map_sum]
      simp only [hw]
      exact hsum
  obtain ⟨E, ⟨M, hEM⟩, hEF, hstab, hiso, hlieE⟩ := GlobalTheory.T.exists_lagrangian_lift_lie_squareZero_harrisTaylor p D R b C (RingHom.ker π) hI2 tR
    (Crys (divided₂ hsq) (spMap π) o₀.A) (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act) hprojF φ₀ hskew hbij hadj
    F hIF hFstab hFiso hFlagr ⟨E', M', hE'M', hE'F⟩ hFlie
  refine ⟨E, ⟨M, hEM⟩, fun y ↦ ⟨fun hy ↦ ?_, fun ⟨d, hd, hc⟩ ↦ ?_⟩, fun c d hd ↦ hstab c d hd,
    fun φ hφ x hx y hy ↦ by rw [huniq φ hφ]; exact hiso x hx y hy, fun d hd ↦ hlieE d hd⟩
  · obtain ⟨x, rfl⟩ := hsurj y
    have hx : x ∈ F := hy
    rw [← hEF] at hx
    obtain ⟨d, hd, j, hj, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨d, hd, (hcorr _ _).2 (by rw [map_add, hredI j hj, add_zero])⟩
  · rw [← (hcorr d y).1 hc]
    have : d ∈ F := hEF ▸ Submodule.mem_sup_left hd
    exact this

end GlobalTheory.HTSummand
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_exists_isotropic_stable_summand : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∃ E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E) ∧ (∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ E → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E) := by
  atlas_forward_decl GlobalTheory.HTSummand.exists_summand
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.UPel.HT

theorem exists_sqZero_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ t)), ∃ o : GlobalTheory.UPel.HT.Obj b N t, Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)) := by
  intro p _ D R _ b N hN C C₀ _ _ _ _ π hπ hsq' t o₀
  have hsq : RingHom.ker π ^ 2 = 0 := by rw [hsq']; rfl
  obtain ⟨tR, rfl⟩ : ∃ tR : R →+* C, t = spMap tR :=
    ⟨(Spec.preimage t).hom, by simp [spMap]⟩
  obtain ⟨E, hEc, hEf, hEs, hEi, hEl⟩ := GlobalTheory.T.harrisTaylor_exists_isotropic_stable_summand p D R b N C C₀ π hπ hsq tR o₀
  obtain ⟨A, _, i, h, act, hA, hE, hact⟩ := GlobalTheory.T.harrisTaylor_exists_lift_orderAction_hodge_summand p D R b N C C₀ π hπ hsq tR o₀ E hEc hEf hEs
  haveI : IsCommMonObj A := hA.comm
  subst hE
  obtain ⟨P, φ₂, hP, r1, r2, hsym, hamp, hker, hros, hsq2, hpol⟩ :=
    GlobalTheory.T.harrisTaylor_exists_polarisation_bundle_lift p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEi
  obtain ⟨eta, e1, e2, e3, e4, e5⟩ := GlobalTheory.T.harrisTaylor_primeToP_level_lift_squareZero p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hN P φ₂ hP hsq2 hpol
  exact ⟨{ A := A
           ab := hA
           act := act
           P := P
           isLB := hP
           rig₁ := r1
           rig₂ := r2
           symm := hsym
           ample := hamp
           kerP := hker
           rosati := hros
           lie := fun R' _ β x hx v hv => GlobalTheory.T.harrisTaylor_lift_lie_of_hodge_summand_lie p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEl R' β x hx v hv
           lieRank := fun k _ _ x β hx j => GlobalTheory.T.harrisTaylor_lieMultiplicity_squareZeroLift p D R b N C C₀ π hπ hsq tR o₀ A i h act hact k x β hx j
           eta := eta
           eta_add := e1
           eta_lin := e2
           eta_ker := e3
           geom := e4 },
    ⟨{ φ := i
       φ₂ := φ₂
       cart := h
       sq := hsq2
       act := hact
       pol := hpol
       eta := e5 }⟩⟩

end GlobalTheory.UPel.HT
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_exists_lift_squareZero_artinian : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ t)), ∃ o : GlobalTheory.UPel.HT.Obj b N t, Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)) := by
  first | (exact @GlobalTheory.UPel.HT.exists_sqZero_lift) | (exact GlobalTheory.UPel.HT.exists_sqZero_lift) | (intros; apply GlobalTheory.UPel.HT.exists_sqZero_lift <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem GlobalTheory.UPel.HT.obj_lift_sqZero : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (A₁ A₀ : Type) [CommRing A₁] [CommRing A₀] [IsLocalRing A₁] [IsArtinianRing A₁] (π : A₁ →+* A₀) (β : R →+* A₁), Function.Surjective π → RingHom.ker π * RingHom.ker π = ⊥ → ∀ o : Obj b N (spMap (π.comp β)), ∃ o' : Obj b N (spMap β), Nonempty (ObjMap o o' (spMap π)) := by
  intro p _ D R _ b N _ hN A₁ A₀ _ _ _ _ π β hπ hk o
  have hc : spMap (π.comp β) = spMap π ≫ spMap β := by
    simp only [spMap, Sp, CommRingCat.ofHom_comp, Spec.map_comp]
  have hk2 : RingHom.ker π ^ 2 = ⊥ := by rw [pow_two]; exact hk
  revert o
  rw [hc]
  intro o
  first
  | exact GlobalTheory.T.harrisTaylor_exists_lift_squareZero_artinian p D R b N hN A₁ A₀ π hπ hk2 (spMap β) o
  | exact GlobalTheory.T.harrisTaylor_exists_lift_squareZero_artinian p D R b N A₁ A₀ π hπ hk2 (spMap β) o
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_formally_smooth_squareZero_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (A₁ A₀ : Type) [CommRing A₁] [CommRing A₀] [IsLocalRing A₁] [IsArtinianRing A₁] (π : A₁ →+* A₀) (β : R →+* A₁), Function.Surjective π → RingHom.ker π * RingHom.ker π = ⊥ → ∀ o : Obj b N (spMap (π.comp β)), ∃ o' : Obj b N (spMap β), Nonempty (ObjMap o o' (spMap π)) := by
  first | (exact @GlobalTheory.UPel.HT.obj_lift_sqZero) | (exact GlobalTheory.UPel.HT.obj_lift_sqZero) | (intros; apply GlobalTheory.UPel.HT.obj_lift_sqZero <;> assumption)
end
