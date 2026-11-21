import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.MkEqZeroOfTriv
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.H1OnPointsEqZeroOfIsIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTangentEqOfCrystallineValuesEq
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RestrictTrivEqZero
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.PerfectRing
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CrystallineDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamStructureToFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidOfFreeOfCrystallineDeRham

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

theorem rigid {S : Scheme.{0}} {G : Over S} [GrpObj G] (hG : IsAbelianScheme G) {Z : Scheme.{0}} (e : S ⟶ G.left)
    (he : e ≫ G.hom = 𝟙 S) (f : G.left ⟶ Z) (k : S ⟶ Z) (hk : ∀ y, f y = k (G.hom y)) : f = G.hom ≫ e ≫ f := by
  have := hG.proper
  refine Scheme.hom_ext_of_forall _ _ fun y ↦ ?_
  obtain ⟨V, hV, h⟩ := GlobalTheory.local_rigidity _ _ _ G.hom e f he inferInstance
    (GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.globalFns_holds G hG) (G.hom y) (k (G.hom y))
    (fun x hx ↦ by rw [hk, hx])
  exact ⟨G.hom ⁻¹ᵁ V, hV, h⟩

theorem epsRed_surjective (R : Type) [CommRing R] : Surjective (GlobalTheory.DeRham.epsRed R) := by
  refine ⟨fun q ↦ ⟨spMap (algebraMap R (DualNumber R)) q, ?_⟩⟩
  refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
  change algebraMap R (DualNumber R) c.fst ∈ q.asIdeal ↔ c ∈ q.asIdeal
  have hn : c - algebraMap R (DualNumber R) c.fst ∈ q.asIdeal := by
    refine q.isPrime.mem_of_pow_mem 2 ?_
    have : (c - algebraMap R (DualNumber R) c.fst) ^ 2 = 0 := by
      ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; exact zero_mem _
  exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩

theorem epsRed_hom (R : Type) [CommRing R] : GlobalTheory.DeRham.epsRed R ≫ (epsR R).hom = 𝟙 _ := by
  change spMap _ ≫ spMap _ = _
  rw [← GlobalTheory.Cris.spMap_comp]
  exact GlobalTheory.Cris.spMap_id R

theorem cube_family (hC : CubeTheorem) {S : Scheme.{0}} {A T : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {M : LB (A ⊗ T).left} (hM : M.IsLB) {Y : Over S} (a a' b : Y ⟶ A) (t : Y ⟶ T) :
    evc hM (a * a' * b) t - evc hM (a * a') t - evc hM b t + evc hM 1 t =
      (evc hM (a * b) t - evc hM a t - evc hM b t + evc hM 1 t) +
        (evc hM (a' * b) t - evc hM a' t - evc hM b t + evc hM 1 t) := by
  obtain ⟨A', _, φ, hφ⟩ : ∃ (A' : Over T.left) (_ : GrpObj A') (φ : A'.left ⟶ A.left), IsGrpPullback A' A T.hom φ :=
    ⟨_, inferInstance, _, isGrpPullback_pullback A T.hom⟩
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hφ
  let W : Over S := Over.mk (A'.hom ≫ T.hom)
  let j : W ⟶ A ⊗ T := lift (Over.homMk φ hφ.1.w) (Over.homMk A'.hom rfl)
  have j₁ : j.left ≫ (fst A T).left = φ := lift_left_fst _ _
  have j₂ : j.left ≫ (snd A T).left = A'.hom := lift_left_snd _ _
  have hs : t.left ≫ T.hom = Y.hom := Over.w t
  let q : (Y ⟶ A) → (Over.mk t.left ⟶ A') := fun a ↦ liftPt hφ t.left a.left ((Over.w a).trans hs.symm)
  have q₁ : ∀ a, (q a).left ≫ φ = a.left := fun a ↦ liftPt_left _ _ _ _
  have qm : ∀ a b, q a * q b = q (a * b) := fun a b ↦ pt_ext hφ
    ((mul_left_comp hφ hs (x₀ := (a : Over.mk Y.hom ⟶ A)) (y₀ := (b : Over.mk Y.hom ⟶ A)) (q₁ a) (q₁ b)).trans
      (q₁ (a * b)).symm)
  have qo : (1 : Over.mk t.left ⟶ A') = q 1 := pt_ext hφ ((one_left_comp hφ hs).trans (q₁ 1).symm)
  have hM' : (M.pull j.left).IsLB := pull_isLB hM _
  have ev : ∀ a, GlobalTheory.CechPic.pull (q a).left (cls (X := A'.left) _ hM') = evc hM a t := fun a ↦ by
    have e : (q a).left ≫ j.left = (lift a t).left := left_ext
      (((Category.assoc _ _ _).trans (congrArg _ j₁)).trans ((q₁ a).trans (lift_left_fst a t).symm))
      (((Category.assoc _ _ _).trans (congrArg _ j₂)).trans ((Over.w (q a)).trans (lift_left_snd a t).symm))
    exact (pull_comp _ _ _).symm.trans (congrArg (fun u ↦ GlobalTheory.CechPic.pull u (cls M hM)) e)
  have e := GlobalTheory.CubeDual.lam_mul_left hC hA' (L := M.pull j.left) hM' (q a) (q a') (q b)
  simp only [lam, qm, qo, ev] at e
  exact e

theorem additive_eps (hC : CubeTheorem) {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hP : IsDual A B P) {M : LB (A ⊗ epsR R).left} (hM : M.IsLB) (h₀ : ∀ (Y : Over (Sp R)) (t : Y ⟶ epsR R), evc hM (1 : Y ⟶ A) t = 0) (h₁ : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ epsR R), t.left = Y.hom ≫ GlobalTheory.DeRham.epsRed R → evc hM a t = 0) : IsAdditive M := by
  let Λ : ∀ {Y : Over (Sp R)}, (Y ⟶ A) → (Y ⟶ A ⊗ epsR R) → Pic Y.left := fun a y ↦
    evc hM (a * (y ≫ fst _ _)) (y ≫ snd _ _) - evc hM a (y ≫ snd _ _) - evc hM (y ≫ fst _ _) (y ≫ snd _ _) +
      evc hM 1 (y ≫ snd _ _)
  obtain ⟨N, hN, eN⟩ := cls_surj (Λ (fst A (A ⊗ epsR R)) (snd A (A ⊗ epsR R)))
  have vN : ∀ {Y : Over (Sp R)} (a : Y ⟶ A) (y : Y ⟶ A ⊗ epsR R), evc hN a y = Λ a y := fun a y ↦ by
    rw [evc, eN]
    simp only [Λ, map_add, map_sub, pull_evc, MonObj.comp_mul, MonObj.comp_one, lift_fst, lift_snd_assoc]
  have aN : IsAdditive N := (isAdditive_iff hN).2 fun Y a a' y ↦ by
    rw [vN, vN, vN]
    exact cube_family hC hA hM a a' _ _
  obtain ⟨x, hx, -⟩ := hP.univ _ N hN aN
  have ex : cls N hN = evc hP.isLB (fst _ _) (snd _ _ ≫ x) := (cls_eq_iff hN (pull_isLB hP.isLB _)).2 hx
  have one : ∀ {Y : Over (Sp R)} (y : Y ⟶ A ⊗ epsR R), Λ (fst A Y) (snd A Y ≫ y) = 0 → y ≫ x = 1 := fun y h ↦
    hP.eq_one _ ((triv_ev_iff hP.isLB _ _).2 (by
      rw [← Category.assoc, ← GlobalTheory.BirigidLift.evc_of_cls hP.isLB hN ex, vN, h]))
  let z : A ⟶ epsR R := Over.homMk (A.hom ≫ GlobalTheory.DeRham.epsRed R) (by
    rw [Category.assoc, epsRed_hom, Category.comp_id])
  have x₁ : lift (𝟙 A) z ≫ x = 1 := one _ (by
    have hz : ((snd A A ≫ lift (𝟙 A) z) ≫ snd _ _).left = (A ⊗ A).hom ≫ GlobalTheory.DeRham.epsRed R := by
      rw [Category.assoc, lift_snd, Over.comp_left, ← Over.w (snd A A), Category.assoc]
      rfl
    simp only [Λ, h₁ _ _ _ hz, sub_zero, add_zero])
  have x₂ : lift 1 (𝟙 (epsR R)) ≫ x = 1 := one _ (by
    simp only [Λ, Category.assoc, lift_fst, lift_snd, MonObj.comp_one, _root_.mul_one, sub_self, h₀, sub_zero,
      add_zero])
  have x0 : x = 1 := by
    obtain ⟨A', _, φ, hφ⟩ : ∃ (A' : Over (epsR R).left) (_ : GrpObj A') (φ : A'.left ⟶ A.left),
        IsGrpPullback A' A (epsR R).hom φ := ⟨_, inferInstance, _, isGrpPullback_pullback A (epsR R).hom⟩
    have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hφ
    let W : Over (Sp R) := Over.mk (A'.hom ≫ (epsR R).hom)
    let j : W ⟶ A ⊗ epsR R := lift (Over.homMk φ hφ.1.w) (Over.homMk A'.hom rfl)
    have j₁ : j.left ≫ (fst A (epsR R)).left = φ := lift_left_fst _ _
    have j₂ : j.left ≫ (snd A (epsR R)).left = A'.hom := lift_left_snd _ _
    have lf : ∀ {Y : Over (Sp R)} (y : Y ⟶ A ⊗ epsR R), ∃ u : Y.left ⟶ A'.left,
        u ≫ φ = (y ≫ fst _ _).left ∧ u ≫ A'.hom = (y ≫ snd _ _).left ∧ u ≫ j.left = y.left := fun y ↦ by
      have w : (y ≫ fst _ _).left ≫ A.hom = (y ≫ snd _ _).left ≫ (epsR R).hom :=
        (Over.w _).trans (Over.w _).symm
      refine ⟨hφ.1.lift _ _ w, hφ.1.lift_fst _ _ _, hφ.1.lift_snd _ _ _, left_ext ?_ ?_⟩
      · exact ((Category.assoc _ _ _).trans (congrArg _ j₁)).trans (hφ.1.lift_fst _ _ _)
      · exact ((Category.assoc _ _ _).trans (congrArg _ j₂)).trans (hφ.1.lift_snd _ _ _)
    obtain ⟨i, i₁, i₂, i₃⟩ := lf (lift (𝟙 A) z)
    obtain ⟨e, -, e₂, e₃⟩ := lf (lift 1 (𝟙 (epsR R)))
    obtain ⟨u, -, u₂, u₃⟩ := lf (𝟙 _)
    rw [lift_fst] at i₁
    rw [lift_snd] at i₂ e₂
    have i₂' : i ≫ A'.hom = A.hom ≫ GlobalTheory.DeRham.epsRed R := i₂
    have pb : IsPullback i A.hom A'.hom (GlobalTheory.DeRham.epsRed R) := by
      refine IsPullback.of_right ?_ i₂' hφ.1
      rw [i₁, epsRed_hom]
      haveI : IsIso (Over.Hom.left (𝟙 A)) := by rw [Over.id_left]; infer_instance
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    have hi : Surjective i := MorphismProperty.of_isPullback (P := @Surjective) pb.flip (epsRed_surjective R)
    let k : (epsR R).left ⟶ B.left := (1 : epsR R ⟶ B).left
    have ik : i ≫ j.left ≫ x.left = i ≫ A'.hom ≫ k := by
      rw [← Category.assoc, i₃, ← Category.assoc, i₂, ← Over.comp_left, x₁, ← Over.comp_left, MonObj.comp_one]
    have rg := rigid hA' e e₂ (j.left ≫ x.left) k fun y ↦ by
      obtain ⟨y, rfl⟩ := hi.surj y
      exact congrArg (fun u ↦ u y) ik
    have ek : e ≫ j.left ≫ x.left = k := by
      rw [← Category.assoc, e₃, ← Over.comp_left, x₂]
    rw [ek] at rg
    apply Over.OverMorphism.ext
    have h := congrArg (u ≫ ·) rg
    simp only [← Category.assoc] at h
    rw [u₃, u₂] at h
    refine ((Category.id_comp _).symm.trans h).trans ?_
    rw [← Over.comp_left, MonObj.comp_one]
  refine (isAdditive_iff hM).2 fun Y a a' t ↦ ?_
  have h := GlobalTheory.BirigidLift.evc_of_cls hP.isLB hN ex a (lift a' t)
  rw [x0, MonObj.comp_one, evc_one_right hP.isLB hP.zero, vN] at h
  simp only [Λ, lift_fst, lift_snd, h₀, add_zero] at h
  rw [← sub_eq_zero, ← h]
  abel

end CrystallinePoints.Pd
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

open GlobalTheory.AbLaw GlobalTheory.GrpTangent TensorProduct
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R]

def ResSurj.{u} : Prop :=
  ∀ (R : Type) [CommRing R] (H : Type 1) [AddCommGroup H] [Module R H] (M : Type u) [AddCommGroup M] [Module R M]
    (g : ℕ) (F N : Submodule R H), IsCompl F N → Module.Finite R H → Module.Projective R H →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk H p = 2 * g) → Module.Finite R F → Module.Projective R F →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk F p = g) → Module.Finite R M → Module.Projective R M →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk M p = g) → ∀ gam : H →ₗ[R] M,
    (∀ m : Ideal R, m.IsMaximal → ∀ q : H, gam q ∈ m • (⊤ : Submodule R M) → q ∈ F ⊔ m • (⊤ : Submodule R H)) →
    Function.Surjective gam

theorem cst_top {Y : Scheme.{0}} (f : Y ⟶ Sp R) (r : R) :
    cst f ⊤ r = f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := rs_self _ _

theorem cst_comp {Y Y' : Scheme.{0}} (ψ : Y' ⟶ Y) (f : Y ⟶ Sp R) (r : R) :
    cst (ψ ≫ f) ⊤ r = ψ.appTop.hom (cst f ⊤ r) := by
  rw [cst_top, cst_top, Scheme.Hom.comp_appTop]; rfl

theorem cst_spMap {R' : Type} [CommRing R'] {Y : Scheme.{0}} (t : Y ⟶ Sp R') (ρ : R →+* R') (r : R) :
    cst (t ≫ spMap ρ) ⊤ r = cst t ⊤ (ρ r) := by
  rw [cst_top, cst_top, Scheme.Hom.comp_appTop]
  have e := congrArg (fun q ↦ q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))
  exact congrArg t.appTop.hom e.symm

section Mod

variable {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem pull_w {R' : Type} [CommRing R'] {σ : R →+* R'} {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left}
    (h : IsGrpPullback A' A (spMap σ) φ) : φ ≫ A.hom ≫ 𝟙 _ = (A'.hom ≫ 𝟙 _) ≫ spMap σ := by
  rw [Category.comp_id, Category.comp_id]; exact h.1.w

theorem mem_sup_of_pullP (hB : AbelianDeRham.BaseChange) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (m : Ideal R) {A' : Over (Sp (R ⧸ m))} [GrpObj A']
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap (algebraMap R (R ⧸ m))) φ) (q : primDR A)
    (hq : pullP (pull_w h) (toP _ q.1) = 0) : q ∈ PrimitiveSubmodule A ⊔ m • (⊤ : Submodule R (primDR A)) := by
  obtain ⟨hbc, hF⟩ := hB R A g hA hg (R ⧸ m) A' φ h
  have h1 : (AbelianDeRham.bcMor h).pull q ∈ PrimitiveSubmodule A' :=
    (toP_eq_zero_iff _).1 ((pullP_toP (AbelianDeRham.bcMor h).isMor q.1).symm.trans hq)
  rw [hF] at h1
  have h2 : ∀ z ∈ Submodule.span (R ⧸ m) ((AbelianDeRham.bcMor h).pull '' (PrimitiveSubmodule A)),
      ∃ f ∈ PrimitiveSubmodule A, (AbelianDeRham.bcMor h).pull f = z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, zero_mem _, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, add_mem ha hb, map_add _ _ _⟩
    | smul r x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      exact ⟨r • a, Submodule.smul_mem _ _ ha, LinearMap.map_smulₛₗ _ _ _⟩
  obtain ⟨f, hf, e⟩ := h2 _ h1
  have h3 : (1 : R ⧸ m) ⊗ₜ[R] (q - f) = 0 := hbc.1 (by
    rw [liftSemi_tmul, one_smul, map_sub, e, sub_self, map_zero])
  have h4 := congrArg (TensorProduct.quotTensorEquivQuotSMul (primDR A) m) h3
  rw [map_zero, ← map_one (Ideal.Quotient.mk m), TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul,
    Submodule.Quotient.mk_eq_zero] at h4
  rw [← add_sub_cancel f q]
  exact Submodule.add_mem_sup hf h4

theorem surj_of_gamma (hR : ResSurj.{0}) (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge)
    (hB : AbelianDeRham.BaseChange) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {M : Type} [AddCommGroup M] [Module R M] (h₁ : Module.Finite R M) (h₂ : Module.Projective R M)
    (h₃ : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = g) (gam : H1OnPoints (A.hom ≫ 𝟙 _) →ₗ[R] M)
    (hgam : Function.Injective gam)
    (hm : ∀ (m : Ideal R) (A' : Over (Sp (R ⧸ m))) [GrpObj A'] (φ : A'.left ⟶ A.left)
      (h : IsGrpPullback A' A (spMap (algebraMap R (R ⧸ m))) φ) (c : H1OnPoints (A.hom ≫ 𝟙 _)),
      gam c ∈ m • (⊤ : Submodule R M) → pullP (pull_w h) c = 0) :
    Function.Surjective (toP (A.hom ≫ 𝟙 _)) := by
  obtain ⟨a₁, a₂, a₃⟩ := hF.prim hA hg
  obtain ⟨-, ⟨N, hN⟩, b₁, b₂, b₃⟩ := hH R A g hA hg
  have hs := hR R (primDR A) M g (PrimitiveSubmodule A) N hN a₁ a₂ a₃ b₁ b₂ b₃ h₁ h₂ h₃
    (gam ∘ₗ toP _ ∘ₗ (primDR A).subtype) fun m _ q hq ↦
      mem_sup_of_pullP hB hA hg m (isGrpPullback_pullback A _) q (hm m _ _ (isGrpPullback_pullback A _) _ hq)
  intro c
  obtain ⟨q, hq⟩ := hs (gam c)
  exact ⟨q.1, hgam hq⟩

end Mod

section Gamma

variable {E : ETy} (hE : IsE @E) {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem E_congr {X Y : Scheme.{0}} (s : X ⟶ Sp R) (c : H1OnPoints s) {π π' : Y ⟶ X} {ν ν' : Γ(Y, ⊤)} (h : ν * ν = 0)
    (h' : ν' * ν' = 0) (e : π = π') (e' : ν = ν') : E s c π ν h = E s c π' ν' h' := by
  subst e e'; rfl

include hE in
theorem E_zero {X Y : Scheme.{0}} (s : X ⟶ Sp R) (π : Y ⟶ X) (ν : Γ(Y, ⊤)) (h : ν * ν = 0) : E s 0 π ν h = 0 := by
  have e := hE.add s 0 0 π ν h
  rw [add_zero] at e
  exact left_eq_add.1 e

variable (E) in

def Ec (c : H1OnPoints (A.hom ≫ 𝟙 _)) {Y : Over (Sp R)} (a : Y ⟶ A) (t : Y ⟶ epsR R) : Pic Y.left :=
  E (A.hom ≫ 𝟙 _) c a.left (epsFn (R := R) t.left) (epsFn_sq _)

omit [GrpObj A] in
include hE in
theorem pull_Ec (c : H1OnPoints (A.hom ≫ 𝟙 _)) {Y Z : Over (Sp R)} (u : Z ⟶ Y) (a : Y ⟶ A) (t : Y ⟶ epsR R) :
    GlobalTheory.CechPic.pull u.left (Ec E c a t) = Ec E c (u ≫ a) (u ≫ t) :=
  hE.nat _ c a.left _ _ u.left _ _ (cst_comp u.left t.left _)

include hE in
theorem Ec_one (c : H1OnPoints (A.hom ≫ 𝟙 _)) {Y : Over (Sp R)} (t : Y ⟶ epsR R) : Ec E c (1 : Y ⟶ A) t = 0 := by
  have h : (η[A].left : Sp R ⟶ A.left) ≫ A.hom ≫ 𝟙 _ = 𝟙 (Sp R) ≫ spMap (RingHom.id R) := by
    rw [Category.comp_id, GlobalTheory.Cris.spMap_id, Category.comp_id]; exact Over.w η[A]
  have e := hE.chg h c Y.hom (epsFn (R := R) t.left) (epsFn_sq _)
  haveI : IsIso (𝟙 (Sp R)) := IsIso.id _
  rw [H1OnPoints_eq_zero_of_isIso _ (pullP h c), E_zero hE] at e
  exact e.symm

omit [GrpObj A] in
include hE in
theorem Ec_red (c : H1OnPoints (A.hom ≫ 𝟙 _)) {Y : Over (Sp R)} (a : Y ⟶ A) (t : Y ⟶ epsR R)
    (ht : t.left = Y.hom ≫ GlobalTheory.DeRham.epsRed R) : Ec E c a t = 0 := by
  refine hE.zero _ c _ _ _ ?_
  rw [epsFn, ht]
  exact (cst_spMap Y.hom _ _).trans (map_zero _)

omit [GrpObj A] in
include hE in
theorem Ec_smul (c : H1OnPoints (A.hom ≫ 𝟙 _)) (r : R) {Y : Over (Sp R)} (a : Y ⟶ A) (t : Y ⟶ epsR R) :
    Ec E (r • c) a t = Ec E c a (t ≫ GlobalTheory.GrpTangent.epsScale r) := by
  refine hE.smul _ c r _ _ _ _ _ ?_
  have e : a.left ≫ A.hom ≫ 𝟙 _ = t.left ≫ spMap (algebraMap R (DualNumber R)) := by
    rw [Category.comp_id, Over.w a]; exact (Over.w t).symm
  rw [e]
  refine (cst_spMap (R := DualNumber R) t.left (epsScaleR r) _).trans ?_
  rw [cst_spMap, epsFn, ← map_mul]
  congr 1
  ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

variable {P : LB (A ⊗ B).left} (hP : IsDual A B P)
  (hadd : ∀ {M : LB (A ⊗ epsR R).left} (hM : M.IsLB),
    (∀ (Y : Over (Sp R)) (t : Y ⟶ epsR R), evc hM (1 : Y ⟶ A) t = 0) →
    (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ epsR R), t.left = Y.hom ≫ GlobalTheory.DeRham.epsRed R → evc hM a t = 0) →
    IsAdditive M)

include hE hP hadd in
theorem exists_pt (c : H1OnPoints (A.hom ≫ 𝟙 _)) : ∃ x : epsR R ⟶ B, IsTangent x ∧
    ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ epsR R), evc hP.isLB a (t ≫ x) = Ec E c a t := by
  obtain ⟨M, hM, eM⟩ := cls_surj (Ec E c (fst A (epsR R)) (snd A (epsR R)))
  have k : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ epsR R), evc hM a t = Ec E c a t := fun Y a t ↦ by
    rw [evc, eM, pull_Ec hE, lift_fst, lift_snd]
  obtain ⟨x, hx, -⟩ := hP.univ _ M hM (hadd hM (fun Y t ↦ (k Y _ t).trans (Ec_one hE c t))
    fun Y a t ht ↦ (k Y a t).trans (Ec_red hE c a t ht))
  have e : cls M hM = evc hP.isLB (fst A _) (snd A _ ≫ x) := (cls_eq_iff hM (pull_isLB hP.isLB _)).2 hx
  have k' : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ epsR R), evc hP.isLB a (t ≫ x) = Ec E c a t := fun Y a t ↦ by
    rw [← k, evc, evc, e, pull_evc, lift_fst, lift_snd_assoc, evc]
  refine ⟨x, (isTangent_iff x).2 (hP.eq_one _ ((triv_ev_iff hP.isLB _ _).2 ?_)), k'⟩
  rw [← Category.assoc, k']
  refine Ec_red hE c _ _ ?_
  rw [Over.comp_left, ← Over.w (snd A (𝟙_ (Over (Sp R))))]
  exact congrArg (· ≫ GlobalTheory.DeRham.epsRed R) (Category.comp_id _).symm

include hE hP hadd in
theorem surj_of_isDual' (hR : ResSurj.{0}) (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge)
    (hB : AbelianDeRham.BaseChange) {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (hA' : IsAbelianScheme B) (hg' : SmoothOfRelativeDimension g B.hom) (hsw : IsAdditive (swap P)) :
    Function.Surjective (toP (A.hom ≫ 𝟙 _)) := by
  haveI := hA'.comm
  choose x hx k using exists_pt hE hP hadd
  let gam : H1OnPoints (A.hom ≫ 𝟙 _) →ₗ[R] GlobalTheory.Serre.Lie (GlobalTheory.Serre.intAct B) :=
    { toFun := fun c ↦ GlobalTheory.Serre.Lie.mk _ (x c) (hx c)
      map_add' := fun c c' ↦ GlobalTheory.Serre.Lie.ext (GlobalTheory.BirigidLift.dual_ext hP (by
        change evc _ _ (_ ≫ x (c + c')) = evc _ _ (_ ≫ (x c * x c'))
        rw [MonObj.comp_mul, (GlobalTheory.BirigidLift.isAdditive_swap_iff hP.isLB).1 hsw, k, k, k]
        exact hE.add _ _ _ _ _ _))
      map_smul' := fun r c ↦ GlobalTheory.Serre.Lie.ext (GlobalTheory.BirigidLift.dual_ext hP (by
        change evc _ _ (_ ≫ x (r • c)) = evc _ _ (_ ≫ GlobalTheory.GrpTangent.epsScale r ≫ x c)
        rw [← Category.assoc, k, k, Ec_smul hE])) }
  obtain ⟨l₁, l₂, l₃⟩ := GlobalTheory.LieInj.lie_finite_projective B g hg' (GlobalTheory.Serre.intAct B)
  have pb : ∀ {C : Type} [CommRing C] (G : Over (Sp C)), IsPullback (fst G (epsR C)).left (snd G (epsR C)).left
      (G.hom ≫ 𝟙 _) (spMap (algebraMap C (DualNumber C))) := fun G ↦ by
    rw [Category.comp_id]; exact IsPullback.of_hasPullback _ _
  refine surj_of_gamma hR hF hH hB hA hg l₁ l₂ l₃ gam ((injective_iff_map_eq_zero _).2 fun c hc ↦ ?_)
    fun m A' _ φ h c hc ↦ ?_
  · have e : x c = 1 := congrArg GlobalTheory.Serre.Lie.hom hc
    refine hE.inj _ c _ _ (pb A) ((k _ _ _ _).symm.trans ?_)
    rw [e, MonObj.comp_one, evc_one_right hP.isLB hP.zero]
  · let σ := algebraMap R (R ⧸ m)
    let Y : Over (Sp R) := Over.mk ((A' ⊗ epsR (R ⧸ m)).hom ≫ spMap σ)
    let a : Y ⟶ A := Over.homMk ((fst A' (epsR (R ⧸ m))).left ≫ φ) (by
      change (_ ≫ φ) ≫ A.hom = _ ≫ spMap σ
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
    have hc' : (Chart.dualMapR σ).comp (algebraMap R (DualNumber R)) =
        (algebraMap (R ⧸ m) (DualNumber (R ⧸ m))).comp σ := RingHom.ext fun r ↦ by
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
    let t : Y ⟶ epsR R := Over.homMk ((snd A' (epsR (R ⧸ m))).left ≫ spMap (Chart.dualMapR σ)) (by
      change (_ ≫ _) ≫ spMap _ = _ ≫ spMap σ
      rw [Category.assoc, ← GlobalTheory.Cris.spMap_comp, hc', GlobalTheory.Cris.spMap_comp, ← Category.assoc]
      exact congrArg (· ≫ spMap σ) (Over.w (snd A' (epsR (R ⧸ m)))))
    have ht : t ≫ (gam c).hom = 1 := by
      refine Submodule.smul_induction_on (p := fun v ↦ t ≫ GlobalTheory.Serre.Lie.hom v = 1) hc (fun r hr v _ ↦ ?_)
        fun v w hv hw ↦ by rw [GlobalTheory.Serre.Lie.hom_add, MonObj.comp_mul, hv, hw, _root_.mul_one]
      have e : t ≫ GlobalTheory.GrpTangent.epsScale r = t ≫ GlobalTheory.GrpTangent.epsScale 0 := by
        refine Over.OverMorphism.ext ?_
        change (_ ≫ spMap _) ≫ spMap (epsScaleR r) = (_ ≫ spMap _) ≫ spMap (epsScaleR 0)
        rw [Category.assoc, Category.assoc, ← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp]
        congr 2
        have hr' : σ r = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hr
        refine RingHom.ext fun z ↦ ?_
        ext <;> simp [Chart.dualMapR, epsScaleR, hr']
      rw [GlobalTheory.Serre.Lie.hom_smul, ← Category.assoc, e, Category.assoc, epsScale_zero_comp v.isTangent,
        MonObj.comp_one]
    have e0 : Ec E c a t = 0 := by
      rw [← k]
      exact (congrArg (evc hP.isLB a) ht).trans (evc_one_right hP.isLB hP.zero a)
    refine hE.inj _ _ _ _ (pb A') ((hE.chg (pull_w h) c _ _ _).trans (Eq.trans (E_congr _ c _ _ rfl ?_) e0))
    refine Eq.trans ?_ (cst_spMap (R := DualNumber R) _ (Chart.dualMapR σ) _).symm
    rw [epsFn]
    congr 1
    ext <;> simp [Chart.dualMapR]

end Gamma

end CrystallinePoints.Pd
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

section Alg

theorem key₁ {B B' : Type} [CommRing B] [CommRing B'] {n : ℕ} (ρ : B →+* B') (fφ : B) (fc fψ : B')
    (aφ gm : Fin n → B) (ac aψ bψ gm' : Fin n → B') (h1 : ρ fφ - fc + fψ = ∑ k, ρ (aφ k) * bψ k)
    (h2 : ∀ k, ac k = ρ (aφ k) + aψ k) (h3 : ∀ k, gm' k = ρ (gm k) + bψ k) :
    fc + ∑ k, ac k * gm' k = ρ (fφ + ∑ k, aφ k * gm k) + (fψ + ∑ k, aψ k * gm' k) := by
  have e : ∀ k, ac k * gm' k = ρ (aφ k) * ρ (gm k) + ρ (aφ k) * bψ k + aψ k * gm' k := by
    intro k
    linear_combination gm' k * h2 k + ρ (aφ k) * h3 k
  have hs := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => e k)
  simp only [Finset.sum_add_distrib] at hs
  rw [map_add, map_sum]
  simp only [map_mul]
  linear_combination hs - h1

theorem key₂ {B B' : Type} [CommRing B] [CommRing B'] {n : ℕ} (ρ : B →+* B') (fθ : B) (fc f₂ f₁ fθ' : B')
    (aθ gm₀ : Fin n → B) (b₂ a₁ bθ' a₂ aθ' gm₂ gm₁ t : Fin n → B')
    (h1 : ρ fθ - fc + f₂ = ∑ k, ρ (aθ k) * b₂ k) (h2 : f₁ - fc + fθ' = ∑ k, a₁ k * bθ' k)
    (h3 : ∀ k, ρ (aθ k) + a₂ k = a₁ k + aθ' k) (h4 : ∀ k, gm₂ k = ρ (gm₀ k) + b₂ k)
    (h5 : ∀ k, t k + gm₂ k = gm₁ k + bθ' k) :
    (fθ' + ∑ k, aθ' k * gm₂ k) - ρ (fθ + ∑ k, aθ k * gm₀ k) =
      (f₂ + ∑ k, a₂ k * gm₂ k) - (f₁ + ∑ k, a₁ k * gm₁ k) + ∑ k, t k * a₁ k := by
  have e : ∀ k, aθ' k * gm₂ k - ρ (aθ k) * ρ (gm₀ k) - a₂ k * gm₂ k + a₁ k * gm₁ k - t k * a₁ k
      = ρ (aθ k) * b₂ k - a₁ k * bθ' k := by
    intro k
    linear_combination (-gm₂ k) * h3 k + ρ (aθ k) * h4 k - a₁ k * h5 k
  have hs := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => e k)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hs
  rw [map_add, map_sum]
  simp only [map_mul]
  linear_combination hs + h2 - h1

theorem exists_factor' {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) (x : M →ₗ[R] R)
    (h : ∀ m, f m = 0 → x m = 0) : ∃ x' : N →ₗ[R] R, ∀ m, x' (f m) = x m := by
  have hk : LinearMap.ker f ≤ LinearMap.ker x := fun m hm => h m hm
  refine ⟨(LinearMap.ker f).liftQ x hk ∘ₗ (f.quotKerEquivOfSurjective hf).symm.toLinearMap, fun m => ?_⟩
  have hm : (f.quotKerEquivOfSurjective hf).symm (f m) = Submodule.Quotient.mk m := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp [hm]

end Alg

section Cochain

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

def v1 (f : C1 (FP s)) {S S' : Pt s} (φ : S ⟶ S') : S'.B := f S S' φ

theorem cocycle_value_comp (f : Z1 (FP s)) {S S' S'' : Pt s} (φ : S ⟶ S') (ψ : S' ⟶ S'') (χ : S ⟶ S'')
    (e : ∀ b, χ.ρ b = ψ.ρ (φ.ρ b)) : v1 f.1 χ = ψ.ρ (v1 f.1 φ) + v1 f.1 ψ := by
  have hχ : χ = φ ≫ ψ := by
    obtain ⟨ρχ, hχpt⟩ := χ
    have hρ : ρχ = (φ ≫ ψ).ρ := AlgHom.ext e
    subst hρ
    rfl
  subst hχ
  exact f.2 φ ψ

theorem cocycle_value_sum {n : ℕ} (t : Fin n → R) (z : Fin n → Z1 (FP s)) {S S' : Pt s} (φ : S ⟶ S') :
    v1 (∑ k, t k • z k).1 φ = ∑ k, algebraMap R S'.B (t k) * v1 (z k).1 φ := by
  unfold v1
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Algebra.smul_def _ _

theorem pull2_chern_class_eq_zero {L : LB X} (hL : L.IsLB) {z : SecondDeRham s} (hz : IsChern (dp0 R) s L z) :
    (toPC s).pull2 z = 0 := by
  have hT : ∀ P : Pt s, IsTriv s ((toPC s).G.obj P) := fun P => rfl
  let n : CoefMap (RingHom.id R) ((IsTriv s).ι ⋙ O (dp0 R) s) (FP s) :=
    { G := ObjectProperty.lift (IsTriv s) (toPC s).G hT
      α := fun P => RingHom.id P.B
      naturality := fun φ b => (toPC s).naturality φ b
      smul := fun P r b => (toPC s).smul P r b }
  have he : toPC s = (CoefMap.restrict (O (dp0 R) s) (IsTriv s).ι).comp n := rfl
  rw [he, CoefMap.pullCohomologyTwo_comp, GlobalTheory.CompanionTheory.PdChern.restrict_triv_eq_zero R X s L hL z hz, map_zero]

variable {W Y : Scheme.{0}} {sW : W ⟶ Sp R} {sY : Y ⟶ Sp R} {p : W ⟶ Y}
  (hp : p ≫ sY = sW ≫ spMap (RingHom.id R)) {n : ℕ} (α : Fin n → Z1 (FP sW)) (β : Fin n → Z1 (FP sY))
  (f : C1 (FP sW))

def Bounds : Prop := ∀ (S S' S'' : Pt sW) (φ : S ⟶ S') (ψ : S' ⟶ S'') (χ : S ⟶ S''),
  (∀ b, χ.ρ b = ψ.ρ (φ.ρ b)) →
    ψ.ρ (v1 f φ) - v1 f χ + v1 f ψ = ∑ k, ψ.ρ (v1 (α k).1 φ) * v1 (β k).1 (pushHom hp ψ)

theorem exists_bounds
    (h : ∑ k, cup (FP sW) (H1.mk _ (α k)) (pullP hp (H1.mk _ (β k))) = 0) : ∃ f, Bounds hp α β f := by
  have hpull : ∀ k, pullP hp (H1.mk _ (β k)) = H1.mk (FP sW) ((pushC hp).pullbackOneCocycle (β k)) :=
    fun k => CoefMap.pullCohomologyOne_class _ _
  simp only [hpull, cup_mk] at h
  rw [← map_sum] at h
  obtain ⟨f, hf⟩ := H2.mk_eq_zero.mp h
  refine ⟨f, fun S S' S'' φ ψ χ e => ?_⟩
  have hχ : χ = φ ≫ ψ := by
    obtain ⟨ρχ, hχpt⟩ := χ
    have hρ : ρχ = (φ ≫ ψ).ρ := AlgHom.ext e
    subst hρ
    rfl
  subst hχ
  have hz := congrFun (congrFun (congrFun (congrFun (congrFun hf S) S') S'') φ) ψ
  simp only [d1_apply, Submodule.coe_sum, Finset.sum_apply, cupZ_apply, CoefMap.pullCocycleOne_apply] at hz
  exact hz

variable {T : Pt sY} {X' : Scheme.{0}} {s' : X' ⟶ Sp T.B} {w : X' ⟶ W}
  (hw : w ≫ sW = s' ≫ spMap (algebraMap R T.B)) (hw₂ : w ≫ p = s' ≫ T.x)

def eHom (S : Pt s') : T ⟶ pushPt hp (pushPt hw S) where
  ρ := { algebraMap T.B S.B with commutes' := fun _ ↦ rfl }
  pt := by
    change spMap (algebraMap T.B S.B) ≫ T.x = (S.x ≫ w) ≫ p
    rw [← S.w, Category.assoc, Category.assoc, hw₂]

variable {α β f}

def hZ (H : Bounds hp α β f) : Z1 (FP s') :=
  ⟨fun S S' φ ↦ (show S'.B from v1 f (pushHom hw φ)) +
      ∑ k, (show S'.B from v1 (α k).1 (pushHom hw φ)) * (show S'.B from v1 (β k).1 (eHom hp hw hw₂ S')),
    fun S S' S'' φ ψ ↦ key₁ (ψ.ρ : S'.B →+* S''.B) _ _ _ _ _ _ _ _ _
      (H _ _ _ (pushHom hw φ) (pushHom hw ψ) (pushHom hw (φ ≫ ψ)) fun _ ↦ rfl)
      (fun k ↦ cocycle_value_comp (α k) (pushHom hw φ) (pushHom hw ψ) (pushHom hw (φ ≫ ψ)) fun _ ↦ rfl)
      (fun k ↦ cocycle_value_comp (β k) (eHom hp hw hw₂ S') (pushHom hp (pushHom hw ψ)) (eHom hp hw hw₂ S'')
        fun b ↦ (ψ.ρ.commutes b).symm)⟩

theorem hZ_rel (H : Bounds hp α β f) {T' : Pt sY} (τ : T ⟶ T') {X'' : Scheme.{0}} {s'' : X'' ⟶ Sp T'.B}
    {w' : X'' ⟶ W} (hw' : w' ≫ sW = s'' ≫ spMap (algebraMap R T'.B)) (hw₂' : w' ≫ p = s'' ≫ T'.x)
    {j : X'' ⟶ X'} (hj : j ≫ s' = s'' ≫ spMap (τ.ρ : T.B →+* T'.B)) (e : j ≫ w = w') :
    H1.mk _ (hZ hp hw' hw₂' H) - pullP hj (H1.mk _ (hZ hp hw hw₂ H)) +
      ∑ k, v1 (β k).1 τ • pullP hj (pullP hw (H1.mk _ (α k))) = 0 := by
  have e1 : ∀ z, pullP hj (H1.mk (FP s') z) = H1.mk (FP s'') ((pushC hj).pullbackOneCocycle z) :=
    fun z => CoefMap.pullCohomologyOne_class _ _
  have e2 : ∀ z, pullP hw (H1.mk (FP sW) z) = H1.mk (FP s') ((pushC hw).pullbackOneCocycle z) :=
    fun z => CoefMap.pullCohomologyOne_class _ _
  simp only [e1, e2]
  simp only [← LinearMap.map_smul, ← map_sum, ← map_sub, ← map_add]
  rw [H1.mk_eq_zero]
  let u : ∀ S : Pt s'', pushPt hw (pushPt hj S) ⟶ pushPt hw' S := fun S =>
    { ρ := { RingHom.id S.B with commutes' := fun r => congrArg (algebraMap T'.B S.B) (τ.ρ.commutes r) }
      pt := by
        show Spec.map (CommRingCat.ofHom (RingHom.id S.B)) ≫ (S.x ≫ j) ≫ w = S.x ≫ w'
        rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.assoc, e] }
  refine ⟨fun S => v1 f (u S) + ∑ k, v1 (α k).1 (u S) * v1 (β k).1 (eHom hp hw' hw₂' S), ?_⟩
  funext S S' φ
  rw [amitsur_d0_apply]
  have hR : (↑(hZ hp hw' hw₂' H - (pushC hj).pullbackOneCocycle (hZ hp hw hw₂ H) +
      ∑ x : Fin n, v1 (β x).1 τ • (pushC hj).pullbackOneCocycle ((pushC hw).pullbackOneCocycle (α x))) : C1 (FP s'')) S S' φ
      = (v1 f (pushHom hw' φ) + ∑ k, v1 (α k).1 (pushHom hw' φ) * v1 (β k).1 (eHom hp hw' hw₂' S'))
        - (v1 f (pushHom hw (pushHom hj φ)) + ∑ k, v1 (α k).1 (pushHom hw (pushHom hj φ)) *
            v1 (β k).1 (eHom hp hw hw₂ (pushPt hj S')))
        + ∑ k, algebraMap T'.B S'.B (v1 (β k).1 τ) * v1 (α k).1 (pushHom hw (pushHom hj φ)) := by
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def]
    rfl
  rw [hR]
  rw [map_add, map_sum]
  simp only [map_mul]
  have B1 : mp (FP s'') φ (v1 f (u S)) - v1 f (u S ≫ pushHom hw' φ) + v1 f (pushHom hw' φ)
      = ∑ k, mp (FP s'') φ (v1 (α k).1 (u S)) * v1 (β k).1 (pushHom hp (pushHom hw' φ)) :=
    H _ _ _ (u S) (pushHom hw' φ) (u S ≫ pushHom hw' φ) (fun _ => rfl)
  have B2 : v1 f (pushHom hw (pushHom hj φ)) - v1 f (u S ≫ pushHom hw' φ) + v1 f (u S')
      = ∑ k, v1 (α k).1 (pushHom hw (pushHom hj φ)) * v1 (β k).1 (pushHom hp (u S')) :=
    H _ _ _ (pushHom hw (pushHom hj φ)) (u S') (u S ≫ pushHom hw' φ) (fun _ => rfl)
  have Ek : ∀ k, v1 (α k).1 (u S') * v1 (β k).1 (eHom hp hw' hw₂' S')
      - mp (FP s'') φ (v1 (α k).1 (u S)) * mp (FP s'') φ (v1 (β k).1 (eHom hp hw' hw₂' S))
      - v1 (α k).1 (pushHom hw' φ) * v1 (β k).1 (eHom hp hw' hw₂' S')
      + v1 (α k).1 (pushHom hw (pushHom hj φ)) * v1 (β k).1 (eHom hp hw hw₂ (pushPt hj S'))
      - algebraMap T'.B S'.B (v1 (β k).1 τ) * v1 (α k).1 (pushHom hw (pushHom hj φ))
      - mp (FP s'') φ (v1 (α k).1 (u S)) * v1 (β k).1 (pushHom hp (pushHom hw' φ))
      + v1 (α k).1 (pushHom hw (pushHom hj φ)) * v1 (β k).1 (pushHom hp (u S')) = 0 := by
    intro k
    have A1 : v1 (α k).1 (u S ≫ pushHom hw' φ)
        = mp (FP s'') φ (v1 (α k).1 (u S)) + v1 (α k).1 (pushHom hw' φ) :=
      cocycle_value_comp (α k) (u S) (pushHom hw' φ) (u S ≫ pushHom hw' φ) (fun _ => rfl)
    have A2 : v1 (α k).1 (u S ≫ pushHom hw' φ)
        = v1 (α k).1 (pushHom hw (pushHom hj φ)) + v1 (α k).1 (u S') :=
      cocycle_value_comp (α k) (pushHom hw (pushHom hj φ)) (u S') (u S ≫ pushHom hw' φ) (fun _ => rfl)
    have C1 : v1 (β k).1 (eHom hp hw hw₂ (pushPt hj S') ≫ pushHom hp (u S'))
        = algebraMap T'.B S'.B (v1 (β k).1 τ) + v1 (β k).1 (eHom hp hw' hw₂' S') :=
      cocycle_value_comp (β k) τ (eHom hp hw' hw₂' S') (eHom hp hw hw₂ (pushPt hj S') ≫ pushHom hp (u S')) (fun _ => rfl)
    have C2 : v1 (β k).1 (eHom hp hw hw₂ (pushPt hj S') ≫ pushHom hp (u S'))
        = v1 (β k).1 (eHom hp hw hw₂ (pushPt hj S')) + v1 (β k).1 (pushHom hp (u S')) :=
      cocycle_value_comp (β k) (eHom hp hw hw₂ (pushPt hj S')) (pushHom hp (u S'))
        (eHom hp hw hw₂ (pushPt hj S') ≫ pushHom hp (u S')) (fun _ => rfl)
    have D : v1 (β k).1 (eHom hp hw' hw₂' S')
        = mp (FP s'') φ (v1 (β k).1 (eHom hp hw' hw₂' S)) + v1 (β k).1 (pushHom hp (pushHom hw' φ)) :=
      cocycle_value_comp (β k) (eHom hp hw' hw₂' S) (pushHom hp (pushHom hw' φ)) (eHom hp hw' hw₂' S')
        (fun b => (φ.ρ.commutes b).symm)
    linear_combination (v1 (β k).1 (eHom hp hw' hw₂' S') : S'.B) * (A1 - A2)
      + (mp (FP s'') φ (v1 (α k).1 (u S)) : S'.B) * D
      + (v1 (α k).1 (pushHom hw (pushHom hj φ)) : S'.B) * (C1 - C2)
  have hs := Finset.sum_eq_zero (fun k (_ : k ∈ Finset.univ) => Ek k)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  linear_combination B2 - B1 + hs

end Cochain

section Fun

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem exists_fun (hF : AbelianDeRham.Free) (hB : AbelianDeRham.BaseChange) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {x : HdR A} (hx : x ∈ Fil A) {C : Type} [CommRing C] [Algebra R C]
    {A' : Over (Sp C)} [GrpObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap (algebraMap R C)) φ)
    (hS : Function.Surjective (toP (A'.hom ≫ 𝟙 _)))
    (hφ : φ ≫ A.hom ≫ 𝟙 _ = (A'.hom ≫ 𝟙 _) ≫ spMap (algebraMap R C)) :
    (∃ X : H1OnPoints (A'.hom ≫ 𝟙 _) →ₗ[C] C, ∀ c : primDR A, X (pullP hφ (toP _ c.1)) = algebraMap R C (x c)) ∧
      ∀ u : H1OnPoints (A'.hom ≫ 𝟙 _), u ∈ Submodule.span C (Set.range fun c : primDR A ↦ pullP hφ (toP _ c.1)) := by
  obtain ⟨hbc, hF1⟩ := hB R A g hA hg C A' φ h
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h
  have hg' : SmoothOfRelativeDimension g A'.hom := by
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    exact MorphismProperty.of_isPullback h.1 hg
  have hall : prim (dp0 C) (𝟙 (Sp C)) A' = ⊤ := (hF C A' g hA' hg').1
  set m := AbelianDeRham.bcMor h with hm
  have hpt : ∀ c : primDR A, pullP hφ (toP _ c.1) = toP _ (m.pull c).1 := fun c => pullP_toP m.isMor c.1
  set x' := hbc.bcMap x with hxe
  have hx' : ∀ c, x' (m.pull c) = algebraMap R C (x c) := hbc.corr_iff.mpr rfl
  let e : FirstDeRham (A'.hom ≫ 𝟙 _) →ₗ[C] primDR A' :=
    LinearMap.codRestrict (primDR A') LinearMap.id (fun d => by
      show d ∈ prim (dp0 C) (𝟙 (Sp C)) A'
      rw [hall]
      exact Submodule.mem_top)
  have hle : Submodule.span C (m.pull '' (PrimitiveSubmodule A)) ≤ LinearMap.ker x' := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hx', (Submodule.mem_dualAnnihilator x).mp hx c hc, map_zero]
  obtain ⟨X, hX⟩ := exists_factor' (toP (A'.hom ≫ 𝟙 _)) hS (x'.comp e) (by
    intro d hd
    rw [toP_eq_zero_iff] at hd
    have hmem : e d ∈ PrimitiveSubmodule A' := hd
    rw [hF1] at hmem
    exact hle hmem)
  refine ⟨⟨X, fun c => ?_⟩, fun u => ?_⟩
  · rw [hpt, hX]
    have he : e (m.pull c).1 = m.pull c := Subtype.ext rfl
    simp only [LinearMap.comp_apply, he, hx']
  · obtain ⟨d, rfl⟩ := hS u
    obtain ⟨t, ht⟩ := hbc.2 (e d)
    have hd : d = (liftSemi m.pull t).1 := by rw [ht]; rfl
    rw [hd]
    clear ht hd
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r c =>
      have hl : liftSemi m.pull (r ⊗ₜ c) = r • m.pull c := by
        first
        | rfl
        | simp [liftSemi]
      rw [hl, Submodule.coe_smul, map_smul, ← hpt]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
    | add a b ha hb =>
      rw [map_add, Submodule.coe_add, map_add]
      exact Submodule.add_mem _ ha hb

end Fun

open scoped CategoryTheory.Obj in
theorem exists_grpPullback {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) :
    ∃ (G' : Over S') (_ : GrpObj G') (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ := by
  letI : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  letI iP : GrpObj (Over.mk (Limits.pullback.snd G.hom f)) := Over.grpObjMkPullbackSnd
  refine ⟨Over.mk (Limits.pullback.snd G.hom f), iP, Limits.pullback.fst G.hom f,
    ⟨IsPullback.of_hasPullback _ _, ?_⟩⟩
  intro T x y x₀ y₀ hx hy
  rw [Hom.mul_def, Hom.mul_def, Over.grpObjMkPullbackSnd_mul]
  simp only [Over.comp_left, Category.assoc]
  have hm : ((Over.pullback f).map (μ : Over.mk G.hom ⊗ Over.mk G.hom ⟶ Over.mk G.hom)).left ≫
      Limits.pullback.fst G.hom f = Limits.pullback.fst _ f ≫ (μ : Over.mk G.hom ⊗ Over.mk G.hom ⟶ Over.mk G.hom).left := by
    simp only [Over.pullback_map_left]
    exact Limits.pullback.lift_fst _ _ _
  rw [hm]
  have key : (lift x y).left ≫ (Functor.LaxMonoidal.μ (Over.pullback f) (Over.mk G.hom) (Over.mk G.hom)).left ≫
      Limits.pullback.fst _ f = (lift x₀ y₀).left := by
    apply Limits.pullback.hom_ext
    · simp
      erw [Limits.pullback.lift_fst_assoc, Limits.pullback.lift_fst]
      exact hx.symm
    · simp
      erw [Limits.pullback.lift_snd_assoc, Limits.pullback.lift_snd]
      exact hy.symm
  rw [← key]
  simp only [Category.assoc]

set_option maxHeartbeats 1000000 in
theorem orth_of_surj (hF : AbelianDeRham.Free) (hB : AbelianDeRham.BaseChange) {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hS : ∀ (C : Type) [CommRing C] [Algebra R C] (A' : Over (Sp C)) [GrpObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap (algebraMap R C)) φ → Function.Surjective (toP (A'.hom ≫ 𝟙 _))) {P : LB (A ⊗ B).left} (hP : P.IsLB) {φ : HdR A →ₗ[R] HdR B →ₗ[R] R} (hφ : IsCorrForm (dp0 R) (𝟙 _) A B P φ) : ∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0 := by
  intro x hx y hy
  obtain ⟨n, a, b, hCh, hform⟩ := hφ
  rw [hform]
  have hp : (snd A B).left ≫ B.hom ≫ 𝟙 (Sp R) = ((A ⊗ B).hom ≫ 𝟙 (Sp R)) ≫ spMap (RingHom.id R) := by
    rw [← Category.assoc, Over.w]
    simp [spMap]
  have hq : (fst A B).left ≫ A.hom ≫ 𝟙 (Sp R) = ((A ⊗ B).hom ≫ 𝟙 (Sp R)) ≫ spMap (RingHom.id R) := by
    rw [← Category.assoc, Over.w]
    simp [spMap]
  have h0 := pull2_chern_class_eq_zero hP hCh
  rw [map_sum] at h0
  simp only [CoefMap.pullCohomologyTwo_cup] at h0
  have eA : ∀ k, (toPC _).pull1 (pullOver (dp0 R) (𝟙 (Sp R)) (fst A B) (a k).1) = pullP hq (toP _ (a k).1) :=
    fun k => (pullP_toP (IsMor.of_dividedPowersZeroIdeal (dp0 R) hq) _).symm
  have eB : ∀ k, (toPC _).pull1 (pullOver (dp0 R) (𝟙 (Sp R)) (snd A B) (b k).1) = pullP hp (toP _ (b k).1) :=
    fun k => (pullP_toP (IsMor.of_dividedPowersZeroIdeal (dp0 R) hp) _).symm
  simp only [eA, eB] at h0
  obtain ⟨α, hα⟩ : ∃ α : Fin n → Z1 (FP ((A ⊗ B).hom ≫ 𝟙 (Sp R))),
      ∀ k, H1.mk _ (α k) = pullP hq (toP _ (a k).1) :=
    ⟨fun k => (H1.mk_surjective _ (pullP hq (toP _ (a k).1))).choose,
      fun k => (H1.mk_surjective _ (pullP hq (toP _ (a k).1))).choose_spec⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin n → Z1 (FP (B.hom ≫ 𝟙 (Sp R))), ∀ k, H1.mk _ (β k) = toP _ (b k).1 :=
    ⟨fun k => (H1.mk_surjective _ (toP _ (b k).1)).choose,
      fun k => (H1.mk_surjective _ (toP _ (b k).1)).choose_spec⟩
  simp only [← hα, ← hβ] at h0
  obtain ⟨f, H⟩ := exists_bounds hp α β h0
  have hex : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), ∃ (A' : Over (Sp T.B)) (_ : GrpObj A') (φ : A'.left ⟶ A.left),
      IsGrpPullback A' A (spMap (algebraMap R T.B)) φ := fun T => exists_grpPullback A _
  choose A' iA φT hT using hex
  have hcond : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), φT T ≫ A.hom = ((A' T).hom ≫ T.x) ≫ B.hom := by
    intro T
    rw [(hT T).1.w, Category.assoc]
    congr 1
    simpa using T.w.symm
  let w : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), (A' T).left ⟶ (A ⊗ B).left :=
    fun T => Limits.pullback.lift (φT T) ((A' T).hom ≫ T.x) (hcond T)
  have hwf : ∀ T, w T ≫ (fst A B).left = φT T := fun T => Limits.pullback.lift_fst _ _ _
  have hws : ∀ T, w T ≫ (snd A B).left = (A' T).hom ≫ T.x := fun T => Limits.pullback.lift_snd _ _ _
  have hw : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), w T ≫ (A ⊗ B).hom ≫ 𝟙 (Sp R) =
      ((A' T).hom ≫ 𝟙 (Sp T.B)) ≫ spMap (algebraMap R T.B) := by
    intro T
    rw [← Over.w (fst A B), ← Category.assoc, ← Category.assoc, hwf, (hT T).1.w]
    simp
  have hw₂ : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), w T ≫ (snd A B).left = ((A' T).hom ≫ 𝟙 (Sp T.B)) ≫ T.x := by
    intro T
    rw [hws]
    simp
  have hφ' : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), φT T ≫ A.hom ≫ 𝟙 (Sp R) =
      ((A' T).hom ≫ 𝟙 (Sp T.B)) ≫ spMap (algebraMap R T.B) := by
    intro T
    simpa using (hT T).1.w
  have hE := fun T => exists_fun hF hB hA hg hx (hT T) (hS T.B (A' T) (φT T) (hT T)) (hφ' T)
  choose X hXc using fun T => (hE T).1
  let g : C0 (FP (B.hom ≫ 𝟙 (Sp R))) := fun T => X T (H1.mk _ (hZ hp (hw T) (hw₂ T) H))
  have key : ∀ (T T' : Pt (B.hom ≫ 𝟙 (Sp R))) (τ : T ⟶ T'),
      g T' - τ.ρ (g T) + ∑ k, v1 (β k).1 τ * algebraMap R T'.B (x (a k)) = 0 := by
    intro T T' τ
    have hsp : spMap (algebraMap R T'.B) = spMap (τ.ρ : T.B →+* T'.B) ≫ spMap (algebraMap R T.B) := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext r
      exact (τ.ρ.commutes r).symm
    have hjc : φT T' ≫ A.hom = ((A' T').hom ≫ spMap (τ.ρ : T.B →+* T'.B)) ≫ spMap (algebraMap R T.B) := by
      rw [(hT T').1.w, Category.assoc, hsp]
    let j : (A' T').left ⟶ (A' T).left := (hT T).1.lift (φT T') ((A' T').hom ≫ spMap (τ.ρ : T.B →+* T'.B)) hjc
    have hjf : j ≫ φT T = φT T' := (hT T).1.lift_fst _ _ _
    have hjs : j ≫ (A' T).hom = (A' T').hom ≫ spMap (τ.ρ : T.B →+* T'.B) := (hT T).1.lift_snd _ _ _
    have hj : j ≫ (A' T).hom ≫ 𝟙 (Sp T.B) = ((A' T').hom ≫ 𝟙 (Sp T'.B)) ≫ spMap (τ.ρ : T.B →+* T'.B) := by
      rw [Category.comp_id (A' T).hom, Category.comp_id (A' T').hom, hjs]
    have he : j ≫ w T = w T' := by
      apply Limits.pullback.hom_ext
      · change (j ≫ w T) ≫ (fst A B).left = w T' ≫ (fst A B).left
        rw [Category.assoc, hwf, hwf, hjf]
      · change (j ≫ w T) ≫ (snd A B).left = w T' ≫ (snd A B).left
        rw [Category.assoc, hws, hws, ← Category.assoc, hjs, Category.assoc, τ.pt]
    have hrel := hZ_rel hp (hw T) (hw₂ T) H τ (hw T') (hw₂ T') hj he
    have hi : ∀ u, X T' (pullP hj u) = τ.ρ (X T u) := by
      intro u
      refine Submodule.span_induction (p := fun u _ => X T' (pullP hj u) = τ.ρ (X T u)) ?_ ?_ ?_ ?_ ((hE T).2 u)
      · rintro _ ⟨c, rfl⟩
        rw [pullP_pullP (hφ' T) hj (hφ' T') (fun r => τ.ρ.commutes r) hjf, hXc, hXc]
        exact (τ.ρ.commutes _).symm
      · simp
      · intro u v _ _ hu hv
        simp only [map_add, hu, hv]
      · intro c u _ hu
        simp only [map_smulₛₗ, smul_eq_mul, map_mul, hu]
        rfl
    have hii : ∀ k, X T' (pullP hj (pullP (hw T) (H1.mk _ (α k)))) = algebraMap R T'.B (x (a k)) := by
      intro k
      rw [hα k, pullP_pullP hq (hw T) (hφ' T) (fun r => rfl) (hwf T),
        pullP_pullP (hφ' T) hj (hφ' T') (fun r => τ.ρ.commutes r) hjf, hXc]
    have h1 := congrArg (X T') hrel
    simp only [map_add, map_sub, map_sum, map_smul, smul_eq_mul, hii, map_zero] at h1
    simp only [hi] at h1
    exact h1
  have hcob : ∃ g : C0 (FP (B.hom ≫ 𝟙 (Sp R))), d0 _ g = ↑(∑ k, x (a k) • β k) := by
    refine ⟨-g, ?_⟩
    funext T T' τ
    rw [amitsur_d0_apply]
    show -g T' - τ.ρ (-g T) = v1 (∑ k, x (a k) • β k).1 τ
    rw [cocycle_value_sum, map_neg]
    have hs : ∑ k, algebraMap R T'.B (x (a k)) * v1 (β k).1 τ = ∑ k, v1 (β k).1 τ * algebraMap R T'.B (x (a k)) :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hs]
    linear_combination -key T T' τ
  have hmk : H1.mk _ (∑ k, x (a k) • β k) = 0 := H1.mk_eq_zero.mpr hcob
  have hc : toP (B.hom ≫ 𝟙 (Sp R)) (∑ k, x (a k) • (b k).1) = 0 := by
    simpa only [map_sum, map_smul, hβ] using hmk
  have hF1 := (toP_eq_zero_iff _).mp hc
  have hcF : (∑ k, x (a k) • b k) ∈ PrimitiveSubmodule B := by
    show (primDR B).subtype (∑ k, x (a k) • b k) ∈ F1 _
    simpa using hF1
  have hy0 := (Submodule.mem_dualAnnihilator _).mp hy _ hcF
  simpa [map_sum, map_smul] using hy0

end CrystallinePoints.Pd
end
end

section
set_option autoImplicit false

open TensorProduct

namespace CrystallinePoints.Pd

theorem surjective_of_sup_smulD {R : Type} [CommRing R] {H M : Type*} [AddCommGroup H] [Module R H]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (γ : H →ₗ[R] M)
    (h : ∀ m : Ideal R, m.IsMaximal → LinearMap.range γ ⊔ m • (⊤ : Submodule R M) = ⊤) :
    Function.Surjective γ := by
  set P := LinearMap.range γ
  have key : ∀ m : Ideal R, m.IsMaximal → ∃ r : R, r - 1 ∈ m ∧ ∀ x : M, r • x ∈ P := by
    intro m hm
    have hin : (⊤ : Submodule R (M ⧸ P)) ≤ m • ⊤ := by
      have e := congrArg (Submodule.map P.mkQ) (h m hm)
      rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ,
        Submodule.mkQ_map_self, bot_sup_eq] at e
      exact e.symm.le
    obtain ⟨r, hr, hr'⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m _
      (Module.Finite.fg_top) hin
    refine ⟨r, hr, fun x ↦ ?_⟩
    have := hr' (Submodule.Quotient.mk x) trivial
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
  let J : Ideal R :=
    { carrier := {r | ∀ x : M, r • x ∈ P}
      add_mem' := fun ha hb x ↦ by rw [add_smul]; exact P.add_mem (ha x) (hb x)
      zero_mem' := fun x ↦ by rw [zero_smul]; exact P.zero_mem
      smul_mem' := fun c r hr x ↦ by rw [smul_eq_mul, mul_smul]; exact P.smul_mem c (hr x) }
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨r, hr, hr'⟩ := key m hm
    have h1 : r ∈ m := hle hr'
    exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using m.sub_mem h1 hr))
  intro x
  have : (1 : R) ∈ J := hJ ▸ Submodule.mem_top
  have hx : x ∈ P := by simpa using this x
  exact hx

theorem finrank_res {R : Type} [CommRing R] (m : Ideal R) [hm : m.IsMaximal] (M : Type*) [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M] :
    Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = Module.rankAtStalk M (⟨m, hm.isPrime⟩ : PrimeSpectrum R) := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have h := Module.rankAtStalk_baseChange (R := R) (M := M) (S := R ⧸ m) (⊥ : PrimeSpectrum (R ⧸ m))
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  rw [show Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = _ from h]
  congr 1
  ext x
  simp [Ideal.Quotient.eq_zero_iff_mem]

theorem oneT_iff {R : Type} [CommRing R] (m : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]
    (y : M) : (1 : R ⧸ m) ⊗ₜ[R] y = 0 ↔ y ∈ m • (⊤ : Submodule R M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M m).map_eq_zero_iff, ← Submodule.Quotient.mk_eq_zero]
  have : TensorProduct.quotTensorEquivQuotSMul M m ((1 : R ⧸ m) ⊗ₜ[R] y) = Submodule.Quotient.mk y := by
    have := TensorProduct.quotTensorEquivQuotSMul_mk_tmul (M := M) m 1 y
    rwa [map_one, one_smul] at this
  rw [this]

theorem resSurj_coreD.{u} :
  ∀ (R : Type) [CommRing R] (H : Type 1) [AddCommGroup H] [Module R H] (M : Type u) [AddCommGroup M] [Module R M]
    (g : ℕ) (F N : Submodule R H), IsCompl F N → Module.Finite R H → Module.Projective R H →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk H p = 2 * g) → Module.Finite R F → Module.Projective R F →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk F p = g) → Module.Finite R M → Module.Projective R M →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk M p = g) → ∀ γ : H →ₗ[R] M,
    (∀ m : Ideal R, m.IsMaximal → ∀ q : H, γ q ∈ m • (⊤ : Submodule R M) → q ∈ F ⊔ m • (⊤ : Submodule R H)) →
    Function.Surjective γ := by
  intro R _ H _ _ M _ _ g F N hc fH pH rH fF pF rF fM pM rM γ hγ
  refine surjective_of_sup_smulD γ fun m hm ↦ ?_
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  let π : H →ₗ[R] N := Submodule.linearProjOfIsCompl N F hc.symm
  have hπ : ∀ n : N, π n = n := fun n ↦ Submodule.linearProjOfIsCompl_apply_left hc.symm n
  have hπF : ∀ x ∈ F, π x = 0 := fun x hx ↦ Submodule.linearProjOfIsCompl_apply_right' hc.symm hx
  haveI : Module.Finite R N := Module.Finite.of_surjective π fun n ↦ ⟨n, hπ n⟩
  have d1 := finrank_res m H
  have d2 := finrank_res m F
  have d3 := finrank_res m M
  rw [rH] at d1
  rw [rF] at d2
  rw [rM] at d3
  have d4 : Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] N) = g := by
    have e : (R ⧸ m) ⊗[R] H ≃ₗ[R ⧸ m] ((R ⧸ m) ⊗[R] F) × ((R ⧸ m) ⊗[R] N) :=
      (LinearEquiv.baseChange R (R ⧸ m) _ _ (Submodule.prodEquivOfIsCompl F N hc).symm).trans
        (TensorProduct.prodRight R (R ⧸ m) (R ⧸ m) F N)
    have := e.finrank_eq
    rw [Module.finrank_prod, d1, d2] at this
    omega
  have su : Function.Surjective (algebraMap R (R ⧸ m)) := Ideal.Quotient.mk_surjective
  let δ := (γ ∘ₗ N.subtype).baseChange (R ⧸ m)
  have hinj : Function.Injective δ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨n, rfl⟩ := TensorProduct.mk_surjective R N (R ⧸ m) su z
    have h1 : γ n ∈ m • (⊤ : Submodule R M) := (oneT_iff m _).1 hz
    obtain ⟨f, hf, w, hw, e⟩ := Submodule.mem_sup.1 (hγ m hm n h1)
    refine (oneT_iff m n).2 ?_
    have e2 : n = π w := by rw [← hπ n, ← e, map_add, hπF f hf, zero_add]
    rw [e2]
    have : π w ∈ Submodule.map π (m • ⊤) := Submodule.mem_map_of_mem hw
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hs : Function.Surjective δ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (d4.trans d3.symm)).1 hinj
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨z, hz⟩ := hs ((1 : R ⧸ m) ⊗ₜ y)
  obtain ⟨n, rfl⟩ := TensorProduct.mk_surjective R N (R ⧸ m) su z
  have h2 : y - γ n ∈ m • (⊤ : Submodule R M) := by
    refine (oneT_iff m _).1 ?_
    rw [TensorProduct.tmul_sub, ← hz]
    exact sub_self _
  exact Submodule.mem_sup.2 ⟨γ n, ⟨n, rfl⟩, _, h2, add_sub_cancel _ _⟩

end CrystallinePoints.Pd
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

theorem resSurj.{u} : ResSurj.{u} := resSurj_coreD.{u}

theorem duality_of_surjAll (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge) (hB : AbelianDeRham.BaseChange)
    (hS : SurjAll) : AbelianDeRham.Duality := by
  intro R _ A _ g hA hg L hL ψ hψ
  haveI := hA.comm
  have iso : ∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0 :=
    orth_of_surj hF hB hA hg (fun C _ _ A' _ φ h ↦ hS C A' g (GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h)
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg))
      (LB.isLB_linComb hL _ _) (isCorrForm_lam hψ)
  exact ⟨iso, perfect_ring hF hH hB hA hg hL hψ iso⟩

theorem surjAll_of_dual (hC : CubeTheorem) (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge)
    (hB : AbelianDeRham.BaseChange) (hD : DualAbelianScheme) : SurjAll := by
  intro R _ A _ g hA hg
  obtain ⟨E, hE⟩ := exists_isE
  obtain ⟨B, _, P, hA', hd, h₁, h₂⟩ := hD (Sp R) A hA
  exact surj_of_isDual' hE h₁ (fun hM a b ↦ additive_eps hC hA hA' h₁ hM a b) resSurj hF hH hB hA hg hA' (hd g hg)
    h₂.additive

theorem abelianDeRham (hC : CubeTheorem) (hS : AbelianDeRhamStructure) (hD : DualAbelianScheme) : AbelianDeRham :=
  have hF := GlobalTheory.abelianDeRhamStructure_toFree hS
  ⟨hF, hS.2.1, hS.2.2, AbelianDeRham.rigid_of_free_of_crystallineDeRham hF FubiniStudyChowHeightFormula₂.Adr.crystallineDeRham,
    duality_of_surjAll hF hS.2.1 hS.2.2 (surjAll_of_dual hC hF hS.2.1 hS.2.2 hD)⟩

end CrystallinePoints.Pd
end
end
