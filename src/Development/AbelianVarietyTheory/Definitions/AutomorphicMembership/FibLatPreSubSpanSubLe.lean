import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PairVEqZeroOfMemLieSpan
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsFiniteQCHomModOfExact
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (IsFiniteQC pullbackSections freeModule sectionsHom freeBasis)
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DualPull
open GlobalTheory.LocM (modN modNMap π_modNMap nsmul_id_modN)

namespace GlobalTheory.HTSheaf

section Subsheaves

variable {X : Scheme.{0}} {F G P : X.Modules} {U V : X.Opens}

instance isQuasicoherent_ker (φ : F ⟶ G) [F.IsQuasicoherent] [G.IsQuasicoherent] : (Sub.ker φ).toMod.IsQuasicoherent :=
  QCoh.isQuasicoherent_of_exact_app (Sub.ker φ).incl φ (fun U _ => (Sub.ker φ).incl_app_injective U)
    fun _ _ _ => (Sub.ker φ).mem_sec_iff

def imSub (φ : G ⟶ F) : Sub F := Sub.ker (cokernel.π φ)

instance isQuasicoherent_imSub (φ : G ⟶ F) [F.IsQuasicoherent] [G.IsQuasicoherent] : (imSub φ).toMod.IsQuasicoherent :=
  isQuasicoherent_ker _

theorem app_mem_imSub (φ : G ⟶ F) (s : Γ(G, V)) : φ.app V s ∈ (imSub φ).sec V :=
  congr(($(cokernel.condition φ)).app V s)

theorem mem_imSub_iff (φ : G ⟶ F) [F.IsQuasicoherent] [G.IsQuasicoherent] (hU : IsAffineOpen U) {s : Γ(F, U)} :
    s ∈ (imSub φ).sec U ↔ ∃ t, φ.app U t = s := QCoh.exact_cokernel_π_app φ hU s

def toIm (φ : G ⟶ F) : G ⟶ (imSub φ).toMod := (imSub φ).lift φ fun _ => app_mem_imSub φ

@[reassoc (attr := simp)] theorem toIm_incl (φ : G ⟶ F) : toIm φ ≫ (imSub φ).incl = φ := rfl

instance epi_toIm (φ : G ⟶ F) [F.IsQuasicoherent] [G.IsQuasicoherent] : Epi (toIm φ) :=
  (QCoh.epi_iff_forall_affine _).2 fun U hU s =>
    have ⟨t, ht⟩ := (mem_imSub_iff φ hU).1 ((imSub φ).incl_app_mem s)
    ⟨t, (imSub φ).incl_app_injective U ht⟩

def preSub (φ : F ⟶ G) (N : Sub G) : Sub F := Sub.ker (φ ≫ cokernel.π N.incl)

theorem mem_preSub_iff (φ : F ⟶ G) (N : Sub G) {s : Γ(F, V)} : s ∈ (preSub φ N).sec V ↔ φ.app V s ∈ N.sec V :=
  N.cokernel_π_app_eq_zero_iff

instance isQuasicoherent_preSub (φ : F ⟶ G) (N : Sub G) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [N.toMod.IsQuasicoherent] : (preSub φ N).toMod.IsQuasicoherent := isQuasicoherent_ker _

def spanSub {ι : Type} (u : ι → Γ(F, ⊤)) : Sub F := imSub (sectionsHom u)

instance isQuasicoherent_spanSub {ι : Type} [Finite ι] (u : ι → Γ(F, ⊤)) [F.IsQuasicoherent] :
    (spanSub u).toMod.IsQuasicoherent := isQuasicoherent_imSub _

theorem sectionsHom_app_sum {ι : Type} [Fintype ι] (u : ι → Γ(F, ⊤)) (a : ι → Γ(X, V)) :
    (sectionsHom u).app V (∑ i, a i • resM _ le_top (freeBasis X i)) = ∑ i, a i • resM F le_top (u i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Scheme.Modules.Hom.app_smul, app_resM, QCoh.sectionsHom_app_freeBasis]

theorem mem_spanSub_iff {ι : Type} [Fintype ι] (u : ι → Γ(F, ⊤)) [F.IsQuasicoherent] (hU : IsAffineOpen U)
    {s : Γ(F, U)} : s ∈ (spanSub u).sec U ↔ ∃ a : ι → Γ(X, U), ∑ i, a i • resM F le_top (u i) = s := by
  refine (mem_imSub_iff _ hU).trans ⟨fun ⟨t, ht⟩ => ?_, fun ⟨a, ha⟩ => ⟨_, (sectionsHom_app_sum u a).trans ha⟩⟩
  obtain ⟨a, rfl⟩ := QCoh.exists_sum_smul_freeBasis U t
  exact ⟨a, (sectionsHom_app_sum u a).symm.trans ht⟩

theorem res_mem_spanSub {ι : Type} (u : ι → Γ(F, ⊤)) (i : ι) (V : X.Opens) : resM F le_top (u i) ∈ (spanSub u).sec V :=
  (spanSub u).res_mem le_top (QCoh.sectionsHom_app_freeBasis u i ▸ app_mem_imSub _ _)

theorem π_app_eq_zero_iff [F.IsQuasicoherent] (hU : IsAffineOpen U) (N : ℕ) (s : Γ(F, U)) :
    (cokernel.π (N • 𝟙 F)).app U s = 0 ↔ ∃ r, N • r = s := by
  refine (QCoh.exact_cokernel_π_app _ hU s).trans (exists_congr fun r => ?_)
  rw [show (N • 𝟙 F).app U r = N • r from by
    induction N with
    | zero => rw [zero_smul, zero_smul]; rfl
    | succ n ih => rw [succ_nsmul, succ_nsmul, ← ih]; rfl]

theorem nsmul_sec_modN (N : ℕ) (s : Γ(modN F N, V)) : N • s = 0 := by
  have h (n : ℕ) : (n • 𝟙 (modN F N)).app V s = n • s := by
    induction n with
    | zero => rw [zero_smul, zero_smul]; rfl
    | succ n ih => rw [succ_nsmul, succ_nsmul, ← ih]; rfl
  rw [← h, nsmul_id_modN]
  rfl

end Subsheaves

section Minors

variable {X : Scheme.{0}} {F : X.Modules} (N : Sub F) (r : ℕ)

def minors (U : X.Opens) : Set Γ(X, U) :=
  {d | ∃ (l : Fin r → Γ(dual F, U)) (m : Fin r → Γ(N.toMod, U)),
    d = (Matrix.of fun i k => dualApp (l i) le_rfl (N.incl.app U (m k))).det}

theorem resG_minor {U V : X.Opens} (h : V ≤ U) (l : Fin r → Γ(dual F, U)) (m : Fin r → Γ(N.toMod, U)) :
    resG X h (Matrix.of fun i k => dualApp (l i) le_rfl (N.incl.app U (m k))).det =
      (Matrix.of fun i k => dualApp (resM _ h (l i)) le_rfl (N.incl.app V (resM _ h (m k)))).det := by
  rw [RingHom.map_det]
  congr 1
  ext i k
  rw [Matrix.of_apply, app_resM, dualApp_res]
  exact (dualApp_resM (l i) le_rfl h _).symm

theorem minors_subset [(dual F).IsQuasicoherent] [N.toMod.IsQuasicoherent] {U V : X.Opens} (hU : IsAffineOpen U)
    (f : Γ(X, U)) (h : V ≤ U) (hV : V = X.basicOpen f) : minors N r V ⊆ Ideal.span (resG X h '' minors N r U) := by
  rintro _ ⟨l, m, rfl⟩
  choose a l' hl using fun i => QCoh.exists_pow_smul_eq_res (dual F) hU f h hV (l i)
  choose b m' hm using fun k => QCoh.exists_pow_smul_eq_res N.toMod hU f h hV (m k)
  have hu : IsUnit (resG X h f) := by
    subst hV
    exact X.toRingedSpace.isUnit_res_basicOpen f
  have e := resG_minor N r h l' m'
  have e₂ : (Matrix.of fun i k => dualApp (resM _ h (l' i)) le_rfl (N.incl.app _ (resM _ h (m' k)))) =
      Matrix.diagonal (fun i => resG X h f ^ a i) * (Matrix.of fun i k => dualApp (l i) le_rfl (N.incl.app _ (m k))) *
        Matrix.diagonal fun k => resG X h f ^ b k := by
    ext i k
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, Matrix.of_apply,
      show resM _ h (l' i) = _ from (hl i).symm, show resM _ h (m' k) = _ from (hm k).symm,
      Scheme.Modules.Hom.app_smul, map_smul, dualApp_smul, resG_self, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_comm]
  rw [e₂, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal] at e
  have h₁ : IsUnit (∏ i, resG X h f ^ a i) := IsUnit.prod_univ_iff.2 fun i => hu.pow _
  have h₂ : IsUnit (∏ i, resG X h f ^ b i) := IsUnit.prod_univ_iff.2 fun i => hu.pow _
  rw [SetLike.mem_coe, ← Ideal.unit_mul_mem_iff_mem _ h₁, ← Ideal.mul_unit_mem_iff_mem _ h₂, ← e]
  exact Ideal.subset_span ⟨_, ⟨l', m', rfl⟩, rfl⟩

def minorIdeal [(dual F).IsQuasicoherent] [N.toMod.IsQuasicoherent] : X.IdealSheafData where
  ideal U := Ideal.span (minors N r U.1)
  map_ideal_basicOpen U f := by
    rw [Ideal.map_span]
    refine le_antisymm (Ideal.span_mono ?_) (Ideal.span_le.2 (minors_subset N r U.2 f _ rfl))
    rintro _ ⟨_, ⟨l, m, rfl⟩, rfl⟩
    exact ⟨_, _, resG_minor N r (X.basicOpen_le f) l m⟩

end Minors

section Eps

variable {R O ι : Type} [CommRing R] [CommRing O] (σ : ι → O →+* R)

open EigenSplit

def ann (χ : O →+* R) : Submodule R (R ⊗[ℤ] O) where
  carrier := {x | ∀ a, (1 ⊗ₜ a) * x = χ a • x}
  add_mem' hx hy a := by rw [mul_add, hx, hy, smul_add]
  zero_mem' a := by rw [mul_zero, smul_zero]
  smul_mem' c x hx a := by rw [mul_smul_comm, hx, smul_comm]

variable {σ}

theorem splitMap_eq_zero_of_mem_ann [IsDomain R] {i k : ι} (h : σ k ≠ σ i) {x : R ⊗[ℤ] O} (hx : x ∈ ann (σ i)) :
    splitMap σ x k = 0 := by
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 h
  have := congrArg (splitMap σ · k) (hx a)
  simp only [map_mul, map_smul, Pi.mul_apply, EigenSplit.splitMap_tmul, one_mul, Pi.smul_apply, smul_eq_mul] at this
  exact (mul_eq_zero.1 ((sub_mul _ _ _).trans (sub_eq_zero.2 this))).resolve_left (sub_ne_zero.2 ha)

theorem exists_ann_eq_span [IsDomain R] [IsPrincipalIdealRing R] [Finite ι] (hσ : Function.Injective σ)
    (h : Function.Injective (splitMap σ)) (i : ι) :
    ∃ ε, ann (σ i) = Submodule.span R {ε} ∧ splitMap σ ε i ≠ 0 := by
  classical
  have := Fintype.ofFinite ι
  let q : R ⊗[ℤ] O →ₗ[R] R := LinearMap.proj i ∘ₗ (splitMap σ).toLinearMap
  have hq : ∀ x ∈ ann (σ i), q x = 0 → x = 0 := fun x hx h0 => h (by
    rw [map_zero]
    exact funext fun k => if e : k = i then e ▸ h0 else splitMap_eq_zero_of_mem_ann (hσ.ne e) hx)
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal ((ann (σ i)).map q)).principal
  obtain ⟨ε, hε, rfl⟩ : d ∈ (ann (σ i)).map q := hd ▸ Submodule.mem_span_singleton_self d
  have key : ann (σ i) = Submodule.span R {ε} := by
    refine le_antisymm (fun x hx => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hε)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hd ▸ Submodule.mem_map_of_mem hx)
    exact Submodule.mem_span_singleton.2 ⟨c, sub_eq_zero.1 (hq _ (sub_mem (Submodule.smul_mem _ _ hε) hx)
      (by rw [map_sub, map_smul, hc, sub_self]))⟩
  refine ⟨ε, key, fun h0 => ?_⟩
  choose a ha using fun k : {k // k ≠ i} => DFunLike.ne_iff.1 (hσ.ne k.2)
  let x : R ⊗[ℤ] O := ∏ k : {k // k ≠ i}, (1 ⊗ₜ a k - σ k.1 (a k) ⊗ₜ 1)
  have hx (k : ι) : splitMap σ x k = ∏ k' : {k // k ≠ i}, (σ k (a k') - σ k'.1 (a k')) := by simp [x]
  have hm : x ∈ ann (σ i) := fun b => h (funext fun k => by
    simp only [map_mul, map_smul, Pi.mul_apply, EigenSplit.splitMap_tmul, one_mul, Pi.smul_apply, smul_eq_mul]
    by_cases e : k = i
    · rw [e]
    · rw [hx, Finset.prod_eq_zero (Finset.mem_univ (⟨k, e⟩ : {k // k ≠ i})) (sub_self _), mul_zero, mul_zero])
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (key ▸ hm)
  have := hx i
  rw [← hc, map_smul, Pi.smul_apply, h0, smul_zero] at this
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 this.symm
  exact ha k (sub_eq_zero.1 hk).symm

theorem map_eq_smul_idem [IsDomain R] [DecidableEq ι] (hσ : Function.Injective σ) {i : ι} {x : R ⊗[ℤ] O}
    (hx : x ∈ ann (σ i)) {R' : Type} [CommRing R'] (f : R →+* R') (h : IsSplitting fun k => f.comp (σ k)) :
    Algebra.TensorProduct.map f.toIntAlgHom (AlgHom.id ℤ O) x = f (splitMap σ x i) • idem h i := by
  have e (y : R ⊗[ℤ] O) (k : ι) : splitMap (fun k => f.comp (σ k))
      (Algebra.TensorProduct.map f.toIntAlgHom (AlgHom.id ℤ O) y) k = f (splitMap σ y k) := by
    induction y with
    | zero => simp
    | add y z hy hz => simp only [map_add, Pi.add_apply, hy, hz]
    | tmul r a => simp
  refine h.1 (funext fun k => ?_)
  rw [e, map_smul, splitMap_idem, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k = i
  · rw [hk, Pi.single_eq_same, mul_one]
  · rw [Pi.single_eq_of_ne hk, mul_zero, splitMap_eq_zero_of_mem_ann (hσ.ne hk) hx, map_zero]

variable {X : Scheme.{0}} {F : X.Modules}

def tensAct (β : R →+* Γ(X, ⊤)) (ρ : O →+* End F) : R ⊗[ℤ] O →+* End F :=
  letI : Algebra ℤ (End F) := Ring.toIntAlgebra _
  (Algebra.TensorProduct.lift ((smulEnd F).comp β).toIntAlgHom ρ.toIntAlgHom
    fun _ a => (smulHom_comp (act ρ a) _).symm).toRingHom

end Eps

section Pull

variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G'] [GrpObj G'']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {g : S'' ⟶ S'} {ψ : G''.left ⟶ G'.left}
  (h : IsGrpPullback G' G f φ) {V V' : S.Opens} {T T' : S'.Opens}

def pb (e : T ≤ f ⁻¹ᵁ V) : Γ(omega G, V) →+ Γ(omega G', T) :=
  letI := QCoh.appLEModule f ((Scheme.Modules.pullback f).obj (omega G)) e
  ((omegaBase h).app T).hom.comp (pullbackSections f (omega G) e).toAddMonoidHom

theorem pb_apply (e : T ≤ f ⁻¹ᵁ V) (s : Γ(omega G, V)) :
    pb h e s = (omegaBase h).app T (pullbackSections f (omega G) e s) := rfl

theorem pb_smul (e : T ≤ f ⁻¹ᵁ V) (a : Γ(S, V)) (s : Γ(omega G, V)) : pb h e (a • s) = f.appLE V T e a • pb h e s := by
  rw [pb_apply, QCoh.pullbackSections_smul, Scheme.Modules.Hom.app_smul, pb_apply]

theorem pb_resM (e : T ≤ f ⁻¹ᵁ V') (k : V' ≤ V) (s : Γ(omega G, V)) :
    pb h e (resM _ k s) = pb h (e.trans (f.preimage_mono k)) s :=
  congrArg ((omegaBase h).app T) (QCoh.pullbackSections_res f (omega G) e k s)

theorem resM_pb (e : T ≤ f ⁻¹ᵁ V) (k : T' ≤ T) (s : Γ(omega G, V)) : resM _ k (pb h e s) = pb h (k.trans e) s :=
  (app_resM (omegaBase h) k _).symm.trans (congrArg ((omegaBase h).app T') (QCoh.res_pullbackSections f (omega G) e k s))

variable [QuasiSeparated G.hom]

theorem pb_pb (h' : IsGrpPullback G'' G' g ψ) {k : S'' ⟶ S} {χ : G''.left ⟶ G.left} (h'' : IsGrpPullback G'' G k χ)
    (hk : g ≫ f = k) (hχ : ψ ≫ φ = χ) {W : S''.Opens} (e : T ≤ f ⁻¹ᵁ V) (e' : W ≤ g ⁻¹ᵁ T) (e'' : W ≤ k ⁻¹ᵁ V)
    (s : Γ(omega G, V)) : pb h' e' (pb h e s) = pb h'' e'' s := by
  subst hk hχ
  have H (x : W) := Conormal.exists_isChart (sec_hom (MonObj.one (X := G))) (V := V) (x := (g ≫ f) x.1) (e'' x.2)
  choose U B hx hU c using H
  refine Twist.sec_ext_of_cover (fun x : W => W ⊓ (g ≫ f) ⁻¹ᵁ U x) (fun _ => inf_le_left)
    (fun x hxW => Opens.mem_iSup.2 ⟨⟨x, hxW⟩, hxW, hx _⟩) fun x => ?_
  obtain ⟨a, ha⟩ := (c x).d_surjective (sec_hom (MonObj.one (X := G))) (resM _ (hU x) s)
  have k₁ : T ⊓ f ⁻¹ᵁ U x ≤ f ⁻¹ᵁ U x := inf_le_right
  have k₂ : W ⊓ (g ≫ f) ⁻¹ᵁ U x ≤ g ⁻¹ᵁ (T ⊓ f ⁻¹ᵁ U x) := inf_le_inf e' le_rfl
  have k₃ := Conormal.le_of_sq (unitSec_comp h) (c x).le k₁
  have k₄ := Conormal.le_of_sq (unitSec_comp h') k₃ k₂
  calc _ = pb h' k₂ (pb h k₁ (resM _ (hU x) s)) := by
        rw [resM_pb, pb_resM, ← resM_pb h e inf_le_left, pb_resM]
    _ = pb h'' inf_le_right (resM _ (hU x) s) := by
        rw [← show dUnit G (c x).le a = resM (omega G) (hU x) s from ha, pb_apply h, omegaBase_dUnit h _ _ k₃ le_rfl, pb_apply, omegaBase_dUnit h' _ _ k₄ le_rfl, pb_apply,
          omegaBase_dUnit h'' _ _ (W' := ψ ⁻¹ᵁ φ ⁻¹ᵁ B x) k₄ le_rfl]
        exact congrArg _ (Conormal.appLE_appLE rfl _ _ _ a)
    _ = _ := by rw [resM_pb, pb_resM]

theorem span_range_pb (hT : IsAffineOpen T) (hV : IsAffineOpen V) (e : T ≤ f ⁻¹ᵁ V) :
    Submodule.span Γ(S', T) (Set.range (pb h e)) = ⊤ := by
  letI := QCoh.appLEAlgebra f e
  letI := QCoh.appLEModule f ((Scheme.Modules.pullback f).obj (omega G)) e
  haveI := QCoh.appLE_isScalarTower f ((Scheme.Modules.pullback f).obj (omega G)) e
  refine eq_top_iff.2 fun s _ => ?_
  obtain ⟨t, rfl⟩ : ∃ t, (omegaBase h).app T t = s :=
    ⟨(inv (omegaBase h)).app T s, by rw [QCoh.app_app, IsIso.inv_hom_id]; rfl⟩
  induction t using (QCoh.isBaseChange_pullbackSections f (omega G) hT hV e).inductionOn with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
  | smul a t ht => rw [Scheme.Modules.Hom.app_smul]; exact Submodule.smul_mem _ _ (ht trivial)
  | add t t' ht ht' => rw [map_add]; exact add_mem (ht trivial) (ht' trivial)

omit [QuasiSeparated G.hom]

def pushOm : omega G ⟶ (Scheme.Modules.pushforward f).obj (omega G') :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv (omega G) (omega G') (omegaBase h)

theorem pushOm_app (s : Γ(omega G, V)) : (pushOm h).app V s = pb h (le_refl (f ⁻¹ᵁ V)) s :=
  congrArg ((omegaBase h).app (f ⁻¹ᵁ V)) (resM_self (F := (Scheme.Modules.pullback f).obj (omega G)) _ _).symm

def pushMod (N : ℕ) : modN (omega G) N ⟶ (Scheme.Modules.pushforward f).obj (modN (omega G') N) :=
  cokernel.desc _ (pushOm h ≫ (Scheme.Modules.pushforward f).map (cokernel.π _)) (by
    rw [Preadditive.nsmul_comp, Category.id_comp, ← Preadditive.comp_nsmul, ← Functor.map_nsmul,
      ← Category.comp_id (cokernel.π _), ← Preadditive.comp_nsmul, nsmul_id_modN, comp_zero, Functor.map_zero, comp_zero])

def pbMod (N : ℕ) (e : T ≤ f ⁻¹ᵁ V) : Γ(modN (omega G) N, V) →+ Γ(modN (omega G') N, T) :=
  (resM (modN (omega G') N) e).comp ((pushMod h N).app V).hom

theorem pbMod_π (N : ℕ) (e : T ≤ f ⁻¹ᵁ V) (s : Γ(omega G, V)) :
    pbMod h N e ((cokernel.π (N • 𝟙 (omega G))).app V s) = (cokernel.π (N • 𝟙 (omega G'))).app T (pb h e s) := by
  have e₁ : (pushMod h N).app V ((cokernel.π (N • 𝟙 (omega G))).app V s) =
      (cokernel.π (N • 𝟙 (omega G'))).app _ (pb h (le_refl (f ⁻¹ᵁ V)) s) := by
    rw [QCoh.app_app, pushMod, cokernel.π_desc, ← pushOm_app]
    rfl
  exact (congrArg (resM (modN (omega G') N) e) e₁).trans ((app_resM _ e _).symm.trans (congrArg _ (resM_pb h _ e s)))

theorem pbMod_resM (N : ℕ) (e : T ≤ f ⁻¹ᵁ V') (k : V' ≤ V) (u : Γ(modN (omega G) N, V)) :
    pbMod h N e (resM _ k u) = pbMod h N (e.trans (f.preimage_mono k)) u :=
  (congrArg (resM (modN (omega G') N) e) (app_resM (pushMod h N) k u)).trans
    (resM_resM (F := modN (omega G') N) (f.preimage_mono k) e _)

theorem resM_pbMod (N : ℕ) (e : T ≤ f ⁻¹ᵁ V) (k : T' ≤ T) (u : Γ(modN (omega G) N, V)) :
    resM _ k (pbMod h N e u) = pbMod h N (k.trans e) u := resM_resM e k _

theorem pbMod_omegaMap (a : G ⟶ G) (a' : G' ⟶ G') [IsMonHom a] [IsMonHom a'] (w : a'.left ≫ φ = φ ≫ a.left) (N : ℕ)
    (e : T ≤ f ⁻¹ᵁ V) (u : Γ(modN (omega G) N, V)) :
    pbMod h N e ((modNMap (omegaMap a) N).app V u) = (modNMap (omegaMap a') N).app T (pbMod h N e u) := by
  have key : modNMap (omegaMap a) N ≫ pushMod h N =
      pushMod h N ≫ (Scheme.Modules.pushforward f).map (modNMap (omegaMap a') N) := by
    have k₀ : omegaMap a ≫ pushOm h = pushOm h ≫ (Scheme.Modules.pushforward f).map (omegaMap a') := by
      rw [pushOm, ← Adjunction.homEquiv_naturality_left, omegaBase_naturality h h a a' w,
        Adjunction.homEquiv_naturality_right]
    rw [← cancel_epi (cokernel.π _), LocM.π_modNMap_assoc, pushMod, cokernel.π_desc, cokernel.π_desc_assoc, Category.assoc,
      ← Functor.map_comp, π_modNMap, reassoc_of% k₀, Functor.map_comp]
  exact (congrArg (resM (modN (omega G') N) e) congr(($key).app V u)).trans (app_resM (modNMap (omegaMap a') N) e _).symm

end Pull

example {X : Scheme.{0}} (F : X.Modules) (V : X.Opens) (s : Γ(F, V)) : s ∈ (imSub (𝟙 F)).sec V := app_mem_imSub (𝟙 F) s

example : (1 : ℤ) ⊗ₜ[ℤ] ((1, 0) : ℤ × ℤ) ∈ ann (RingHom.fst ℤ ℤ) := fun a => by
  rw [Algebra.TensorProduct.tmul_mul_tmul, ← TensorProduct.tmul_smul]
  cases a
  simp

end GlobalTheory.HTSheaf
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct NNReal CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HTLat GlobalTheory.LocM GlobalTheory.ChTor
open GlobalTheory.PtNorm (evz top_le_preimage_iff isLocalRing_intO)
open Formalism.MainNotions.DIV.Cons (SCF intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTSheaf

theorem exists_affine_le {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} {z : Sp R ⟶ X} {U : X.Opens}
    (e : ⊤ ≤ z ⁻¹ᵁ U) : ∃ W : X.Opens, IsAffineOpen W ∧ ⊤ ≤ z ⁻¹ᵁ W ∧ W ≤ U :=
  have ⟨W, hW, hx, hle⟩ := QCoh.exists_affine_mem_le _ ((top_le_preimage_iff z).1 e)
  ⟨W, hW, (top_le_preimage_iff z).2 hx, hle⟩

section Point

variable {p : ℕ} [Fact p.Prime] {C : SCF p} {Λ : Type} [CommRing Λ] [StarRing Λ]
  {P : Point p (fldVal C) ↥(intO ↥C.S) Λ} {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Sp ↥(intO ↥C.S) ⟶ X}
  {φ : P.G.left ⟶ G.left} (hφ : IsGrpPullback P.G G z φ) {U V : X.Opens}

variable (P) in

def omVal : Γ(omega P.G, ⊤) →+ P.OmC :=
  haveI := P.semi
  P.inclOm.toAddMonoidHom.comp (P.omegaCmp.toLinearMap.toAddMonoidHom.comp (toOmega P.G))

theorem omVal_smul (a : Γ(Sp ↥(intO ↥C.S), ⊤)) (s : Γ(omega P.G, ⊤)) :
    omVal P (a • s) = (show ↥(intO ↥C.S) from (Scheme.ΓSpecIso (.of ↥(intO ↥C.S))).hom a) • omVal P s := by
  have := P.semi
  obtain ⟨b, rfl⟩ : ∃ b, LieVB.cst _ b = a := ⟨_, Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of ↥(intO ↥C.S))) a⟩
  rw [Iso.inv_hom_id_apply]
  exact (congrArg (fun w => P.inclOm (P.omegaCmp w)) (toOmega_smul b s)).trans
    ((congrArg P.inclOm (P.omegaCmp.map_smul b _)).trans (P.inclOm.map_smul b _))

theorem exists_omVal_eq {w : P.OmC} (hw : w ∈ P.latOm) : ∃ s, omVal P s = w := by
  have := P.semi
  have := P.semi.smooth
  obtain ⟨w, rfl⟩ := hw
  obtain ⟨w, rfl⟩ := P.omegaCmp.surjective w
  obtain ⟨s, rfl⟩ := (OmegaGlobal.toOmega_bijective _ P.G
    ⟨tangent_injective _ _, TangentSurj.tangent_surjective _ _⟩).2 w
  exact ⟨s, rfl⟩

def evPt (e : ⊤ ≤ z ⁻¹ᵁ U) : Γ(omega G, U) →+ P.OmC := (omVal P).comp (pb hφ e)

theorem evPt_apply (e : ⊤ ≤ z ⁻¹ᵁ U) (s : Γ(omega G, U)) : evPt hφ e s = omVal P (pb hφ e s) := rfl

theorem evPt_mem (e : ⊤ ≤ z ⁻¹ᵁ U) (s : Γ(omega G, U)) : evPt hφ e s ∈ P.latOm := ⟨_, rfl⟩

theorem evPt_smul (e : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(X, U)) (s : Γ(omega G, U)) : evPt hφ e (a • s) = evz z e a • evPt hφ e s := by
  rw [evPt_apply, pb_smul, omVal_smul]
  rfl

theorem evPt_resM (e : ⊤ ≤ z ⁻¹ᵁ V) (k : V ≤ U) (s : Γ(omega G, U)) :
    evPt hφ e (resM _ k s) = evPt hφ (e.trans (z.preimage_mono k)) s := by
  rw [evPt_apply, pb_resM, evPt_apply]

def IsLiftAt {N : ℕ} (u : Γ(modN (omega G) N, ⊤)) (v : P.OmC) : Prop :=
  ∃ (U : X.Opens) (e : ⊤ ≤ z ⁻¹ᵁ U) (s : Γ(omega G, U)), (cokernel.π (N • 𝟙 (omega G))).app U s = resM _ le_top u ∧
    ∃ w ∈ P.latOm, v - evPt hφ e s = N • w

def fibLat (M : Sub (omega G)) : Submodule ↥(intO ↥C.S) P.OmC :=
  Submodule.span _ {v | ∃ (U : X.Opens) (e : ⊤ ≤ z ⁻¹ᵁ U), ∃ s ∈ M.sec U, evPt hφ e s = v}

theorem fibLat_le (M : Sub (omega G)) : fibLat hφ M ≤ P.latOm :=
  Submodule.span_le.2 (by rintro _ ⟨U, e, s, -, rfl⟩; exact evPt_mem hφ e s)

theorem evPt_mem_fibLat {M : Sub (omega G)} (e : ⊤ ≤ z ⁻¹ᵁ U) {s : Γ(omega G, U)} (hs : s ∈ M.sec U) :
    evPt hφ e s ∈ fibLat hφ M := Submodule.subset_span ⟨U, e, s, hs, rfl⟩

variable {hφ} {N : ℕ} {u u' : Γ(modN (omega G) N, ⊤)} {v v' : P.OmC}

theorem IsLiftAt.mem (h : IsLiftAt hφ u v) : v ∈ P.latOm := by
  obtain ⟨U, e, s, -, w, hw, h⟩ := h
  rw [sub_eq_iff_eq_add.1 h]
  exact add_mem (nsmul_mem hw _) (evPt_mem hφ e s)

theorem IsLiftAt.of_sub (h : IsLiftAt hφ u v) {w : P.OmC} (hw : w ∈ P.latOm) (e : v' - v = N • w) : IsLiftAt hφ u v' := by
  obtain ⟨U, k, s, hs, w', hw', h⟩ := h
  exact ⟨U, k, s, hs, w + w', add_mem hw hw', by rw [smul_add, ← e, ← h, sub_add_sub_cancel]⟩

theorem isLiftAt_zero (hφ : IsGrpPullback P.G G z φ) (N : ℕ) : IsLiftAt hφ (0 : Γ(modN (omega G) N, ⊤)) 0 :=
  ⟨⊤, le_top, 0, by rw [map_zero, map_zero], 0, zero_mem _, by rw [map_zero, sub_zero, smul_zero]⟩

theorem IsLiftAt.add (h : IsLiftAt hφ u v) (h' : IsLiftAt hφ u' v') : IsLiftAt hφ (u + u') (v + v') := by
  obtain ⟨U, e, s, hs, w, hw, h⟩ := h
  obtain ⟨U', e', s', hs', w', hw', h'⟩ := h'
  have k : ⊤ ≤ z ⁻¹ᵁ (U ⊓ U') := le_inf e e'
  refine ⟨U ⊓ U', k, resM _ inf_le_left s + resM _ inf_le_right s', ?_, w + w', add_mem hw hw', ?_⟩
  · rw [map_add, app_resM, app_resM, hs, hs', resM_resM, resM_resM, map_add]
  · rw [map_add, evPt_resM, evPt_resM, smul_add, ← h, ← h', add_sub_add_comm]

variable [QuasiSeparated G.hom]

theorem IsLiftAt.sub_evPt (h : IsLiftAt hφ u v) (e : ⊤ ≤ z ⁻¹ᵁ U) {s : Γ(omega G, U)}
    (hs : (cokernel.π (N • 𝟙 (omega G))).app U s = resM _ le_top u) : ∃ w ∈ P.latOm, v - evPt hφ e s = N • w := by
  have := isLocalRing_intO ↥C.S
  obtain ⟨U', e', s', hs', w, hw, h⟩ := h
  obtain ⟨W, hW, k, hle⟩ := exists_affine_le (U := U' ⊓ U) (le_inf e' e)
  obtain ⟨r, hr⟩ := (π_app_eq_zero_iff hW N (resM _ (hle.trans inf_le_left) s' - resM _ (hle.trans inf_le_right) s)).1 (by
    rw [map_sub, app_resM, app_resM, hs, hs', resM_resM, resM_resM, sub_self])
  have := congrArg (evPt hφ k) hr
  rw [map_nsmul, map_sub, evPt_resM, evPt_resM] at this
  exact ⟨w + evPt hφ k r, add_mem hw (evPt_mem hφ k r), by rw [smul_add, ← h, this, sub_add_sub_cancel]⟩

theorem IsLiftAt.sub (h : IsLiftAt hφ u v) (h' : IsLiftAt hφ u v') : ∃ w ∈ P.latOm, v - v' = N • w := by
  obtain ⟨U, e, s, hs, w', hw', h'⟩ := h'
  obtain ⟨w, hw, h⟩ := h.sub_evPt e hs
  exact ⟨w - w', sub_mem hw hw', by rw [smul_sub, ← h, ← h', sub_sub_sub_cancel_right]⟩

variable (hφ)

theorem exists_isLiftAt (u : Γ(modN (omega G) N, ⊤)) : ∃ v, IsLiftAt hφ u v := by
  have := isLocalRing_intO ↥C.S
  obtain ⟨W, hW, k, -⟩ := exists_affine_le (z := z) (U := ⊤) le_top
  obtain ⟨s, hs⟩ := QCoh.surjective_cokernel_π_app (N • 𝟙 (omega G)) hW (resM _ le_top u)
  exact ⟨_, W, k, s, hs, 0, zero_mem _, by rw [sub_self, smul_zero]⟩

theorem span_range_evPt (hU : IsAffineOpen U) (e : ⊤ ≤ z ⁻¹ᵁ U) :
    Submodule.span ↥(intO ↥C.S) (Set.range (evPt hφ e)) = P.latOm := by
  refine le_antisymm (Submodule.span_le.2 (by rintro _ ⟨s, rfl⟩; exact evPt_mem hφ e s)) fun w hw => ?_
  obtain ⟨s, rfl⟩ := exists_omVal_eq hw
  clear hw
  have hs : s ∈ Submodule.span Γ(Sp ↥(intO ↥C.S), ⊤) (Set.range (pb hφ e)) :=
    (span_range_pb hφ (isAffineOpen_top _) hU e).ge trivial
  induction hs using Submodule.span_induction with
  | mem s hs => obtain ⟨t, rfl⟩ := hs; exact Submodule.subset_span ⟨t, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add s t _ _ hs ht => rw [map_add]; exact add_mem hs ht
  | smul a s _ hs => rw [omVal_smul]; exact Submodule.smul_mem _ _ hs

theorem nsmul_mem_fibLat_preSub (M : Sub (modN (omega G) N)) {w : P.OmC} (hw : w ∈ P.latOm) :
    N • w ∈ fibLat hφ (preSub (cokernel.π (N • 𝟙 (omega G))) M) := by
  have := isLocalRing_intO ↥C.S
  obtain ⟨W, hW, k, -⟩ := exists_affine_le (z := z) (U := ⊤) le_top
  rw [← span_range_evPt hφ hW k] at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨s, rfl⟩ := hw
    rw [← map_nsmul]
    refine evPt_mem_fibLat hφ k ((mem_preSub_iff _ _).2 ?_)
    rw [(π_app_eq_zero_iff hW N _).2 ⟨s, rfl⟩]
    exact zero_mem _
  | zero => rw [smul_zero]; exact zero_mem _
  | add s t _ _ hs ht => rw [smul_add]; exact add_mem hs ht
  | smul a s _ hs => rw [smul_comm]; exact Submodule.smul_mem _ _ hs

theorem exists_eq_of_mem_preSub {F : X.Modules} [F.IsQuasicoherent] {J : Type} [Fintype J] (u : J → Γ(modN F N, ⊤))
    (hU : IsAffineOpen U) {s : Γ(F, U)} (hs : s ∈ (preSub (cokernel.π (N • 𝟙 F)) (spanSub u)).sec U) :
    ∃ (a : J → Γ(X, U)) (t : J → Γ(F, U)) (r : Γ(F, U)),
      (∀ i, (cokernel.π (N • 𝟙 F)).app U (t i) = resM _ le_top (u i)) ∧ s = N • r + ∑ i, a i • t i := by
  obtain ⟨a, ha⟩ := (mem_spanSub_iff u hU).1 ((mem_preSub_iff _ _).1 hs)
  choose t ht using fun i => QCoh.surjective_cokernel_π_app (N • 𝟙 F) hU (resM _ le_top (u i))
  obtain ⟨r, hr⟩ := (π_app_eq_zero_iff hU N (s - ∑ i, a i • t i)).1 (by
    rw [map_sub, map_sum, ← ha, sub_eq_zero]
    exact Finset.sum_congr rfl fun i _ => by rw [Scheme.Modules.Hom.app_smul, ht])
  exact ⟨a, t, r, ht, eq_add_of_sub_eq hr.symm⟩

theorem fibLat_preSub_spanSub_le {J : Type} [Fintype J] (u : J → Γ(modN (omega G) N, ⊤))
    {L : Submodule ↥(intO ↥C.S) P.OmC} (h₀ : ∀ w ∈ P.latOm, N • w ∈ L) (h₁ : ∀ i, ∃ v ∈ L, IsLiftAt hφ (u i) v) :
    fibLat hφ (preSub (cokernel.π (N • 𝟙 (omega G))) (spanSub u)) ≤ L := by
  have := isLocalRing_intO ↥C.S
  refine Submodule.span_le.2 ?_
  rintro _ ⟨U, e, s, hs, rfl⟩
  obtain ⟨W, hW, k, hle⟩ := exists_affine_le e
  obtain ⟨a, t, r, ht, hr⟩ := exists_eq_of_mem_preSub u hW ((preSub _ _).res_mem hle hs)
  have e₁ := evPt_resM hφ k hle s
  rw [hr, map_add, map_nsmul, map_sum] at e₁
  refine SetLike.mem_coe.2 (e₁ ▸ add_mem (h₀ _ (evPt_mem hφ k r)) (sum_mem fun i _ => ?_))
  obtain ⟨v, hv, h⟩ := h₁ i
  obtain ⟨w, hw, h⟩ := h.sub_evPt k (ht i)
  rw [evPt_smul, ← sub_sub_cancel v (evPt hφ k (t i)), h]
  exact Submodule.smul_mem _ _ (sub_mem hv (h₀ w hw))

theorem IsLiftAt.mem_fibLat {M : Sub (modN (omega G) N)} (hu : u ∈ M.sec ⊤) (h : IsLiftAt hφ u v) :
    v ∈ fibLat hφ (preSub (cokernel.π (N • 𝟙 (omega G))) M) := by
  obtain ⟨U, e, s, hs, w, hw, h⟩ := h
  rw [sub_eq_iff_eq_add.1 h]
  exact add_mem (nsmul_mem_fibLat_preSub hφ M hw)
    (evPt_mem_fibLat hφ e ((mem_preSub_iff _ _).2 (hs ▸ M.res_mem le_top hu)))

theorem IsLiftAt.pbMod {X' : Scheme.{0}} {G' : Over X'} [GrpObj G'] {f : X' ⟶ X} {ψ : G'.left ⟶ G.left}
    (hψ : IsGrpPullback G' G f ψ) {z' : Sp ↥(intO ↥C.S) ⟶ X'} {φ' : P.G.left ⟶ G'.left} (hφ' : IsGrpPullback P.G G' z' φ')
    (hz : z' ≫ f = z) (e : φ' ≫ ψ = φ) (h : IsLiftAt hφ u v) : IsLiftAt hφ' (pbMod hψ N le_top u) v := by
  obtain ⟨U, k, s, hs, w, hw, h⟩ := h
  have k' : ⊤ ≤ z' ⁻¹ᵁ f ⁻¹ᵁ U := (Conormal.le_preimage_of_comp hz).2 k
  refine ⟨f ⁻¹ᵁ U, k', pb hψ le_rfl s, ?_, w, hw, ?_⟩
  · rw [← pbMod_π, hs, pbMod_resM]
    exact (resM_pbMod hψ N le_top le_top u).symm
  · rw [evPt_apply, pb_pb hψ hφ' hφ hz e _ _ k, ← h, evPt_apply]

variable {La : Type} [AddCommGroup La] (lv : La → Pts P.A.A) {n : ℕ} (h : La →+ Γ(modN (omega G) (p ^ n), ⊤))

def IsVal (t : P.T) (v : P.OmC) : Prop := ∃ a, lv a = t.lev n ∧ IsLiftAt hφ (h a) v

variable {hφ lv h} (hadd : ∀ a b, lv (a + b) = lv a * lv b)
include hadd

theorem lv_zero : lv 0 = 1 := by
  have := hadd 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem IsVal.isLiftAt (hker : ∀ a, lv a = 1 → ∃ b, a = p ^ n • b) {t : P.T} (hv : IsVal hφ lv h t v) {a : La}
    (ha : lv a = t.lev n) : IsLiftAt hφ (h a) v := by
  obtain ⟨a', ha', hv⟩ := hv
  obtain ⟨b, hb⟩ := hker (a - a') (by
    have := hadd (a - a') a'
    rw [sub_add_cancel, ha, ha'] at this
    exact right_eq_mul.1 this)
  rwa [eq_add_of_sub_eq hb, map_add, map_nsmul, nsmul_sec_modN, zero_add]

variable (hφ h) in

theorem exists_isVal (honto : ∀ q, q ^ p ^ n = 1 → ∃ a, lv a = q) : ∃ f : P.T →+ P.OmC, ∀ t, IsVal hφ lv h t (f t) := by
  let A : AddSubmonoid (P.T × P.OmC) :=
    { carrier := {x | IsVal hφ lv h x.1 x.2}
      zero_mem' := ⟨0, lv_zero hadd, (map_zero h).symm ▸ isLiftAt_zero hφ _⟩
      add_mem' := fun ⟨a, ha, hv⟩ ⟨b, hb, hw⟩ => ⟨a + b, by rw [hadd, ha, hb]; rfl, (map_add h a b).symm ▸ hv.add hw⟩ }
  let B : Submodule ℤ_[p] (P.T × P.OmC) :=
    { A with
      smul_mem' := fun c x hx => by
        obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n c)
        rw [eq_add_of_sub_eq hd.symm, add_smul, Nat.cast_smul_eq_nsmul]
        refine A.add_mem ⟨0, ?_, ?_⟩ (A.nsmul_mem hx _)
        · rw [lv_zero hadd]
          exact (((tate_free_of_card p _ _ P.card_torsion).2.2 n _).2 ⟨d • x.1, by rw [smul_smul, mul_comm]; rfl⟩).symm
        · rw [map_zero]
          refine (isLiftAt_zero hφ _).of_sub (w := algebraMap ℤ_[p] ↥(intO ↥C.S) d • x.2)
            (P.latOm.smul_mem _ hx.choose_spec.2.mem) ?_
          rw [sub_zero, algebraMap_smul, ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_smul, mul_comm, Nat.cast_pow]
          rfl }
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (LinearMap.fst ℤ_[p] _ _ ∘ₗ B.subtype) LinearMap.id fun t => by
    obtain ⟨a, ha⟩ := honto _ (t.lev_pow n)
    obtain ⟨v, hv⟩ := exists_isLiftAt hφ (h a)
    exact ⟨⟨(t, v), a, ha, hv⟩, rfl⟩
  refine ⟨(LinearMap.snd ℤ_[p] _ _ ∘ₗ B.subtype ∘ₗ σ).toAddMonoidHom, fun t => ?_⟩
  have h₁ : IsVal hφ lv h (σ t).1.1 (σ t).1.2 := (σ t).2
  rwa [show (σ t).1.1 = t from congr($hσ t)] at h₁

end Point

section Level

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {p : ℕ} {C : SCF p}
  (P : PointsOfFlagModel.PtC Y C)

def levPt (k : ℕ) (a : Dw.La) : Pts (abVar P).A :=
  Over.homMk ((isGrpPullback_abVarι P).1.lift (P.y ≫ (Y.oF.etaA a ^ (l.A / k)).left) (𝟙 _)
    (by rw [Category.assoc, Over.w]; exact (Category.comp_id _).trans (Category.id_comp _).symm))
    ((isGrpPullback_abVarι P).1.lift_snd _ _ _)

theorem levPt_ι (k : ℕ) (a : Dw.La) : (levPt P k a).left ≫ abVarι P = P.y ≫ (Y.oF.etaA a ^ (l.A / k)).left :=
  (isGrpPullback_abVarι P).1.lift_fst _ _ _

def ptsEquiv : Pts (abVar P).A ≃* ((Over.mk (𝟙 _ ≫ P.y) : Over (Xo.XF c)) ⟶ Y.oF.t.G) :=
  MulEquiv.ofBijective (MonoidHom.mk' (fun x => pushPt (isGrpPullback_abVarι P).1.w x) fun x y =>
    Over.OverMorphism.ext ((isGrpPullback_abVarι P).2 _ x y _ _ rfl rfl).symm)
    ⟨fun x y e => Over.OverMorphism.ext ((isGrpPullback_abVarι P).1.hom_ext (congrArg (·.left) e)
      ((Over.w x).trans (Over.w y).symm)),
    fun x => ⟨Over.homMk ((isGrpPullback_abVarι P).1.lift x.left (𝟙 _) (Over.w x))
      ((isGrpPullback_abVarι P).1.lift_snd _ _ _), Over.OverMorphism.ext ((isGrpPullback_abVarι P).1.lift_fst _ _ _)⟩⟩

theorem ptsEquiv_left (x : Pts (abVar P).A) : (ptsEquiv P x).left = x.left ≫ abVarι P := rfl

theorem ptsEquiv_levPt (k : ℕ) (a : Dw.La) : ptsEquiv P (levPt P k a) = (toUnit _ ≫ Y.oF.etaA a) ^ (l.A / k) := by
  rw [← MonObj.comp_pow]
  refine Over.OverMorphism.ext ((levPt_ι P k a).trans ?_)
  rw [Over.comp_left, Over.toUnit_left]
  exact congrArg (· ≫ _) (Category.id_comp _).symm

theorem levPt_add (k : ℕ) (a b : Dw.La) : levPt P k (a + b) = levPt P k a * levPt P k b :=
  (ptsEquiv P).injective (by
    rw [map_mul, ptsEquiv_levPt, ptsEquiv_levPt, ptsEquiv_levPt, Y.oF.etaA_add, MonObj.comp_mul, mul_pow])

theorem levPt_spec {k : ℕ} (hk : k ∣ l.A) : (∀ q, q ^ k = 1 ↔ ∃ a, levPt P k a = q) ∧
    (∀ a, levPt P k a = 1 ↔ ∃ b, a = k • b) ∧
    letI := H.starRing; ∀ (x : 𝓞 E) a, levPt P k (x • a) = levPt P k a ≫ (abAct P).act x := by
  obtain ⟨m, hm⟩ := hk
  have h₀ : 0 < k * m := hm ▸ l.A_pos
  have hk := Nat.pos_of_mul_pos_right h₀
  obtain ⟨-, I, -, hI, -⟩ := Y.oF.geom ↥C.S (𝟙 _ ≫ P.y) (P.fK.comp (IntermediateField.inclusion c.le).toRingHom) (by
    rw [Category.id_comp, pullback.condition, reassoc_of% P.y_over]
    exact (Spec.map_comp _ _).symm)
  have e (a : Dw.La) : ptsEquiv P (levPt P k a) = I.ev k a := by
    rw [ptsEquiv_levPt, hI, hm, Nat.mul_div_cancel_left _ hk, I.tower k m hk (Nat.pos_of_mul_pos_left h₀)]
  refine ⟨fun q => ?_, fun a => ?_, fun x a => (ptsEquiv P).injective ?_⟩
  · rw [← (ptsEquiv P).map_eq_one_iff, map_pow, I.onto k hk]
    exact exists_congr fun a => by rw [← e, (ptsEquiv P).apply_eq_iff_eq]
  · rw [← (ptsEquiv P).map_eq_one_iff, e, I.ker k hk]
  · rw [e, I.lin, ← e]
    refine Over.OverMorphism.ext ?_
    rw [ptsEquiv_left, Over.comp_left, Over.comp_left, ptsEquiv_left, Category.assoc, Category.assoc, abAct_ι]

end Level

end GlobalTheory.HTSheaf
end
end
