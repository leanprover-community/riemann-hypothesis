import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupScheStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupSchemeStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_sqZero_naturality : ∀ (O : Type) [CommRing O] (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (A : Over (Sp O)) [GrpObj A] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w) := by
  first | exact @GlobalTheory.SqZeroPt.Phi_sqZeroMap_comp | exact GlobalTheory.SqZeroPt.Phi_sqZeroMap_comp | (intros; apply GlobalTheory.SqZeroPt.Phi_sqZeroMap_comp <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_smul : ∀ (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (A : Over (Sp O)) [GrpObj A] (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Wmod A), Phi z h (c • w) = c • Phi z h w := by
  first | exact @GlobalTheory.SqZeroPt.Phi_smul | exact GlobalTheory.SqZeroPt.Phi_smul | (intros; apply GlobalTheory.SqZeroPt.Phi_smul <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
open GlobalTheory.LieVB GlobalTheory.Conormal

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

theorem kappa_eq_epsIso (O : Type) [CommRing O]
    (σ : Γ(conormal (sec (zeroSec O O)), ⊤)) :
    kappa O O σ = toO O ((epsIso O).hom.app ⊤ σ) := by
  obtain ⟨b, rfl⟩ := (isChart O O).d_surjective (sec_hom (zeroSec O O)) σ
  rw [kappa_d]
  have hinj := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt O O))).hom).1
  let ε : Γ((TM O O).left, ⊤) := (Scheme.ΓSpecIso (.of (TrivSqZeroExt O O))).inv DualNumber.eps
  have hε : toTsze O O ε = DualNumber.eps := Iso.inv_hom_id_apply _ _
  have hb : b = (TM O O).hom.appLE ⊤ ⊤ le_top (cst O (toTsze O O b).fst) +
      (TM O O).hom.appLE ⊤ ⊤ le_top (cst O (toTsze O O b).snd) * ε := by
    apply hinj
    change toTsze O O b = toTsze O O _
    rw [map_add, map_mul, toTsze_base, toTsze_base, hε, Iso.inv_hom_id_apply,
      Iso.inv_hom_id_apply]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have e0 := d_base (sec_hom (zeroSec O O)) (isChart O O).le (le_preimage_top (TM O O).hom ⊤)
    (cst O (toTsze O O b).fst)
  have e1 := d_base (sec_hom (zeroSec O O)) (isChart O O).le (le_preimage_top (TM O O).hom ⊤)
    (cst O (toTsze O O b).snd)
  have e2 := d_mul (sec_hom (zeroSec O O)) (isChart O O).le
    ((TM O O).hom.appLE ⊤ ⊤ le_top (cst O (toTsze O O b).snd)) ε
  have e3 := appLE_base (sec_hom (zeroSec O O)) (isChart O O).le
    (le_preimage_top (TM O O).hom ⊤) le_rfl (cst O (toTsze O O b).snd)
  have hd : d (sec_hom (zeroSec O O)) (isChart O O).le b =
      cst O (toTsze O O b).snd • d (sec_hom (zeroSec O O)) (isChart O O).le ε := by
    conv_lhs => rw [hb]
    rw [map_add, e0, zero_add, e2, e1, smul_zero, add_zero, e3, GlobalTheory.LB.resG_self]
  have h1 : (epsIso O).hom.app ⊤ (d (sec_hom (zeroSec O O)) (isChart O O).le ε) =
      (1 : Γ(Sp O, ⊤)) := epsIso_d O
  rw [hd]
  have h2 := Scheme.Modules.Hom.app_smul (epsIso O).hom (cst O (toTsze O O b).snd)
    (d (sec_hom (zeroSec O O)) (isChart O O).le ε)
  refine Eq.trans ?_ (congrArg (toO O) h2).symm
  rw [h1]
  change _ = toO O (cst O (toTsze O O b).snd * 1)
  rw [_root_.mul_one, Iso.inv_hom_id_apply]

theorem exists_phi_eq (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A] :
    (GlobalTheory.LieVB.omega A).IsQuasicoherent →
      (∀ (l : Wmod A →ₗ[O] O), ∃ (v : TM O O ⟶ A) (h : zeroSec O O ≫ v = η[A]),
        ∀ w, Phi v h w = l w) := by
  intro hqc l
  let f : Γ(GlobalTheory.LieVB.omega A, ⊤) →ₗ[Γ(Sp O, ⊤)] Γ(Sp O, ⊤) :=
    { toFun := fun w => cst O (l w)
      map_add' := fun w w' => (congrArg (cst O) (l.map_add w w')).trans (map_add _ _ _)
      map_smul' := fun r w => by
        obtain ⟨a, rfl⟩ : ∃ a, r = cst O a := ⟨toO O r, (Iso.hom_inv_id_apply _ _).symm⟩
        have e : l (cst O a • w) = a * l w := l.map_smul a w
        exact (congrArg (cst O) e).trans (map_mul _ _ _) }
  obtain ⟨lam, hlam⟩ := (GlobalTheory.OmegaGlobal.dualApp_top_bijective (GlobalTheory.LieVB.omega A)).2 f
  obtain ⟨x, hx⟩ := GlobalTheory.LieVB.TangentSurj.tangent_surjective O A lam
  refine ⟨x.1, epsZero_comp x, fun w => ?_⟩
  have h1 := dualApp_tangent x (V := ⊤) w
  rw [hx] at h1
  have h2 : GlobalTheory.VB.dualApp lam (le_refl ⊤) w = cst O (l w) := LinearMap.congr_fun hlam w
  refine (kappa_eq_epsIso O _).trans ?_
  exact (congrArg (toO O) (h1.symm.trans h2)).trans (Iso.inv_hom_id_apply _ _)

end GlobalTheory.SqZeroPt
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_surjective_onto_dual : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A], (GlobalTheory.LieVB.omega A).IsQuasicoherent → (∀ (l : Wmod A →ₗ[O] O), ∃ (v : TM O O ⟶ A) (h : zeroSec O O ≫ v = η[A]), ∀ w, Phi v h w = l w) := by
  first | exact @GlobalTheory.SqZeroPt.exists_phi_eq | exact GlobalTheory.SqZeroPt.exists_phi_eq | (intros; apply GlobalTheory.SqZeroPt.exists_phi_eq <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

theorem Phi_congr {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
    [IsCentralScalar O M] {A : Over (Sp O)} [GrpObj A] {z z' : TM O M ⟶ A} (e : z = z')
    (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O M ≫ z' = η[A]) (w : Wmod A) :
    Phi z h w = Phi z' h' w := by
  subst e; rfl

theorem eq_map_comp_univ {p : ℕ} {O : Type} [CommRing O] (G : GlobalTheory.PDivGroup p O) {M : Type}
    [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ)
    (φ : G.A n →ₐ[O] TrivSqZeroExt O M)
    (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) :
    φ = (TrivSqZeroExt.map
      (GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩)).comp (univ G n) := by
  have hf : ∀ a, (φ a).fst = Bialgebra.counitAlgHom O (G.A n) a := fun a => AlgHom.congr_fun hφ a
  ext a
  · simp [univ, hf]
  · simp [univ]

theorem Phi_spOver_y : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) := by
  intro p O _ G A _ t nat M _ _ _ _ n φ hφ w
  have e : spOver φ ≫ t.y n = GlobalTheory.GrpTangent.sqZeroMap
      (GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩) ≫
        spOver (univ G n) ≫ t.y n := by
    rw [← Category.assoc]
    congr 1
    have e1 : GlobalTheory.GrpTangent.sqZeroMap
        (GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩) =
        spOver (TrivSqZeroExt.map
          (GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩)) := rfl
    rw [e1, spOver_comp, ← eq_map_comp_univ G n φ hφ]
  have h' : zeroSec O M ≫ GlobalTheory.GrpTangent.sqZeroMap
      (GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩) ≫
        spOver (univ G n) ≫ t.y n = η[A] := e ▸ zeroSec_spOver_y t n φ hφ
  rw [Phi_congr e _ h' w]
  exact nat _ M _ (spOver (univ G n) ≫ t.y n)
    (zeroSec_spOver_y t n _ (fst_comp_univ (G := G) n)) h' w

end GlobalTheory.SqZeroPt
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_naturality_module : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) := by
  first | exact @GlobalTheory.SqZeroPt.Phi_spOver_y | exact GlobalTheory.SqZeroPt.Phi_spOver_y | (intros; apply GlobalTheory.SqZeroPt.Phi_spOver_y <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

theorem cotMap_res_cn : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → ∀ (n : ℕ) (w : Wmod A), GlobalTheory.PDiv.cotMap (G.res n) (cn t (n + 1) w) = cn t n w := by
  intro p O _ G A _ t hnat n w
  have key : (TrivSqZeroExt.map (GlobalTheory.PDiv.cotMap (G.res n))).comp (univ G (n + 1)) =
      (univ G n).comp (G.res n : G.A (n + 1) →ₐ[O] G.A n) := by
    ext a
    · simp [univ]
    · simp [univ]
  have hz : GlobalTheory.GrpTangent.sqZeroMap (GlobalTheory.PDiv.cotMap (G.res n)) ≫
      (spOver (univ G (n + 1)) ≫ t.y (n + 1)) = spOver (univ G n) ≫ t.y n := by
    have e1 : GlobalTheory.GrpTangent.sqZeroMap (GlobalTheory.PDiv.cotMap (G.res n)) =
        spOver (TrivSqZeroExt.map (GlobalTheory.PDiv.cotMap (G.res n))) := rfl
    rw [← Category.assoc, e1, spOver_comp, key, ← spOver_comp, Category.assoc, t.res n]
  have h0 := zeroSec_spOver_y t (n + 1) _ (fst_comp_univ (G := G) (n + 1))
  have h1 : zeroSec O _ ≫ (GlobalTheory.GrpTangent.sqZeroMap (GlobalTheory.PDiv.cotMap (G.res n)) ≫
      (spOver (univ G (n + 1)) ≫ t.y (n + 1))) = η[A] := by
    rw [hz]; exact zeroSec_spOver_y t n _ (fst_comp_univ (G := G) n)
  have := hnat _ _ (GlobalTheory.PDiv.cotMap (G.res n)) _ h0 h1 w
  unfold cn
  rw [← this]
  have hP : ∀ {z z' : TM O (GlobalTheory.PDiv.Cot O (G.A n)) ⟶ A} (e : z = z') h h', Phi z h = Phi z' h' := by
    rintro _ _ rfl _ _; rfl
  exact congrArg (fun f => f w) (hP hz _ _)

end GlobalTheory.SqZeroPt
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_naturality_linear : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → ∀ (n : ℕ) (w : Wmod A), GlobalTheory.PDiv.cotMap (G.res n) (cn t (n + 1) w) = cn t n w := by
  atlas_forward_decl GlobalTheory.SqZeroPt.cotMap_res_cn
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt.CnSurj

theorem kappa_smul (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (r : Γ(Sp O, ⊤))
    (s : Γ(GlobalTheory.Conormal.conormal (GlobalTheory.LieVB.sec (zeroSec O M)), ⊤)) :
    kappa O M (r • s) = toO O r • kappa O M s := by
  letI := (isChart O M).algebra
  letI := topModule O M
  exact map_smul ((AugCot.lift ((isChart O M).aug (GlobalTheory.LieVB.sec_hom _)) (sndFn O M)
    (sndFn_der O M)) ∘ₗ ((isChart O M).augCotEquiv (GlobalTheory.LieVB.sec_hom _)).symm.toLinearMap) r s

theorem Phi_smul {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] {A : Over (Sp O)} [GrpObj A]
    (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Wmod A) :
    Phi z h (c • w) = c • Phi z h w := by
  have e : toO O (GlobalTheory.LieVB.cst O c) = c := Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of O)) c
  have h1 := map_smul (QCoh.appLinear (GlobalTheory.LieVB.cotMap z h) ⊤) (GlobalTheory.LieVB.cst O c)
    (show Γ(GlobalTheory.LieVB.omega A, ⊤) from w)
  refine (congrArg (kappa O M) h1).trans ((kappa_smul O M _ _).trans ?_)
  rw [e]
  rfl

theorem cn_surjective (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O))
    [GrpObj A] (t : G.TorsionTower A)
    (hinj : ∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M]
      (z z' : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O M ≫ z' = η[A]),
      (∀ w, Phi z h w = Phi z' h' w) → z = z')
    (hnat : ∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M]
      (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M)
      (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A),
      Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w =
        GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w))
    (n : ℕ) : Function.Surjective (cn t n) := by
  let ε := Bialgebra.counitAlgHom O (G.A n)
  let c : Wmod A →ₗ[O] AugCot ε :=
    { toFun := cn t n
      map_add' := map_add (cn t n)
      map_smul' := fun a w => Phi_smul _ _ a w }
  let N := AugCot ε ⧸ LinearMap.range c
  letI : Module Oᵐᵒᵖ N := opModule O N
  haveI : IsCentralScalar O N := opModule_central O N
  let q : AugCot ε →ₗ[O] N := (LinearMap.range c).mkQ
  let φ := (AugCot.sqZeroEquiv ε N).symm q
  let φ₀ := (AugCot.sqZeroEquiv ε N).symm 0
  have e : φ.1 = φ₀.1 := t.inj n _ _ _ <|
    hinj N _ _ (zeroSec_spOver_y t n φ.1 φ.2) (zeroSec_spOver_y t n φ₀.1 φ₀.2) fun w => by
      refine (hnat N n φ.1 φ.2 w).trans (Eq.trans ?_ (hnat N n φ₀.1 φ₀.2 w).symm)
      change AugCot.sqZeroEquiv ε N φ (c w) = AugCot.sqZeroEquiv ε N φ₀ (c w)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, LinearMap.zero_apply]
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨w, rfl⟩
  have hq : q = 0 := (AugCot.sqZeroEquiv ε N).symm.injective (Subtype.ext e)
  intro x
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range c)).1 (LinearMap.congr_fun hq x)

end GlobalTheory.SqZeroPt.CnSurj
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_injective_criterion : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (z z' : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O M ≫ z' = η[A]), (∀ w, Phi z h w = Phi z' h' w) → z = z') → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) → ∀ n : ℕ, Function.Surjective (cn t n) := by
  first | exact @GlobalTheory.SqZeroPt.CnSurj.cn_surjective | exact GlobalTheory.SqZeroPt.CnSurj.cn_surjective | (intros; apply GlobalTheory.SqZeroPt.CnSurj.cn_surjective <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LieKer

theorem mem_smul_top_of_forms {O W : Type} [CommRing O] [AddCommGroup W] [Module O W]
    [Module.Finite O W] [Module.Projective O W] (I : Ideal O) (w : W)
    (hw : ∀ l : W →ₗ[O] O, l w ∈ I) : w ∈ (I • ⊤ : Submodule O W) := by
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' O W
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have e : w = ∑ i, (s w i) • f (Pi.single i 1) := by
    conv_lhs => rw [← LinearMap.id_apply (R := O) w, ← hs]
    rw [LinearMap.comp_apply]
    conv_lhs => rw [pi_eq_sum_univ (s w)]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  rw [e]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
  exact hw (LinearMap.proj i ∘ₗ s)

end GlobalTheory.LieKer

namespace GlobalTheory.LieKer

open GlobalTheory.PDiv

theorem zeroSec_sqZeroMap {O : Type} [CommRing O] {M N : Type} [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N]
    [IsCentralScalar O N] (l : M →ₗ[O] N) :
    zeroSec O N ≫ GlobalTheory.GrpTangent.sqZeroMap l = zeroSec O M := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  simp

theorem ker_cn_le : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), Module.Finite O (Wmod A) → Module.Projective O (Wmod A) → (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → (∀ (l : Wmod A →ₗ[O] O), ∃ (v : TM O O ⟶ A) (h : zeroSec O O ≫ v = η[A]), ∀ w, Phi v h w = l w) → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) → ∀ (n : ℕ) (w : Wmod A), cn t n w = 0 → w ∈ (Ideal.span {(p : O) ^ n} • ⊤ : Submodule O (Wmod A)) := by
  intro p O _ G A _ t hfin hproj hnat hsurj hcn n w hw
  refine mem_smul_top_of_forms _ w fun l => ?_
  obtain ⟨v, hv, hl⟩ := hsurj l
  let M := ModPow p O n
  let mk : O →ₗ[O] M := (Ideal.Quotient.mkₐ O (Ideal.span {(p : O) ^ n})).toLinearMap
  have h' : zeroSec O M ≫ (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v) = η[A] := by
    rw [← Category.assoc, zeroSec_sqZeroMap, hv]
  have e1 := hnat O M mk v hv h' w
  have htan : IsTangent v := by
    have := congrArg Over.Hom.left hv
    simp only [Over.comp_left, zeroSec, Over.homMk_left] at this
    exact this
  have hpow : (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v : SpAlg O (TrivSqZeroExt O M) ⟶ A) ^ p ^ n = 1 := by
    have hs : GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale (((p ^ n : ℕ) : O)) =
        GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale 0 := by
      ext1
      change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      ext
      · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR]
      · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR, mk]
    rw [← MonObj.comp_pow, GlobalTheory.GrpTangent.pow_eq_epsScale_comp htan, ← Category.assoc, hs,
      Category.assoc, GlobalTheory.GrpTangent.epsScale_zero_comp htan, MonObj.comp_one]
  obtain ⟨φ, hφy⟩ := t.surj n (TrivSqZeroExt O M) _ hpow
  have hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n) := by
    have H : spOver ((TrivSqZeroExt.fstHom O O M).comp φ) ≫ t.y n = 1 := by
      rw [← spOver_comp, Category.assoc, hφy]
      ext1
      simp only [Over.comp_left]
      have e : (spOver (TrivSqZeroExt.fstHom O O M)).left ≫ (GlobalTheory.GrpTangent.sqZeroMap mk).left =
          spMap (TrivSqZeroExt.fstHom O O O).toRingHom := by
        change Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp]
        congr 1
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        simp
      rw [← Category.assoc, e]
      refine (htan : _).trans ?_
      have hu : (toUnit (Over.mk (spMap (algebraMap O O)))).left = 𝟙 (Sp O) := by
        rw [Over.toUnit_left]; exact Spec.map_id _
      change η[A].left = (toUnit (Over.mk (spMap (algebraMap O O))) ≫ η[A]).left
      rw [Over.comp_left, hu]
      exact (Category.id_comp _).symm
    exact AlgHom.ext fun a => ((t.eq_one_iff n _).1 H a).trans (by simp)
  have e2 := hcn M n φ hφ w
  have e3 : Phi (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v) h' w = 0 := by
    have tr : ∀ (z : TM O M ⟶ A) (hz : zeroSec O M ≫ z = η[A]), spOver φ ≫ t.y n = z →
        Phi z hz w = Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w := by
      rintro z hz rfl; rfl
    rw [tr _ h' hφy, e2, hw, map_zero]
  rw [e3, hl] at e1
  exact (Ideal.Quotient.eq_zero_iff_mem).1 e1.symm

end GlobalTheory.LieKer
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_naturality_family : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), Module.Finite O (Wmod A) → Module.Projective O (Wmod A) → (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → (∀ (l : Wmod A →ₗ[O] O), ∃ (v : TM O O ⟶ A) (h : zeroSec O O ≫ v = η[A]), ∀ w, Phi v h w = l w) → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) → ∀ (n : ℕ) (w : Wmod A), cn t n w = 0 → w ∈ (Ideal.span {(p : O) ^ n} • ⊤ : Submodule O (Wmod A)) := by
  first | exact @GlobalTheory.LieKer.ker_cn_le | exact GlobalTheory.LieKer.ker_cn_le | (intros; apply GlobalTheory.LieKer.ker_cn_le <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.PDiv

namespace GlobalTheory.SqZeroPt

theorem tanDer_cn : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) → ∀ (v : epsR O ⟶ A) (hv : IsTangent v) (h : zeroSec O O ≫ v = η[A]) (n : ℕ) (w : Wmod A), t.tanDer hv n (cn t n w) = Ideal.Quotient.mk _ (Phi v h w) := by
  intro p O _ G A _ t hlin hpt v hv h n w
  haveI : IsCentralScalar O (ModPow p O n) := ⟨fun r m => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
    change (Submodule.Quotient.mk (MulOpposite.op r • x) : ModPow p O n) =
      Submodule.Quotient.mk (r • x)
    rw [op_smul_eq_smul]⟩
  let mk : O →ₗ[O] ModPow p O n := (Ideal.Quotient.mkₐ O _).toLinearMap
  let v' : TM O (ModPow p O n) ⟶ A := GlobalTheory.GrpTangent.sqZeroMap mk ≫ v
  have hsq : ∀ l : O →ₗ[O] ModPow p O n,
      GlobalTheory.GrpTangent.sqZeroMap l = spOver (TrivSqZeroExt.map l) := fun _ => rfl
  have hsc : ∀ c : O, GlobalTheory.GrpTangent.epsScale c =
      spOver (TrivSqZeroExt.map (c • (LinearMap.id : O →ₗ[O] O))) := fun _ => rfl
  have hpow : v' ^ p ^ n = 1 := by
    have h0 : mk ∘ₗ (((p ^ n : ℕ) : O) • (LinearMap.id : O →ₗ[O] O)) =
        mk ∘ₗ ((0 : O) • (LinearMap.id : O →ₗ[O] O)) := by
      refine LinearMap.ext fun x => ?_
      have hz : mk ((p ^ n : ℕ) : O) = 0 := by
        change Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}) ((p ^ n : ℕ) : O) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
        exact Ideal.mem_span_singleton_self _
      change mk (((p ^ n : ℕ) : O) • x) = mk ((0 : O) • x)
      rw [zero_smul, map_zero, smul_eq_mul, mul_comm, ← smul_eq_mul, map_smul, hz, smul_zero]
    have e1 : GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale ((p ^ n : ℕ) : O) =
        GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale 0 := by
      rw [hsq, hsc, hsc, spOver_comp, spOver_comp, ← TrivSqZeroExt.map_comp_map,
        ← TrivSqZeroExt.map_comp_map, h0]
    change (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v) ^ p ^ n = 1
    rw [← MonObj.comp_pow, GlobalTheory.GrpTangent.pow_eq_epsScale_comp hv, ← Category.assoc, e1,
      Category.assoc, GlobalTheory.GrpTangent.epsScale_zero_comp hv, MonObj.comp_one]
  obtain ⟨φ, hφv⟩ := t.surj n (TrivSqZeroExt O (ModPow p O n)) v' hpow
  have hone : spOver (TrivSqZeroExt.fstHom O O O) ≫ v = 1 := by
    have h2 := congrArg Over.Hom.left h
    simp only [Over.comp_left] at h2
    ext1
    simp only [Over.comp_left]
    change (zeroSec O O).left ≫ v.left = _
    rw [h2]
    have hu : (toUnit (Over.mk (spMap (algebraMap O O)))).left = 𝟙 (Sp O) := by
      rw [Over.toUnit_left]; exact Spec.map_id _
    change _ = (toUnit (Over.mk (spMap (algebraMap O O)))).left ≫ η[A].left
    erw [hu]
    exact (Category.id_comp _).symm
  have hφ : (TrivSqZeroExt.fstHom O O (ModPow p O n)).comp φ =
      Bialgebra.counitAlgHom O (G.A n) := by
    have e : (TrivSqZeroExt.fstHom O O (ModPow p O n)).comp (TrivSqZeroExt.map mk) =
        TrivSqZeroExt.fstHom O O O := by
      ext; simp
    have h1 : spOver ((TrivSqZeroExt.fstHom O O (ModPow p O n)).comp φ) ≫ t.y n = 1 := by
      rw [← spOver_comp, Category.assoc, hφv]
      change spOver _ ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v = 1
      rw [hsq, ← Category.assoc, spOver_comp, e, hone]
    exact AlgHom.ext fun a => ((t.eq_one_iff n _).1 h1 a).trans (by simp)
  let q := Ideal.Quotient.mk (Ideal.span {(p : O) ^ n})
  let κ : TrivSqZeroExt O (ModPow p O n) →ₐ[O] DualNumber (ModPow p O n) :=
    { toFun := fun z => TrivSqZeroExt.inl (q z.fst) + TrivSqZeroExt.inr z.snd
      map_one' := by ext <;> simp
      map_mul' := fun x y => by
        ext
        · simp
        · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr]
          simp [Algebra.smul_def, q, mul_comm]
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp [q]
      commutes' := fun r => by ext <;> simp [q, TrivSqZeroExt.algebraMap_eq_inl', Ideal.Quotient.algebraMap_eq] }
  have key : κ.comp (TrivSqZeroExt.map mk) = epsTo O (ModPow p O n) := by
    ext <;> simp [κ, q, mk]
  have htan : t.tanPt hv n = κ.comp φ := by
    refine t.inj n _ _ _ ?_
    rw [t.tanPt_y hv n, ← spOver_comp, Category.assoc, hφv]
    change _ = spOver κ ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v
    rw [hsq, ← Category.assoc, spOver_comp, key]
  have hder : t.tanDer hv n =
      GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) (ModPow p O n) ⟨φ, hφ⟩ :=
    GlobalTheory.AugCot.hom_ext fun a => by
      change t.tanDer hv n (dUnit O a) = _
      rw [t.tanDer_d hv n, GlobalTheory.AugCot.sqZeroEquiv_d, htan]
      simp [κ]
  have h' : zeroSec O (ModPow p O n) ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v = η[A] :=
    by have e := zeroSec_spOver_y t n φ hφ; rw [hφv] at e; exact e
  have hc : ∀ (z z' : TM O (ModPow p O n) ⟶ A) (e : z = z') (hz : zeroSec O (ModPow p O n) ≫ z = η[A])
      (hz' : zeroSec O (ModPow p O n) ≫ z' = η[A]), Phi z hz w = Phi z' hz' w := by
    intro z z' e hz hz'; subst e; rfl
  rw [hder, ← hpt (ModPow p O n) n φ hφ w, hc _ _ hφv _ h']
  exact hlin O (ModPow p O n) mk v h h' w

end GlobalTheory.SqZeroPt
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_naturality_pair : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) → ∀ (v : epsR O ⟶ A) (hv : IsTangent v) (h : zeroSec O O ≫ v = η[A]) (n : ℕ) (w : Wmod A), t.tanDer hv n (cn t n w) = Ideal.Quotient.mk _ (Phi v h w) := by
  atlas_forward_decl GlobalTheory.SqZeroPt.tanDer_cn
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompatLift

theorem exists_of_compat {O : Type} [CommRing O] (p : O) [IsPrecomplete (Ideal.span {p}) O]
    {W : Type} [AddCommGroup W] [Module O W] [Module.Finite O W]
    {C : ℕ → Type} [∀ n, AddCommGroup (C n)] [∀ n, Module O (C n)]
    (c : ∀ n, W →+ C n) (hsurj : ∀ n, Function.Surjective (c n))
    (hker : ∀ (n : ℕ) (w : W), c n w = 0 → w ∈ (Ideal.span {p ^ n} • ⊤ : Submodule O W))
    (hsmul : ∀ (n : ℕ) (a : O) (w : W), c n (a • w) = a • c n w)
    (hkill : ∀ (n : ℕ) (x : C n), p ^ n • x = 0)
    (u : ∀ n, C n) (hcomp : ∀ (n : ℕ) (w : W), c (n + 1) w = u (n + 1) → c n w = u n) :
    ∃ w : W, ∀ n, c n w = u n := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' O W
  have step : ∀ (n : ℕ) (a : Fin k → O), c n (f a) = u n → ∃ a' : Fin k → O,
      c (n + 1) (f a') = u (n + 1) ∧ ∃ b : Fin k → O, a' = a + p ^ n • b := by
    intro n a ha
    obtain ⟨w', hw'⟩ := hsurj (n + 1) (u (n + 1))
    have h1 : c n (w' - f a) = 0 := by rw [map_sub, hcomp n w' hw', ha, sub_self]
    have h2 := hker n _ h1
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
    obtain ⟨v, -, hv⟩ := h2
    obtain ⟨b, rfl⟩ := hf v
    refine ⟨a + p ^ n • b, ?_, b, rfl⟩
    rw [map_add, map_smul, hv, add_sub_cancel, hw']
  choose! g hg using step
  let a : ℕ → Fin k → O := fun n => Nat.rec 0 (fun m x => g m x) n
  have h0 : ∀ x : C 0, x = 0 := fun x => by simpa using hkill 0 x
  have ha : ∀ n, c n (f (a n)) = u n := by
    intro n
    induction n with
    | zero => rw [h0 (c 0 _), h0 (u 0)]
    | succ n ih => exact (hg n _ ih).1
  have hd : ∀ n, ∃ b : Fin k → O, a (n + 1) = a n + p ^ n • b := fun n => (hg n _ (ha n)).2
  have hcong : ∀ m n, m ≤ n → ∀ i, ∃ e : O, a n i = a m i + p ^ m * e := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact fun i => ⟨0, by simp⟩
    | succ n hmn ih =>
      intro i
      obtain ⟨e, he⟩ := ih i
      obtain ⟨b, hb⟩ := hd n
      refine ⟨e + p ^ (n - m) * b i, ?_⟩
      rw [hb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, he, ← pow_mul_pow_sub p hmn]
      ring
  have hmem : ∀ (m : ℕ) (x y : O),
      x ≡ y [SMOD (Ideal.span {p} ^ m • ⊤ : Submodule O O)] ↔ ∃ e : O, y = x + p ^ m * e := by
    intro m x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨e, he⟩
      exact ⟨-e, by rw [mul_neg, mul_comm, he]; ring⟩
    · rintro ⟨e, rfl⟩
      exact ⟨-e, by ring⟩
  choose L hL using fun i => IsPrecomplete.prec' (I := Ideal.span {p}) (fun n => a n i)
    fun {m n} hmn => (hmem m _ _).2 (hcong m n hmn i)
  refine ⟨f L, fun n => ?_⟩
  choose e he using fun i => (hmem n _ _).1 (hL i n)
  have hLe : L = a n + p ^ n • e := funext fun i => by
    rw [he i, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hLe, map_add, map_smul, map_add, hsmul, hkill, add_zero, ha]

end GlobalTheory.CompatLift

namespace GlobalTheory.SqZeroPt

theorem cn_hits_compatible : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), Module.Finite O (Wmod A) → (∀ n, Function.Surjective (cn t n)) → (∀ (n : ℕ) (w : Wmod A), cn t n w = 0 → w ∈ (Ideal.span {(p : O) ^ n} • ⊤ : Submodule O (Wmod A))) → (∀ (n : ℕ) (w : Wmod A), GlobalTheory.PDiv.cotMap (G.res n) (cn t (n + 1) w) = cn t n w) → (∀ (n : ℕ) (c : O) (w : Wmod A), cn t n (c • w) = c • cn t n w) → ∀ u : G.omega, ∃ w, ∀ n, cn t n w = u.1 n := by
  intro p O _ _ G A _ t hfin hsurj hker hres hsmul u
  exact GlobalTheory.CompatLift.exists_of_compat (p : O) (C := fun n => GlobalTheory.PDiv.Cot O (G.A n)) (cn t)
    hsurj hker hsmul (fun n x => G.pow_smul_cot n x) (fun n => u.1 n)
    fun n w hw => by rw [← hres n w, hw]; exact u.2 n

end GlobalTheory.SqZeroPt
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cotangent_inverse_limit_compatible : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), Module.Finite O (Wmod A) → (∀ n, Function.Surjective (cn t n)) → (∀ (n : ℕ) (w : Wmod A), cn t n w = 0 → w ∈ (Ideal.span {(p : O) ^ n} • ⊤ : Submodule O (Wmod A))) → (∀ (n : ℕ) (w : Wmod A), GlobalTheory.PDiv.cotMap (G.res n) (cn t (n + 1) w) = cn t n w) → (∀ (n : ℕ) (c : O) (w : Wmod A), cn t n (c • w) = c • cn t n w) → ∀ u : G.omega, ∃ w, ∀ n, cn t n w = u.1 n := by
  atlas_forward_decl GlobalTheory.SqZeroPt.cn_hits_compatible
end

section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.PDiv in

theorem GlobalTheory.PDivGroup.TorsionTower.existsUnique_tangent : ∀ (p : ℕ) (O : Type) [CommRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O))
    [GrpObj A] [Smooth A.hom] (t : G.TorsionTower A) (x : G.Lie), ∃! v : epsR O ⟶ A, t.LieCorr x v := by
  intro p O _ _ G A _ _ t x
  have hfr := GlobalTheory.T.exists_cotangent_frame_smooth_groupScheme O A
  haveI hq : (GlobalTheory.LieVB.omega A).IsQuasicoherent := GlobalTheory.OmegaGlobal.isQuasicoherent_of_frames hfr
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.finite_projective_cotangentGlobalSections_groupScheme O A hfr
  have hnat := GlobalTheory.T.tangent_Phi_sqZero_naturality O
  have hinj := GlobalTheory.T.sqZeroPoint_eq_of_cotangentForm_eq O A hq
  have hsurj := GlobalTheory.T.tangent_Phi_surjective_onto_dual O A hq
  have hspec := GlobalTheory.T.tangent_Phi_naturality_module p O G A t (hnat · · A)
  have hl : ∀ n (c : O) w, cn t n (c • w) = c • cn t n w := fun n c w => GlobalTheory.T.tangent_Phi_smul O _ A _ _ c w
  have hres := GlobalTheory.T.tangent_Phi_naturality_linear p O G A t (hnat · · A)
  have hon := GlobalTheory.T.cotangent_inverse_limit_compatible p O G A t hfin (GlobalTheory.T.tangent_Phi_injective_criterion p O G A t hinj hspec)
    (GlobalTheory.T.tangent_Phi_naturality_family p O G A t hfin hproj (hnat · · A) hsurj hspec) hres hl
  have htan := GlobalTheory.T.tangent_Phi_naturality_pair p O G A t (hnat · · A) hspec
  let c : Wmod A →ₗ[O] G.omega :=
    { toFun := fun w => ⟨fun n => cn t n w, fun n => hres n w⟩
      map_add' := fun w w' => Subtype.ext (funext fun n => map_add (cn t n) w w')
      map_smul' := fun a w => Subtype.ext (funext fun n => hl n a w) }
  have hmk : ∀ (n : ℕ) (a b : O), a ≡ b [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] ↔
      (Ideal.Quotient.mk _ a : ModPow p O n) = Ideal.Quotient.mk _ b := fun n a b => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.Quotient.eq]
  have hu : ∀ a b : O, (∀ n, (Ideal.Quotient.mk _ a : ModPow p O n) = Ideal.Quotient.mk _ b) →
      a = b := fun a b h => sub_eq_zero.1 <| IsHausdorff.haus' (I := Ideal.span {(p : O)}) _
        fun n => SModEq.zero.2 (SModEq.sub_mem.1 ((hmk n a b).2 (h n)))
  obtain ⟨v, hv0, hvμ⟩ := hsurj (x ∘ₗ c)
  have hv : IsTangent v := congrArg Over.Hom.left hv0
  refine ⟨v, (t.lieCorr_iff hv x).2 fun n u => ?_, fun y hy => ?_⟩
  · obtain ⟨w, hw⟩ := hon u
    have e : u = c w := Subtype.ext (funext fun n => (hw n).symm)
    rw [← hw n, htan v hv hv0 n w, hvμ, e]
    rfl
  · have hy' : IsTangent y := hy.1
    have hy0 : zeroSec O O ≫ y = η[A] := Over.OverMorphism.ext hy'
    refine hinj O y v hy0 hv0 fun w => ?_
    rw [hvμ]
    refine hu _ _ fun n => ?_
    rw [← htan y hy' hy0 n w]
    exact ((t.lieCorr_iff hy' x).1 hy n (c w)).symm
end

section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.KernelNoTorsion
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RaynaudPDiv

theorem card_torsion_pow_of_divisible : ∀ (p : ℕ) [Fact p.Prime] (M : Type) [CommGroup M], (∀ y : M, ∃ x : M, x ^ p = y) → Nat.card {x : M // x ^ p = 1} ≠ 0 → ∃ h : ℕ, ∀ n : ℕ, Nat.card {x : M // x ^ p ^ n = 1} = p ^ (n * h) := by
  intro p hp M _ hd h1
  have hp' : p.Prime := hp.out
  let K : ℕ → Subgroup M := fun k => (powMonoidHom k : M →* M).ker
  have hK : ∀ k, Nat.card (K k) = Nat.card {x : M // x ^ k = 1} := fun k => rfl
  haveI : Finite (K p) := Nat.finite_of_card_ne_zero h1
  obtain ⟨h, hh⟩ := (IsPGroup.iff_card (p := p) (G := K p)).1 fun g => ⟨1, Subtype.ext (by rw [pow_one]; exact g.2)⟩
  refine ⟨h, fun n => ?_⟩
  induction n with
  | zero =>
    simp only [pow_zero, pow_one, zero_mul]
    exact Nat.card_unique
  | succ n ih =>
    let f : K (p ^ (n + 1)) →* K (p ^ n) := ((powMonoidHom p : M →* M).comp (K _).subtype).codRestrict _
      fun x => show (x.1 ^ p) ^ p ^ n = 1 by rw [← pow_mul, ← pow_succ']; exact x.2
    have hf : Function.Surjective f := fun y => by
      obtain ⟨x, hx⟩ := hd y.1
      exact ⟨⟨x, show x ^ p ^ (n + 1) = 1 by rw [pow_succ', pow_mul, hx]; exact y.2⟩, Subtype.ext hx⟩
    have hk : Nat.card f.ker = Nat.card (K p) := Nat.card_congr
      { toFun := fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩
        invFun := fun x => ⟨⟨x.1, show x.1 ^ p ^ (n + 1) = 1 by
          rw [pow_succ', pow_mul, show x.1 ^ p = 1 from x.2, one_pow]⟩, Subtype.ext x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← hK, Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, hk, hh,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, hK, ih, ← pow_add, add_mul,
      _root_.one_mul]

theorem exists_isPullback_torsion : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A] [Smooth A.hom] (N : ℕ), IsFinite (torsion A N).hom → Flat (torsion A N).hom → ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (y : SpAlg O R ⟶ A), Module.Finite O R ∧ Module.Projective O R ∧ IsPullback y.left (spMap (algebraMap O R)) (mulN A N).left η[A].left := by
  intro O _ A _ _ N h1 h2
  have : LocallyOfFinitePresentation ((mulN A N).left ≫ A.hom) := by rw [Over.w]; infer_instance
  have h3 := TangentCrit.locallyOfFinitePresentation_of_comp (mulN A N).left A.hom
  let e : Sp O ⟶ A.left := η[A].left
  let X := (torsion A N).left
  have H0 : IsPullback (torsion.ι A N).left (torsion A N).hom (mulN A N).left e := by
    have h := (IsPullback.of_hasPullback (mulN A N) (η : 𝟙_ _ ⟶ A)).map (Over.forget _)
    have h' : (pullback.snd (mulN A N) (η : 𝟙_ _ ⟶ A)).left = (torsion A N).hom :=
      (Category.comp_id _).symm.trans (Over.w (pullback.snd (mulN A N) (η : 𝟙_ _ ⟶ A)))
    exact h' ▸ h
  have : IsAffine X := isAffine_of_isAffineHom (torsion A N).hom
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ (torsion A N).hom)
  have H : IsPullback (X.isoSpec.inv ≫ (torsion.ι A N).left) (Spec.map ψ) (mulN A N).left e := by
    rw [hψ]
    refine H0.of_iso X.isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  have f1 : ψ.hom.Finite := (IsFinite.SpecMap_iff _).1 (by rw [hψ]; infer_instance)
  have f2 : ψ.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 (by rw [hψ]; infer_instance)
  have f3 : ψ.hom.FinitePresentation := (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1
    (MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) H h3)
  let _ : Algebra O Γ(X, ⊤) := ψ.hom.toAlgebra
  have : Module.Finite O Γ(X, ⊤) := f1
  have : Module.Flat O Γ(X, ⊤) := f2
  have : Algebra.FinitePresentation O Γ(X, ⊤) := f3
  have := Module.FinitePresentation.of_finite_of_finitePresentation O Γ(X, ⊤)
  exact ⟨Γ(X, ⊤), inferInstance, inferInstance,
    Over.homMk (X.isoSpec.inv ≫ (torsion.ι A N).left) (by rw [Category.assoc, Over.w]; exact hψ.symm),
    inferInstance, Module.Flat.projective_of_finitePresentation, H⟩

theorem finrank_torsion : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] [Smooth B.hom] (N : ℕ), (N : K) ≠ 0 → ∀ (S : Type) [CommRing S] [Algebra K S] [Module.Finite K S] (y : SpAlg K S ⟶ B), IsPullback y.left (spMap (algebraMap K S)) (mulN B N).left η[B].left → Module.finrank K S = Nat.card {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ N = 1} ∧ Module.finrank K S ≠ 0 := by
  intro K _ _ B _ _ _ N hN S _ _ _ y h
  have he : Etale (mulN B N).left := GrpTangent.etale_mulN B (by
    simpa using (Ne.isUnit hN).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  have : Algebra.Etale K S := RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1
    (MorphismProperty.of_isPullback (P := @Etale) h he))
  have hy := AbelianPDiv.isUnivTorsion_of_isPullback y h
  have : Nontrivial S := hy.counitMap.toRingHom.domain_nontrivial
  refine ⟨?_, Module.finrank_pos.ne'⟩
  rw [← natCard_algHom_eq_finrank_of_etale K S K]
  let i : SpAlg K K ≅ 𝟙_ (Over (Sp K)) := Over.isoMk (Iso.refl _) (by
    exact (Category.comp_id _).trans (Cris.spMap_id K).symm)
  refine Nat.card_eq_of_bijective (fun φ => ⟨i.inv ≫ spOver φ ≫ y, by
    rw [← MonObj.comp_pow, ← MonObj.comp_pow, hy.1, MonObj.comp_one, MonObj.comp_one]⟩) ⟨fun φ ψ e => ?_, fun x => ?_⟩
  · exact hy.inj ((cancel_epi i.inv).1 (congrArg Subtype.val e))
  · obtain ⟨φ, hφ, -⟩ := hy.2 K (i.hom ≫ x.1) (by rw [← MonObj.comp_pow, x.2, MonObj.comp_one])
    exact ⟨φ, Subtype.ext (by simp only [hφ, Iso.inv_hom_id_assoc])⟩

theorem exists_tateEquiv : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A] (G : PDivGroup p O) (t : G.TorsionTower A), ∃ e : G.Tate ≃ₗ[ℤ_[p]] GlobalTheory.HTLat.Tate p (specO O O ⟶ A), ∀ (s : G.Tate) (n : ℕ), (e s).lev n = spOver (s.pt n) ≫ t.y n := by
  intro p _ O _ A _ _ G t
  have hc : ∀ (n : ℕ) (φ : G.A (n + 1) →ₐ[O] O), spOver (φ.comp (G.mulP n : G.A n →ₐ[O] G.A (n + 1))) ≫ t.y n =
      (spOver φ ≫ t.y (n + 1)) ^ p := fun n φ => by
    rw [← spOver_comp, Category.assoc, t.mulP_y, MonObj.comp_pow]
  let f : G.Tate →ₗ[ℤ_[p]] GlobalTheory.HTLat.Tate p (specO O O ⟶ A) :=
    { toFun := fun s => Tate.mk (fun n => spOver (s.pt n) ≫ t.y n) fun n =>
        ⟨(t.exists_iff n _).1 ⟨_, rfl⟩, (hc n _).symm.trans (by rw [s.compat])⟩
      map_add' := fun s s' => Tate.ext fun n => map_mul (t.pts n O) (s.conv n) (s'.conv n)
      map_smul' := fun a s => Tate.ext fun n => map_pow (t.pts n O) (s.conv n) _ }
  refine ⟨.ofBijective f ⟨fun s s' h => TateOver.ext (funext fun n => t.inj n O _ _ (congrArg (·.lev n) h)),
    fun z => ⟨⟨fun n => t.lift n (z.lev n) (z.lev_pow n), fun n => t.inj n O _ _ ?_⟩,
      Tate.ext fun n => t.lift_y n _ (z.lev_pow n)⟩⟩, fun _ _ => rfl⟩
  rw [hc, t.lift_y, t.lift_y]
  exact z.lev_succ n

theorem exists_dual_tate : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A] (G : PDivGroup p O) (t : G.TorsionTower A) (χ : Tv A p), ∃ c : G.dual.Tate, ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (φ : G.A n →ₐ[O] B) (w : specO O B ⟶ torsion A (p ^ n)), w ≫ torsion.ι A (p ^ n) = spOver φ ≫ t.y n → φ (charElem c n) = (unitOf (w ≫ χ.χ n) : B) := by
  intro p _ O _ A _ G t χ
  let l : ∀ n, specO O (G.A n) ⟶ torsion A (p ^ n) := fun n => torsionLift (t.y n) (t.y_pow n)
  have hl : ∀ n, l n ≫ torsion.ι A (p ^ n) = t.y n := fun n => torsionLift_ι _ _
  let u : ∀ n, G.A n := fun n => unitOf (l n ≫ χ.χ n)
  have h0 : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (φ : G.A n →ₐ[O] B),
      φ (u n) = (unitOf ((spOver φ ≫ l n) ≫ χ.χ n) : B) := fun n B _ _ φ => by
    rw [Category.assoc]
    exact (GmPoints.unitOf_ptMap φ _).symm
  have hm : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (φ ψ : WithConv (G.A n →ₐ[O] B)),
      (φ * ψ).ofConv (u n) = φ.ofConv (u n) * ψ.ofConv (u n) := fun n B _ _ φ ψ => by
    rw [h0, h0, h0, ← Units.val_mul, ← GmPoints.unitOf_mul]
    refine congrArg (fun z : specO O B ⟶ Gm (Sp O) => (unitOf z : B)) (χ.isChar n _ _ _ _ ?_)
    rw [Category.assoc, Category.assoc, Category.assoc, hl]
    exact t.mul n B φ ψ
  have hg : ∀ n, IsGroupLikeElem O (u n) := fun n => by
    constructor
    · have h := hm n O 1 1
      rw [_root_.mul_one] at h
      exact ((Units.isUnit _).map (1 : WithConv (G.A n →ₐ[O] O)).ofConv).mul_left_cancel
        (h.symm.trans (_root_.mul_one _).symm)
    · have h := hm n (G.A n ⊗[O] G.A n) (WithConv.toConv Algebra.TensorProduct.includeLeft)
        (WithConv.toConv Algebra.TensorProduct.includeRight)
      rw [AlgHom.convMul_apply] at h
      simpa using h
  have hp : ∀ n, u n ^ p ^ n = 1 := fun n => by
    have h := convPow_apply_groupLike (WithConv.toConv (AlgHom.id O (G.A n))) (hg n) (p ^ n)
    rw [G.pts_pow_self] at h
    refine h.symm.trans ?_
    simp [(hg n).counit_eq_one]
  have hr : ∀ n, G.res n (u (n + 1)) = u n := fun n =>
    (h0 (n + 1) _ (G.res n : G.A (n + 1) →ₐ[O] G.A n)).trans (congrArg (fun z : specO O (G.A n) ⟶ Gm (Sp O) => (unitOf z : G.A n))
      (χ.compat n _ _ _ ((hl n).trans ((t.res n).symm.trans (by rw [Category.assoc, hl])))).symm)
  let f : G ⟶ PDivGroup.mu p O := ⟨fun n => muChar (u n) (hg n) (hp n), fun n => mu_bialgHom_ext <| by
    rw [BialgHom.comp_apply, BialgHom.comp_apply, muChar_muT, hr, muRes_muT, muChar_muT]⟩
  refine ⟨(charHom G).symm f, fun n B _ _ φ w hw => ?_⟩
  rw [← charHom_app_muT, LinearEquiv.apply_symm_apply,
    show w = spOver φ ≫ l n from torsion_hom_ext (by rw [Category.assoc, hl, hw]), ← h0]
  exact congrArg φ (muChar_muT _ (hg n) (hp n))

theorem lie_dlog : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (A : Over (Sp O)) [GrpObj A] (G : PDivGroup p O) (t : G.TorsionTower A) (χ : Tv A p) (c : G.dual.Tate), (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (φ : G.A n →ₐ[O] B) (w : specO O B ⟶ torsion A (p ^ n)), w ≫ torsion.ι A (p ^ n) = spOver φ ≫ t.y n → φ (charElem c n) = (unitOf (w ≫ χ.χ n) : B)) → ∀ (x : LieG A) (y : G.Lie), t.LieCorr y x.1 → y (PDivGroup.dlog G c) = (dlogTv χ).1 x := by
  intro p _ O _ _ A _ G t χ c hc x y h
  refine sub_eq_zero.1 (IsHausdorff.haus' (I := Ideal.span {(p : O)}) _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, ← Ideal.Quotient.eq]
  obtain ⟨ψ, h1, h2⟩ := h.2 n
  let w : specO O (DualNumber (ModPow p O n)) ⟶ torsion A (p ^ n) := torsionLift _ (epsRedPow_pow (p := p) h.1 n)
  have h3 : w ≫ torsion.ι A (p ^ n) = epsRedPow p n x.1 := torsionLift_ι _ _
  have h4 : epsTo O (ModPow p O n) = dualBC (Algebra.ofId O (ModPow p O n)) := AlgHom.ext fun z => by
    ext <;> simp [dualBC, TrivSqZeroExt.lift_def, TrivSqZeroExt.algebraMap_eq_inl']
  have h0 : (p : ModPow p O n) ^ n = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have h5 := isAl_dlogTv χ n _ h0 x w (h3.trans (by rw [← h4]; rfl))
  refine (h2 _ (charElem c n) (dlog_val c n).symm).trans ?_
  rw [hc n _ ψ w (h3.trans h1.symm), h5]
  simp

theorem exists_tower (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] (h0 : (p : O) ≠ 0)
    (A : Over (Sp O)) [GrpObj A] (hA : IsSemiAbelian A)
    (hf : ∀ N, 1 ≤ N → IsFinite (torsion A N).hom ∧ Flat (torsion A N).hom) :
    ∃ G : PDivGroup p O, Nonempty (G.TorsionTower A) := by
  have := hA.comm
  have := hA.smooth
  let K := AlgebraicClosure (FractionRing O)
  have hi : Function.Injective (algebraMap O K) :=
    (algebraMap (FractionRing O) K).injective.comp (IsFractionRing.injective O _)
  let B := (Over.pullback (spMap (algebraMap O K))).obj A
  have : Smooth B.hom := inferInstanceAs (Smooth (pullback.snd A.hom _))
  choose R _ _ y h1 h2 H using fun n : ℕ =>
    exists_isPullback_torsion O A (p ^ n) (hf _ (one_le_ppow p n)).1 (hf _ (one_le_ppow p n)).2
  have h := fun n => AbelianPDiv.isUnivTorsion_of_isPullback (y n) (H n)
  have hk : ∀ n, Module.finrank K (K ⊗[O] R n) = Nat.card {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ p ^ n = 1} ∧
      Module.finrank K (K ⊗[O] R n) ≠ 0 := fun n => by
    obtain ⟨y', h'⟩ := AbelianPDiv.exists_isPullback_baseChange (y n) (H n) K
    exact finrank_torsion K B _ (by
      rw [← map_natCast (algebraMap O K), Nat.cast_pow]
      exact (map_ne_zero_iff _ hi).2 (pow_ne_zero _ h0)) _ y' h'
  obtain ⟨d, hd⟩ := card_torsion_pow_of_divisible p (𝟙_ (Over (Sp K)) ⟶ B)
    (SS.torusExtension_points_divisible K B (hA.fibres K _) p hp.out.pos)
    (by have h := (hk 1).2; rwa [(hk 1).1, pow_one] at h)
  have hr : ∀ n (q : PrimeSpectrum O), Module.rankAtStalk (R n) q = p ^ (n * d) := fun n q => by
    rw [← Module.rankAtStalk_eq_of_le_of_finite_of_flat (R n)
        (p := PrimeSpectrum.comap (algebraMap O K) ⊥) (q := q) ?_, ← Module.rankAtStalk_baseChange,
      Module.rankAtStalk_eq_finrank_of_free, (hk n).1, hd]
    · rfl
    · intro a ha
      have ha' : algebraMap O K a = 0 := ha
      rw [(map_eq_zero_iff _ hi).1 ha']
      exact zero_mem _
  choose r r1 r2 r3 using fun n : ℕ =>
    (h n).exists_res (h (n + 1)) (by rw [pow_succ, pow_mul, (h n).1, one_pow])
  let G : PDivGroup p O :=
    { height := d
      A := R
      hopf := fun n => (h n).hopfAlgebra
      cocomm := fun n => (h n).isCocomm
      finite := h1
      projective := h2
      rank_eq := hr
      res := r
      res_surjective := r1
      ker_res := r2 }
  exact ⟨G, ⟨{
    y := y
    mul := fun n B _ _ => (h n).mul_y
    inj := fun n B _ _ _ _ => (h n).inj
    surj := fun n B _ _ z hz => ((h n).2 B z hz).exists
    res := r3 }⟩⟩

theorem exists_lieEquiv (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (A : Over (Sp O)) [GrpObj A] [Smooth A.hom] (G : PDivGroup p O) (t : G.TorsionTower A) :
    ∃ l : LieG A ≃ G.Lie, ∀ x, t.LieCorr (l x) x.1 := by
  have ht : ∀ v : epsR O ⟶ A, ptMap (TrivSqZeroExt.fstHom O O O) ≫ v = toUnit (specO O O) ≫ η[A] ↔
      IsTangent v := fun v => by
    have e : (toUnit (specO O O) ≫ η[A]).left = η[A].left :=
      (AbelianPDiv.one_left O).trans ((congrArg (· ≫ η[A].left) (Cris.spMap_id O)).trans (Category.id_comp _))
    exact ⟨fun h => (congrArg Over.Hom.left h).trans e, fun h => Over.OverMorphism.ext (h.trans e.symm)⟩
  choose f hf using fun x : LieG A => (t.existsUnique_lieCorr ((ht _).1 x.2)).exists
  refine ⟨.ofBijective f ⟨fun x x' e => Subtype.ext ?_, fun y => ?_⟩, hf⟩
  · exact (TorsionTower.existsUnique_tangent p O G A t (f x)).unique (hf x) (e ▸ hf x')
  · obtain ⟨v, hv⟩ := (TorsionTower.existsUnique_tangent p O G A t y).exists
    exact ⟨⟨v, (ht v).2 hv.1⟩, (hf _).unique_left hv⟩

theorem exists_generator {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) (ε : Eps p C) :
    ∃ ζ : (PDivGroup.mu p O).Tate, Function.Bijective (fun a : ℤ_[p] => a • ζ) ∧
      ∀ n, algebraMap O C (muRoot ζ n) = ε.1.lev n := by
  have hi := hv.hom_inj
  have h1 : ∀ n, ((ε.1.lev n : Cˣ) : C) ^ p ^ n = 1 := fun n => by
    rw [← Units.val_pow_eq_pow_val, ε.1.lev_pow, Units.val_one]
  choose z hz using fun n => hv.exists_of_le_one (r := (ε.1.lev n : C))
    ((pow_le_one_iff_of_nonneg zero_le (Nat.one_le_iff_ne_zero.1 (one_le_ppow p n))).1
      (show v (ε.1.lev n : C) ^ p ^ n ≤ 1 by rw [← map_pow, h1, map_one]))
  let ζ := muTate O z (hi (by simpa [hz] using h1 0)) fun n => hi (by
    rw [map_pow, hz, hz, ← Units.val_pow_eq_pow_val, ε.1.lev_succ])
  have hζ : ∀ n, algebraMap O C (muRoot ζ n) = ε.1.lev n := fun n => by rw [muRoot_muTate, hz]
  have hs : ∀ (a : ℤ_[p]) n, algebraMap O C (muRoot (a • ζ) n) = (a • ε.1).lev n := fun a n => by
    rw [muRoot_smul, map_pow, hζ, Tate.lev_smul, Units.val_pow_eq_pow_val]
  refine ⟨ζ, ⟨fun a b e => ε.bijective.1 (Tate.ext fun n => Units.ext ?_), fun x => ?_⟩, hζ⟩
  · exact (hs a n).symm.trans ((congrArg (fun w => algebraMap O C (muRoot w n)) e).trans (hs b n))
  · have hx : ∀ n, algebraMap O C (muRoot x n) ^ p ^ n = 1 := fun n => by
      rw [← map_pow, muRoot_pow_self, map_one]
    obtain ⟨a, ha⟩ := ε.bijective.2 (Tate.mk (fun n => Units.ofPowEqOne _ _ (hx n)
      (Nat.one_le_iff_ne_zero.1 (one_le_ppow p n))) fun n => ⟨Units.ext (hx n), Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_ofPowEqOne, Units.val_ofPowEqOne, ← map_pow, muRoot_succ_pow])⟩)
    exact ⟨a, muRoot_ext fun n => hi ((hs a n).trans (congrArg (fun w => ((w.lev n : Cˣ) : C)) ha))⟩

theorem exists_pDivGroup_raynaud : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.tateGt) (l : ReciprocityTheory.ChartRestriction.G.Pdiv.LieG P.Gt ≃ G.Lie) (c : P.T →ₗ[ℤ_[p]] G.dual.Tate) (ζ : (PDivGroup.mu p O).Tate), Function.Bijective (fun a : ℤ_[p] => a • ζ) ∧ (∀ s t, PDivGroup.pairing G O s (c t) = pairT P.A P.eps (e s : P.T) t • ζ) ∧ ∀ x t, l x (PDivGroup.dlog (G := G) (c t)) = (P.al₀ t).1 x := by
  intro p hp C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  have hi := P.integers.hom_inj
  haveI : IsDomain O := hi.isDomain (algebraMap O C)
  have hA := isSemiAbelian_of_isGt _ _ P.Gt ⟨P.D⟩
  haveI := hA.smooth
  obtain ⟨G, ⟨t⟩⟩ := exists_tower p O (fun h => hp.out.ne_zero ((Nat.cast_eq_zero (R := C)).1 (by
    rw [← map_natCast (algebraMap O C), h, map_zero]))) P.Gt hA P.finite_flat
  obtain ⟨e, he⟩ := exists_tateEquiv p O P.Gt G t
  obtain ⟨l, hl⟩ := exists_lieEquiv p O P.Gt G t
  obtain ⟨ζ, hζ, hζ'⟩ := exists_generator P.integers P.eps
  choose c hc using fun s : P.T => exists_dual_tate p O P.Gt G t (P.weilChar s)
  have hu : ∀ s n, charElem (c s) n = (unitOf (torsionLift (t.y n) (t.y_pow n) ≫ (P.weilChar s).χ n) : G.A n) :=
    fun s n => hc s n _ (AlgHom.id O _) _ (by rw [torsionLift_ι, spOver_id, Category.id_comp])
  have hx : ∀ {a b : G.dual.Tate}, (∀ n, charElem a n = charElem b n) → a = b := fun h =>
    (charHom G).injective (hom_mu_ext fun n => by rw [charHom_app_muT, charHom_app_muT, h])
  have hadd : ∀ s s', c (s + s') = c s + c s' := fun s s' => hx fun n => by
    rw [charElem_add, hu, hu, hu, P.weilChar_add, MonObj.comp_mul, GmPoints.unitOf_mul, Units.val_mul]
  have hpow : ∀ (R : Type) [CommRing R] [Algebra O R] (w : specO O R ⟶ Gm (Sp O)) (k : ℕ),
      unitOf (w ^ k) = unitOf w ^ k := fun R _ _ w k => map_pow (MonoidHom.mk' unitOf GmPoints.unitOf_mul) w k
  have hsm : ∀ (a : ℤ_[p]) s, c (a • s) = a • c s := fun a s => hx fun n => by
    have h : (P.weilChar (a • s)).χ n = (P.weilChar s).χ n ^ digit n a := P.char_ext fun w => by
      rw [P.isWeilChar_weilChar, MonObj.comp_pow, hpow, Units.val_pow_eq_pow_val, map_pow,
        P.isWeilChar_weilChar, Tate.lev_smul, weil_pow_right (one_le_ppow p n) (s.lev_pow n) (P.toA_pow w),
        Units.val_pow_eq_pow_val]
    rw [charElem_smul, hu, hu, h, MonObj.comp_pow, hpow, Units.val_pow_eq_pow_val]
  refine ⟨G, e.trans (LinearEquiv.ofInjective _ (Tate.map_injective P.toA_injective)), l,
    ⟨⟨c, hadd⟩, hsm⟩, ζ, hζ, fun s s' => muRoot_ext fun n => hi ?_,
    fun x s => lie_dlog p O P.Gt G t _ _ (hc s) x _ (hl x)⟩
  have hw := torsionLift_ι _ ((t.exists_iff n _).1 ⟨s.pt n, rfl⟩)
  rw [muRoot_pairing, muRoot_smul, map_pow, hζ', ← Units.val_pow_eq_pow_val, pow_pairT]
  refine (congrArg (algebraMap O C) (hc s' n O _ _ hw)).trans ((P.isWeilChar_weilChar s' n _).trans ?_)
  rw [hw, ← he]
  rfl

end GlobalTheory.RaynaudPDiv
end
