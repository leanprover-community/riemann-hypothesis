import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImageCocycleSemilinearSheafComplexMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendChainMapAlongQuasiIsoKInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexSemilinearMapCompBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughExtendScalarsZmod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsTateTwistAugmentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCoefficientReductionCupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrFamAddTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneralLinearGroupDetMapFinOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwistAltI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestrict

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_through_extendScalars_zmod : ∀ (Q q : ℕ) (hq : q ∣ Q) (I : Cx (ZMod Q)) (K : Cx (ZMod q)) (ρ : SemiMap I K), ∃ u : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K, ∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U), ρ.app U s a = Sec.map (u.f s) ((extπ (ZMod.castHom hq (ZMod q)) I).app U s a) := by
  first | exact @GlobalTheory.EtC.SemiMap.factor_extCx | exact GlobalTheory.EtC.SemiMap.factor_extCx | (intros; apply GlobalTheory.EtC.SemiMap.factor_extCx <;> assumption)
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

section
variable {R S : Type} [CommRing R] [CommRing S]

theorem secMap_res' {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) :=
  (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (f.hom.naturality g.op)) x).symm

theorem secMap_nsmul' {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map f (c • x) = c • Sec.map f x :=
  map_nsmul (f.hom.app (op U)).hom c x

theorem secMap_zero' {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} :
    Sec.map f (0 : Sec F U) = 0 :=
  map_zero (f.hom.app (op U)).hom

theorem extSh_hom_ext (φ : R →+* S) {F : Shv R} {M : Shv S} (a b : (extSh φ).obj F ⟶ M)
    (h : ∀ (U : Scheme.{0}) (y : Sec F U), Sec.map a (extSh.sec φ F U y) = Sec.map b (extSh.sec φ F U y)) : a = b := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (J := Scheme.etaleTopology) (P := F.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ))
    a.hom b.hom M.cond ?_
  ext U : 2
  apply ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext y
  exact h (unop U) y

end

theorem extAug_comp_ext : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ) (K : Cx (ZMod q))
    (u u' : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K),
    (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)),
      Sec.map (u.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ)) =
        Sec.map (u'.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ))) →
    extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u = extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u' := by
  intro Q q _ hq i K u u' h
  have e : ∀ (v : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K) (V : Scheme.{0}) (z : Sec (tw Q i) V),
      Sec.map ((extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ v.f 0)
          (extSh.sec (ZMod.castHom hq (ZMod q)) (tw Q i) V z) =
        Sec.map (v.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app V 0 (Sec.map (resι _ (tw Q i)) z)) := by
    intro v V z
    change Sec.map (v.f 0) (Sec.map ((extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i))) _) = _
    rw [extSh.sec_map]
    rfl
  have key : (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ u.f 0 =
      (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ u'.f 0 := by
    apply extSh_hom_ext
    intro U y
    apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ (K.X 0) U).1
    obtain ⟨S, hS, hy⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated Q i).1 U y
    refine ⟨S, hS, fun V g hg => ?_⟩
    dsimp only
    rw [secMap_res', secMap_res', extSh.sec_res, e, e]
    rcases hy V g hg with h0 | ⟨ζ, c, hc⟩
    · rw [h0, secMap_zero', map_zero, secMap_zero', secMap_zero']
    · rw [hc, secMap_nsmul', map_nsmul, secMap_nsmul', secMap_nsmul']
      exact congrArg (c • ·) (h V ζ)
  have hv : ∀ v : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K, (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ v).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
        (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ v.f 0 := by
    intro v
    have hs := HomologicalComplex.singleMapHomologicalComplex_inv_app_self (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0 (tw Q i)
    change (((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0)) ≫
        v.f 0 = _
    have hs' : ((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
        (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0) =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
          (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) := by
      rw [hs]
      exact (Category.assoc _ _ _).trans (congrArg _ (Functor.map_comp _ _ _).symm)
    exact (congrArg (· ≫ v.f 0) hs').trans (Category.assoc _ _ _)
  apply HomologicalComplex.from_single_hom_ext
  rw [hv, hv, key]

end GlobalTheory.EtC
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendScalars_tateTwistResolution_hom_ext_augmentation : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ) (K : Cx (ZMod q)) (u u' : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map (u.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ)) = Sec.map (u'.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ))) → extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u = extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u' := by
  first | (exact @GlobalTheory.EtC.extAug_comp_ext) | (exact GlobalTheory.EtC.extAug_comp_ext) | (intros; apply GlobalTheory.EtC.extAug_comp_ext  <;> assumption)
end

section
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedUniq

theorem op_eq : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (i : ℤ) (ρ ρ' : SemiMap (res _ (tw Q i)) (res _ (tw q i))),
    (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), ρ.app U 0 (resGen i ζ) = ρ'.app U 0 (resGen i ζ)) →
    ∀ (E : Spc) (n : ℤ) (x : Ht Q E n i), ρ.op.app E n x = ρ'.op.app E n x := by
  intro Q q _ hq i ρ ρ' h E n x
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_factor_through_extendScalars_zmod Q q hq _ _ ρ
  obtain ⟨u', hu'⟩ := GlobalTheory.T.exists_factor_through_extendScalars_zmod Q q hq _ _ ρ'
  have e1 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective _ _ (extπ (ZMod.castHom hq (ZMod q)) (res _ (tw Q i))) ρ u hu).1 E n x
  have e2 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective _ _ (extπ (ZMod.castHom hq (ZMod q)) (res _ (tw Q i))) ρ' u' hu').1 E n x
  have hε := GlobalTheory.T.extendScalars_tateTwistResolution_hom_ext_augmentation Q q hq i _ u u' (fun U ζ => by rw [← hu, ← hu', h])
  haveI := GlobalTheory.T.quasiIso_extendScalars_tateTwist_augmentation Q q hq i
  haveI : (res (ZMod q) (tw q i)).IsKInjective :=
    inferInstanceAs ((injectiveResolution (tw q i)).cochainComplex.IsKInjective)
  haveI : (res (ZMod q) (tw q i)).IsStrictlyGE 0 :=
    inferInstanceAs ((injectiveResolution (tw q i)).cochainComplex.IsStrictlyGE 0)
  obtain ⟨H⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) _ _ (res _ (tw q i)) (extAug (ZMod.castHom hq (ZMod q)) (tw Q i))).2 u u' hε
  have e3 := ((GlobalTheory.T.hypercohomologyPullbackPushforward_functorial (ZMod q)).2.2.2.2 u u' ⟨H⟩ ((chains (ZMod q)).obj E) n).2
  rw [e1, e2, e3]

end GlobalTheory.EtC.RedUniq

end
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistReduction_cohomology_map_unique : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (i : ℤ) (ρ ρ' : SemiMap (res _ (tw Q i)) (res _ (tw q i))), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), ρ.app U 0 (resGen i ζ) = ρ'.app U 0 (resGen i ζ)) → ∀ (E : Spc) (n : ℤ) (x : Ht Q E n i), ρ.op.app E n x = ρ'.op.app E n x := by
  atlas_forward_decl GlobalTheory.EtC.RedUniq.op_eq
end

section
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedUnit

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map φ y) = Sec.map φ (Sec.res g y) := by
  have := congrArg (fun f => f.hom y) (φ.hom.naturality g.op)
  exact this.symm

theorem res_resGen {q : ℕ} [NeZero q] (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (ζ.map g.appTop.hom) := by
  unfold resGen
  rw [res_map, (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 V U g ζ]

theorem val_one_smul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (y : M) :
    (1 : ZMod q).val • y = y := by
  by_cases hq : q = 1
  · subst hq
    have : Subsingleton M := Module.subsingleton (ULift.{1} (ZMod 1)) M
    exact Subsingleton.elim _ _
  · haveI : Fact (1 < q) := ⟨by have := NeZero.ne q; omega⟩
    rw [ZMod.val_one, one_smul]

theorem resGen_zero_eq {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) : resGen 0 ζ = resGen 0 ξ := by
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).1
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.1 ζ ξ
  refine ⟨S, hS, fun W h hh => ?_⟩
  obtain ⟨a, ha⟩ := hP W h hh
  rw [res_resGen, res_resGen]
  have := (GlobalTheory.T.tateTwist_sections_locally_generated q 0).2.2.2.2.1 W (ζ.map h.appTop.hom) (ξ.map h.appTop.hom) a ha
  unfold resGen
  rw [this, zpow_zero, Units.val_one, val_one_smul]

end GlobalTheory.EtC.RedUnit

theorem GlobalTheory.EtC.red_one : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → red Q q E 0 0 (one Q E) = one q E := by
  intro Q q _ hqQ E hE
  haveI : NeZero q := ⟨fun h => by subst h; exact NeZero.ne Q (Nat.eq_zero_of_zero_dvd hqQ)⟩
  have hEq : Inv q E := fun U hU => by
    obtain ⟨k, hk⟩ := hqQ
    have := hE U hU
    rw [hk, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨α, hα1, hα2⟩ := (GlobalTheory.T.tateTwistUnitClass_rootClass_spec Q).1 E hE
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 0)).1 E 0 α
  have hred : red Q q E 0 0 (one Q E) = CohomologyClass.mk β := by
    rw [← hα1]; exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 0)).2 E 0 α β hβ
  rw [hred]
  refine (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.1 E hEq β fun U x ξ => ?_
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).1
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).1 (hE U ⟨x⟩)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hP V g hg
  obtain ⟨ξ', hξ'⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(V, ⊤)).2.2.2.2.2 q hqQ ζ
  rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β.1 0 0 _ V U g x, hβ 0 0 _ V (x.res g), hα2 V (x.res g) ζ,
    GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ 0 V ζ ξ' hξ', RedUnit.res_resGen]
  exact RedUnit.resGen_zero_eq _ _
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCoefficientReduction_unitClass : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → red Q q E 0 0 (one Q E) = one q E := by
  atlas_forward_decl GlobalTheory.EtC.red_one
end

section
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem defectSec_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U), Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defectSec Q q V (Units.map g.appTop.hom.toMonoidHom u) := by
  intro Q q _ hqQ U u hQ V g
  have hQV : IsUnit (Q : Γ(V, ⊤)) := by
    have := hQ.map g.appTop.hom
    simpa using this
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ V).1
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q V).2.2.2 hQV (Units.map g.appTop.hom.toMonoidHom u)) ?_
  rintro W h ⟨v, hv⟩
  have hres : Sec.res h (Sec.res g (defectSec Q q U u)) = Sec.res (h ≫ g) (defectSec Q q U u) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hres, GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ V _ hQV W h v hv]
  refine GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u hQ W (h ≫ g) v ?_
  rw [hv]
  ext
  simp [Scheme.Hom.comp_appTop] <;> rfl

end GlobalTheory.EtC.RedChern
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerReductionChernDefectSection_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U), Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defectSec Q q V (Units.map g.appTop.hom.toMonoidHom u) := by
  atlas_forward_decl GlobalTheory.EtC.RedChern.defectSec_res
end

section
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

private theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private theorem sec_res_sub {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x - y) = Sec.res g x - Sec.res g y := map_sub _ x y

private theorem sec_map_sub {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x - y) = Sec.map φ x - Sec.map φ y := map_sub _ x y

theorem red_chern_deg_one : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 1) U) (b : Sec ((res _ (tw q 1)).X 1) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g a = Sec.map ((res _ (tw Q 1)).d 0 1) (kumT Q V v)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (w : (Γ(V, ⊤))ˣ), w ^ q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g b = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V w)) → (redMap Q q 1).app U 1 a - b = Sec.map ((res _ (tw q 1)).d 0 1) (GlobalTheory.EtC.RedChern.defectSec Q q U u) := by
  intro Q q _ hqQ U u hQ a b ha hb
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).1 _ _ ?_
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u) ?_
  rintro V g ⟨v, hv⟩
  have hw : (v ^ (Q / q)) ^ q = Units.map g.appTop.hom.toMonoidHom u := by
    rw [← pow_mul, Nat.div_mul_cancel hqQ, hv]
  rw [sec_res_sub, (redMap Q q 1).nat, ha V g v hv, hb V g _ hw, ← (redMap Q q 1).comm, sec_res_map,
    GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u hQ V g v hv, defect, sec_map_sub]

end GlobalTheory.EtC.RedChern
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedChernCocycle_deg_one_sub_eq_differential : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 1) U) (b : Sec ((res _ (tw q 1)).X 1) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g a = Sec.map ((res _ (tw Q 1)).d 0 1) (kumT Q V v)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (w : (Γ(V, ⊤))ˣ), w ^ q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g b = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V w)) → (redMap Q q 1).app U 1 a - b = Sec.map ((res _ (tw q 1)).d 0 1) (GlobalTheory.EtC.RedChern.defectSec Q q U u) := by
  atlas_forward_decl GlobalTheory.EtC.RedChern.red_chern_deg_one
end

section
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u₁ u₂ : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 0) U) (b : Sec ((res _ (tw q 1)).X 0) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ Q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g a = kumT Q V v + kumT Q V w - kumT Q V (v * w)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g b = kumT q V v + kumT q V w - kumT q V (v * w)) → (redMap Q q 1).app U 0 a - b = GlobalTheory.EtC.RedChern.defectSec Q q U u₂ - GlobalTheory.EtC.RedChern.defectSec Q q U (u₁ * u₂) + GlobalTheory.EtC.RedChern.defectSec Q q U u₁ := by
  intro Q q _ hqQ U u₁ u₂ hQ a b ha hb
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue _ ((res _ (tw q 1)).X 0) U).1 _ _ ?_
  have h1 := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u₁
  have h2 := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u₂
  refine GlobalTheory.EtC.RedChern.loc_mono (GlobalTheory.EtC.RedChern.loc_and h1 h2) ?_
  rintro V g ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
  have hvq : (v ^ (Q / q)) ^ q = Units.map g.appTop.hom.toMonoidHom u₁ := by
    rw [← pow_mul, Nat.div_mul_cancel hqQ, hv]
  have hwq : (w ^ (Q / q)) ^ q = Units.map g.appTop.hom.toMonoidHom u₂ := by
    rw [← pow_mul, Nat.div_mul_cancel hqQ, hw]
  have hvw : (v * w) ^ Q = Units.map g.appTop.hom.toMonoidHom (u₁ * u₂) := by
    rw [mul_pow, hv, hw, map_mul]
  have ea := ha V g v w hv hw
  have eb := hb V g _ _ hvq hwq
  have d1 := GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u₁ hQ V g v hv
  have d2 := GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u₂ hQ V g w hw
  have d3 := GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U (u₁ * u₂) hQ V g (v * w) hvw
  have en := (redMap Q q 1).nat g 0 a
  have hsub : ∀ x y : Sec ((res _ (tw q 1)).X 0) U, Sec.res g (x - y) = Sec.res g x - Sec.res g y := fun x y => map_sub _ x y
  have hadd : ∀ x y : Sec ((res _ (tw q 1)).X 0) U, Sec.res g (x + y) = Sec.res g x + Sec.res g y := fun x y => map_add _ x y
  rw [hsub, hadd, hsub, en, ea, eb, d1, d2, d3]
  simp only [GlobalTheory.EtC.RedChern.defect, map_sub, map_add, mul_pow]
  abel
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedChernCocycle_deg_two_sub_eq_defects : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u₁ u₂ : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 0) U) (b : Sec ((res _ (tw q 1)).X 0) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ Q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g a = kumT Q V v + kumT Q V w - kumT Q V (v * w)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g b = kumT q V v + kumT q V w - kumT q V (v * w)) → (redMap Q q 1).app U 0 a - b = GlobalTheory.EtC.RedChern.defectSec Q q U u₂ - GlobalTheory.EtC.RedChern.defectSec Q q U (u₁ * u₂) + GlobalTheory.EtC.RedChern.defectSec Q q U u₁ := by
  atlas_forward_decl GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects
end

section
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RedChern

set_option backward.isDefEq.respectTransparency false

theorem delta_two_eq : (SimplexCategory.δ (2 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 0 1 (by omega) := by
  ext i; fin_cases i <;> rfl

theorem delta_zero_eq : (SimplexCategory.δ (0 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 1 1 (by omega) := by
  ext i; fin_cases i <;> rfl

theorem face_two {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 2 = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [delta_two_eq]

theorem face_zero {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 0 = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [delta_zero_eq]

theorem sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  exact NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x

open GlobalTheory.EtC.PicSpec

theorem corrFam_nat (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) {E : Spc} (hE : Inv Q E) (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (corrFam Q q L p s h U x) = corrFam Q q L p s h V (x.res g) := by
  match p with
  | 0 => simp [corrFam_zero]
  | 1 =>
    obtain rfl : s = 0 := by omega
    rw [corrFam_one, corrFam_one, lineUnit_res,
      GlobalTheory.T.kummerReductionChernDefectSection_res Q q hqQ U _ (hE U ⟨x.face 0⟩) V g]
  | p + 2 => simp [corrFam_add_two]

theorem coefficientReduction_firstChernClass_tateTwist : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → ∀ L : E ⟶ ofCat (glCat 1),
    red Q q E 2 1 (c1 Q L) = c1 q L := by
  intro Q q _ hqQ E hE L
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact NeZero.ne Q (Nat.eq_zero_of_zero_dvd hqQ)
  haveI : NeZero q := ⟨hq0⟩
  have hUnit : Inv q E := fun U hU => by
    obtain ⟨k, hk⟩ := hqQ
    have := hE U hU
    rw [hk, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨γ, hγ, hγ0, hγ1, hγ2⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive Q).1 L hE
  obtain ⟨γ', hγ', hγ0', hγ1', hγ2'⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).1 L hUnit
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 1)).1 E 2 γ
  have hred : red Q q E 2 1 (c1 Q L) = CohomologyClass.mk β := by
    rw [← hγ]
    exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 1)).2 E 2 γ β hβ
  rw [hred, ← hγ']
  obtain ⟨α, hα⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' (ZMod q) (corrFam Q q L) (corrFam_nat Q q hqQ hE L)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)]
  refine ⟨α, ?_⟩
  apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1
  intro p t ht U x
  rw [Cocycle.coe_sub, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 _ _ p t ht U x).2.1, hβ]
  match p with
  | 0 =>
    obtain rfl : t = 2 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).1 x, hα, corrFam_zero, sec_map_zero, hγ0, hγ0', map_zero, sub_zero]
  | 1 =>
    obtain rfl : t = 1 := by omega
    have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).2 0 0 1 (by simp) ht x
    rw [key]
    simp only [hα, corrFam_zero, smul_zero, Finset.sum_const_zero, add_zero, corrFam_one]
    refine (GlobalTheory.T.reducedChernCocycle_deg_one_sub_eq_differential Q q hqQ U (lineUnit L x) (hE U ⟨x.face 0⟩) _ _ (fun V g v hv => ?_) (fun V g w hw => ?_)).symm
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod Q)).2.1 γ.1 1 1 _ V U g x]
      exact hγ1 V (x.res g) v (by rw [lineUnit_res]; exact hv)
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ'.1 1 1 _ V U g x]
      exact hγ1' V (x.res g) w (by rw [lineUnit_res]; exact hw)
  | 2 =>
    obtain rfl : t = 0 := by omega
    have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).2 1 (-1) 0 (by simp) ht x
    rw [key]
    simp only [hα, corrFam_one]
    rw [show corrFam Q q L (1 + 1) (-1) (by simp) U x = 0 from rfl, sec_map_zero, zero_add, Fin.sum_univ_three,
      lineUnit_face, face_zero, face_two]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, Int.reduceNeg]
    rw [Int.negOnePow_even 2 (by decide), one_smul, mul_comm (lineUnit L _) (lineUnit L _), ← sub_eq_add_neg]
    norm_num
    refine (GlobalTheory.T.reducedChernCocycle_deg_two_sub_eq_defects Q q hqQ U _ _ (hE U ⟨(x.face 0).face 0⟩) _ _ (fun V g v w hv hw => ?_) (fun V g v w hv hw => ?_)).symm
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod Q)).2.1 γ.1 2 0 _ V U g x]
      exact hγ2 V (x.res g) v w (by rw [sub_res, lineUnit_res]; exact hv) (by rw [sub_res, lineUnit_res]; exact hw)
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ'.1 2 0 _ V U g x]
      exact hγ2' V (x.res g) v w (by rw [sub_res, lineUnit_res]; exact hv) (by rw [sub_res, lineUnit_res]; exact hw)
  | p + 3 =>
    have hZ := res_isZero (tw q 1) t (by omega)
    exact (sec_eq_zero hZ _).trans (sec_eq_zero hZ _).symm

end GlobalTheory.EtC.RedChern
end
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.red_c1_eq_c1_of_dvd : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → ∀ L : E ⟶ ofCat (glCat 1), red Q q E 2 1 (c1 Q L) = c1 q L := by
  atlas_forward_decl GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.RedCoef

variable {S R T : Type} [CommRing S] [CommRing R] [CommRing T]

def semiId (I : Cx S) : SemiMap I I where
  app _ _ := AddMonoidHom.id _
  nat _ _ _ := rfl
  comm _ _ _ _ := rfl

def semiComp {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J) (σ : SemiMap J K) : SemiMap I K where
  app U s := (σ.app U s).comp (ρ.app U s)
  nat g s a := by
    change Sec.res g (σ.app _ s (ρ.app _ s a)) = σ.app _ s (ρ.app _ s (Sec.res g a))
    rw [σ.nat, ρ.nat]
  comm U s t a := by
    change Sec.map (K.d s t) (σ.app U s (ρ.app U s a)) = σ.app U t (ρ.app U t (Sec.map (I.d s t) a))
    rw [σ.comm, ρ.comm]

theorem semiId_op (I : Cx S) (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) I n) :
    (semiId I).op.app E n x = x := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S S (semiId I)).2 E n α α (fun _ _ _ _ _ => rfl)

theorem semiComp_op {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J) (σ : SemiMap J K) (E : Spc) (n : ℤ)
    (x : CohomologyClass ((chains S).obj E) I n) : (semiComp ρ σ).op.app E n x = σ.op.app E n (ρ.op.app E n x) := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).1 E n α
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R T σ).1 E n β
  rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).2 E n α β hβ, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R T σ).2 E n β γ hγ]
  exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S T (semiComp ρ σ)).2 E n α γ (fun p s h U y => by
    rw [hγ p s h U y, hβ p s h U y]; rfl)

theorem neZero_of_dvd {q Q : ℕ} [NeZero Q] (h : q ∣ Q) : NeZero q :=
  ⟨by rintro rfl; exact NeZero.ne Q (zero_dvd_iff.mp h)⟩

theorem div_mul_div {Q q r : ℕ} [NeZero Q] (hq : q ∣ Q) (hr : r ∣ q) : Q / q * (q / r) = Q / r := by
  obtain ⟨k, rfl⟩ := hq
  obtain ⟨l, rfl⟩ := hr
  have hQ := NeZero.ne (r * l * k)
  have hr0 : r ≠ 0 := by rintro rfl; simp at hQ
  have hl0 : l ≠ 0 := by rintro rfl; simp at hQ
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (Nat.mul_ne_zero hr0 hl0)),
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr0), mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr0),
    mul_comm]

end GlobalTheory.EtC.RedCoef

namespace GlobalTheory.EtC.RedCoef

theorem a11 : GlobalTheory.EtC.A11 := by
  intro Q q _ hqQ E
  haveI : NeZero q := neZero_of_dvd hqQ
  refine ⟨fun a b => GlobalTheory.T.tateTwistCoefficientReduction_cup Q q hqQ E a b, fun hE => ⟨GlobalTheory.T.tateTwistCoefficientReduction_unitClass Q q hqQ E hE, fun L => GlobalTheory.T.red_c1_eq_c1_of_dvd Q q hqQ E hE L⟩,
    fun n i a => ?_, fun r hr n i a => ?_⟩
  · have hgen : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)),
        (redMap Q Q i).app U 0 (resGen i ζ) = (semiId (res _ (tw Q i))).app U 0 (resGen i ζ) := by
      intro U ζ
      refine GlobalTheory.T.tateTwistReductionResolutionMap_generator Q Q dvd_rfl i U ζ ζ ?_
      rw [Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne Q)), pow_one]
    exact (GlobalTheory.T.tateTwistReduction_cohomology_map_unique Q Q dvd_rfl i _ _ hgen E n a).trans (semiId_op _ E n a)
  · haveI : NeZero r := neZero_of_dvd hr
    have hrQ : r ∣ Q := hr.trans hqQ
    have hgen : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)),
        (semiComp (redMap Q q i) (redMap q r i)).app U 0 (resGen i ζ) = (redMap Q r i).app U 0 (resGen i ζ) := by
      intro U ζ
      obtain ⟨η, hη⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).2.2.2.2.2 q hqQ ζ
      obtain ⟨ξ, hξ⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q Γ(U, ⊤)).2.2.2.2.2 r hr η
      change (redMap q r i).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) = _
      rw [GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ i U ζ η hη, GlobalTheory.T.tateTwistReductionResolutionMap_generator q r hr i U η ξ hξ,
        GlobalTheory.T.tateTwistReductionResolutionMap_generator Q r hrQ i U ζ ξ (by rw [hξ, hη, ← pow_mul, div_mul_div hqQ hr])]
    exact (semiComp_op _ _ E n a).symm.trans (GlobalTheory.T.tateTwistReduction_cohomology_map_unique Q r hrQ i _ _ hgen E n a)

end GlobalTheory.EtC.RedCoef
end
end
