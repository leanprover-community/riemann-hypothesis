import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheafStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHypercohomologyIsoOfInjectiveResolution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSheafHomLinearMapsSheafCurryEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocallyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSectionsStatement

section
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RetractAcyc

def resMapRetractHomotopy (R : Type) [CommRing R] {M M' : Shv R} (i : M ⟶ M') (r : M' ⟶ M) (h : i ≫ r = 𝟙 M) :
    Homotopy (resMap R i ≫ resMap R r) (𝟙 (res R M)) := by
  have H : Homotopy (InjectiveResolution.desc i (injectiveResolution M') (injectiveResolution M) ≫
      InjectiveResolution.desc r (injectiveResolution M) (injectiveResolution M'))
      (𝟙 (injectiveResolution M).cocomplex) :=
    (InjectiveResolution.descCompHomotopy i r _ _ _).symm.trans
      (by rw [h]; exact InjectiveResolution.descIdHomotopy _ _)
  have H2 := H.extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_comp, HomologicalComplex.extendMap_id] at H2
  exact H2

theorem post_post_of_retract (R : Type) [CommRing R] {M M' : Shv R} (i : M ⟶ M') (r : M' ⟶ M) (h : i ≫ r = 𝟙 M)
    (K : Cx R) (n : ℤ) (x : HK R K M n) : HK.post R K r n (HK.post R K i n x) = x := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have Hh := resMapRetractHomotopy R i r h
  change CohomologyClass.mk (zcomp (zcomp α (Cocycle.ofHom (resMap R i)) (add_zero n))
    (Cocycle.ofHom (resMap R r)) (add_zero n)) = CohomologyClass.mk α
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨α.1.comp (Cochain.ofHomotopy Hh) (by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega), Cocycle.δ_eq_zero, δ_ofHomotopy]
  ext p q hpq
  simp [zcomp, Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q)]

theorem subsingleton_of_retract : ∀ (R : Type) [CommRing R] (M M' : Shv R) (i : M ⟶ M') (r : M' ⟶ M), i ≫ r = 𝟙 M →
    ∀ (K : Cx R) (n : ℤ), Subsingleton (HK R K M' n) → Subsingleton (HK R K M n) := by
  intro R _ M M' i r h K n hs
  exact (Function.LeftInverse.injective (g := HK.post R K r n) (f := HK.post R K i n)
    (post_post_of_retract R i r h K n)).subsingleton

end GlobalTheory.EtC.RetractAcyc
end
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_etaleHypercohomology_of_retract : ∀ (R : Type) [CommRing R] (M M' : Shv R) (i : M ⟶ M') (r : M' ⟶ M), i ≫ r = 𝟙 M → ∀ (K : Cx R) (n : ℤ), Subsingleton (HK R K M' n) → Subsingleton (HK R K M n) := by
  atlas_forward_decl GlobalTheory.EtC.RetractAcyc.subsingleton_of_retract
end

section
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.CoindRetract

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

def adj : restr φ ⊣ coind φ :=
  Adjunction.restrictFullyFaithful
    ((ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} (liftHom φ)).whiskerRight (Scheme.{0}ᵒᵖ))
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _) (Iso.refl _) (Iso.refl _)

instance restr_faithful : (restr φ).Faithful :=
  show (sheafCompose (Scheme.etaleTopology.{0}) (ModuleCat.restrictScalars.{1} (liftHom φ))).Faithful from inferInstance

instance restr_preservesMono : (restr φ).PreservesMonomorphisms where
  preserves {X Y} f hf := by
    haveI : Mono ((restr φ).map f).hom := by
      rw [NatTrans.mono_iff_mono_app]
      intro U
      exact (ModuleCat.restrictScalars.{1} (liftHom φ)).map_mono (f.hom.app U)
    exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

instance coind_preservesMono : (coind φ).PreservesMonomorphisms := by
  haveI : (coind φ).IsRightAdjoint := (adj φ).isRightAdjoint
  infer_instance

theorem coind_retract (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Shv S) [Injective I] :
    ∃ (J : Shv R) (_ : Injective J) (i : I ⟶ (coind φ).obj J) (r : (coind φ).obj J ⟶ I), i ≫ r = 𝟙 I := by
  let J := Injective.under ((restr φ).obj I)
  let i : I ⟶ (coind φ).obj J := (adj φ).unit.app I ≫ (coind φ).map (Injective.ι ((restr φ).obj I))
  haveI : Mono i := mono_comp _ _
  exact ⟨J, inferInstance, i, Injective.factorThru (𝟙 I) i, Injective.comp_factorThru _ _⟩

end GlobalTheory.EtC.CoindRetract
end
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_etaleSheaf_retract_of_coinduced : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Shv S) [Injective I], ∃ (J : Shv R) (_ : Injective J) (i : I ⟶ (coind φ).obj J) (r : (coind φ).obj J ⟶ I), i ≫ r = 𝟙 I := by
  atlas_forward_decl GlobalTheory.EtC.CoindRetract.coind_retract
end

section
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.HomInj

variable (R : Type) [CommRing R] (P : PSh) (I : Ideal (ULift.{1} R))

def idealFree : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of (ULift.{1} R) (ULift.{1} (P.obj U) →₀ I)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain I (ULift.{1} R) (fun x => ULift.up (P.map f x.down)))
  map_id U := by
    ext1; apply Finsupp.lhom_ext; intro x a
    simp
  map_comp f g := by
    ext1; apply Finsupp.lhom_ext; intro x a
    simp

def idealIncl : idealFree R P I ⟶ (freeP R).obj P where
  app U := ModuleCat.ofHom (Finsupp.mapRange.linearMap I.subtype)
  naturality U V f := by
    ext1; apply Finsupp.lhom_ext; intro x a
    change Finsupp.mapRange (I.subtype) (map_zero _) (Finsupp.mapDomain _ (Finsupp.single x a)) =
      Finsupp.mapDomain _ (Finsupp.mapRange (I.subtype) (map_zero _) (Finsupp.single x a))
    simp only [Finsupp.mapDomain_single, Finsupp.mapRange_single]
    erw [Finsupp.mapDomain_single]
    rfl

instance : Mono (idealIncl R P I) := by
  have : ∀ U, Mono ((idealIncl R P I).app U) := fun U => by
    rw [ModuleCat.mono_iff_injective]
    exact Finsupp.mapRange_injective _ (map_zero _) Subtype.val_injective
  exact NatTrans.mono_of_mono_app _

end GlobalTheory.EtC.HomInj

namespace GlobalTheory.EtC.HomInj
variable (R : Type) [CommRing R] (P : PSh) (I : Ideal (ULift.{1} R)) (J : Shv R)
  (g : I →ₗ[ULift.{1} R] ((free R).obj P ⟶ J))

def evalAt (U : Scheme.{0}ᵒᵖ) (x : ULift.{1} (P.obj U)) : I →ₗ[ULift.{1} R] J.obj.obj U where
  toFun a := ((g a).hom.app U).hom (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app U).hom (ModuleCat.freeMk x))
  map_add' a b := by rw [map_add]; rfl
  map_smul' r a := by rw [map_smul]; rfl

def famHom : idealFree R P I ⟶ J.obj where
  app U := ModuleCat.ofHom (Finsupp.lsum ℕ (evalAt R P I J g U))
  naturality U V f := by
    ext1; apply Finsupp.lhom_ext; intro x a
    change Finsupp.lsum ℕ (evalAt R P I J g V) (Finsupp.mapDomain _ (Finsupp.single x a)) =
      (J.obj.map f).hom (Finsupp.lsum ℕ (evalAt R P I J g U) (Finsupp.single x a))
    rw [Finsupp.mapDomain_single]
    simp only [Finsupp.lsum_single]
    change ((g a).hom.app V).hom _ = (J.obj.map f).hom (((g a).hom.app U).hom _)
    have h1 := congrArg (fun φ => φ.hom (ModuleCat.freeMk x))
      (((toSheafify Scheme.etaleTopology ((freeP R).obj P) : (freeP R).obj P ⟶ ((free R).obj P).obj) ≫ (g a).hom).naturality f)
    change ((g a).hom.app V).hom (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app V).hom
        ((((freeP R).obj P).map f).hom (ModuleCat.freeMk x))) = (J.obj.map f).hom (((g a).hom.app U).hom
        (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app U).hom (ModuleCat.freeMk x))) at h1
    rw [← h1]
    congr 2
    change _ = Finsupp.mapDomain _ (Finsupp.single x (1 : ULift.{1} R))
    erw [Finsupp.mapDomain_single]
    rfl
end GlobalTheory.EtC.HomInj

namespace GlobalTheory.EtC.HomInj

theorem hom_free_injective (R : Type) [CommRing R] (J : Shv R) [Injective J] (P : PSh) :
    Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J) := by
  apply Module.Baer.injective
  intro I g
  let m : (presheafToSheaf Scheme.etaleTopology _).obj (idealFree R P I) ⟶ (free R).obj P :=
    (presheafToSheaf Scheme.etaleTopology _).map (idealIncl R P I)
  let ψ' : (presheafToSheaf Scheme.etaleTopology _).obj (idealFree R P I) ⟶ J :=
    ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).symm (famHom R P I J g)
  haveI : Mono m := inferInstanceAs (Mono ((presheafToSheaf Scheme.etaleTopology _).map (idealIncl R P I)))
  let f := Injective.factorThru ψ' m
  refine ⟨LinearMap.toSpanSingleton _ _ f, fun a ha => ?_⟩
  rw [LinearMap.toSpanSingleton_apply]
  have hm : m ≫ f = ψ' := Injective.comp_factorThru ψ' m
  have hψ : toSheafify Scheme.etaleTopology (idealFree R P I) ≫ ψ'.hom = famHom R P I J g := by
    have := ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).apply_symm_apply (famHom R P I J g)
    rw [Adjunction.homEquiv_unit] at this
    simpa using this
  have h3 : idealIncl R P I ≫ toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ f.hom = famHom R P I J g := by
    have e := toSheafify_naturality Scheme.etaleTopology (idealIncl R P I)
    calc idealIncl R P I ≫ toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ f.hom
        = (idealIncl R P I ≫ toSheafify Scheme.etaleTopology ((freeP R).obj P)) ≫ f.hom := (Category.assoc _ _ _).symm
      _ = (toSheafify Scheme.etaleTopology (idealFree R P I) ≫ sheafifyMap Scheme.etaleTopology (idealIncl R P I)) ≫ f.hom := by
          rw [e]
      _ = toSheafify Scheme.etaleTopology (idealFree R P I) ≫ (m ≫ f).hom :=
          Category.assoc (toSheafify Scheme.etaleTopology (idealFree R P I)) (sheafifyMap Scheme.etaleTopology (idealIncl R P I)) f.hom
      _ = famHom R P I J g := by rw [hm, hψ]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ J.cond
  ext U : 2
  apply ModuleCat.free_hom_ext
  intro x
  have h4 := congrArg (fun φ => (φ.app U).hom (Finsupp.single x ⟨a, ha⟩)) h3
  have e1 : ((idealIncl R P I).app U).hom (Finsupp.single x (⟨a, ha⟩ : I)) = a • ModuleCat.freeMk (R := ULift.{1} R) x := by
    change Finsupp.mapRange I.subtype (map_zero _) (Finsupp.single x (⟨a, ha⟩ : I)) = _
    rw [Finsupp.mapRange_single]
    change _ = a • Finsupp.single x (1 : ULift.{1} R)
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ f.hom).app U).hom
      (((idealIncl R P I).app U).hom (Finsupp.single x ⟨a, ha⟩)) =
    Finsupp.lsum ℕ (evalAt R P I J g U) (Finsupp.single x ⟨a, ha⟩) at h4
  rw [e1] at h4
  erw [LinearMap.map_smul, Finsupp.lsum_single] at h4
  exact h4

end GlobalTheory.EtC.HomInj
end
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduleInjective_hom_free_etaleSheaf_injective : ∀ (R : Type) [CommRing R] (J : Shv R) [Injective J] (P : PSh), Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J) := by
  atlas_forward_decl GlobalTheory.EtC.HomInj.hom_free_injective
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHypercohomology_iso_of_injective_resolution : ∀ (R : Type) [CommRing R] (M : Shv R) (C : Cx R) (ε : sgl M ⟶ C), C.IsStrictlyGE 0 → (∀ t, Injective (C.X t)) → QuasiIso ε → ∀ (K : Cx R) (n : ℤ), Nonempty (HK R K M n ≃+ CohomologyClass K C n) := by
  first | exact @GlobalTheory.EtC.InjResCmp.hyper_iso_of_injective_resolution | exact GlobalTheory.EtC.InjResCmp.hyper_iso_of_injective_resolution | (intros; apply GlobalTheory.EtC.InjResCmp.hyper_iso_of_injective_resolution <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem homSh_injective (R : Type) [CommRing R] (J : Shv R) [Injective J] (M : ModuleCat.{1} (ULift.{1} R)) [Projective M] :
    Injective ((homSh J).obj (op M)) := by
  obtain ⟨e, -, hX⟩ := GlobalTheory.T.exists_sheafHom_linearMapsSheaf_curry_equiv R J
  haveI : Module.Projective (ULift.{1} R) M := (IsProjective.iff_projective (P := M)).2 ‹_›
  constructor
  intro X Y g i _
  have surj : Function.Surjective (Linear.leftComp (ULift.{1} R) J i) :=
    fun k => ⟨Injective.factorThru k i, Injective.comp_factorThru k i⟩
  obtain ⟨h', hh'⟩ := Module.projective_lifting_property _ (e X M g) surj
  refine ⟨(e Y M).symm h', ?_⟩
  apply (e X M).injective
  rw [hX, Equiv.apply_symm_apply, hh']

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_etaleSheafOfLinearMapsFromModule : ∀ (R : Type) [CommRing R] (J : Shv R) [Injective J] (M : ModuleCat.{1} (ULift.{1} R)) [Projective M], Injective ((homSh J).obj (op M)) := by
  first | (exact @GlobalTheory.EtC.homSh_injective) | (exact GlobalTheory.EtC.homSh_injective) | (intros; apply GlobalTheory.EtC.homSh_injective  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem lift_linear_of_injective {S : Type*} [Ring S] {N A B C : Type*} [AddCommGroup N] [Module S N]
    [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B] [AddCommGroup C] [Module S C]
    (hN : Module.Baer S N)
    (u : A →ₗ[S] B) (v : B →ₗ[S] C) (hex : ∀ b, v b = 0 → ∃ a, u a = b)
    (f : B →ₗ[S] N) (hf : f ∘ₗ u = 0) : ∃ g : C →ₗ[S] N, g ∘ₗ v = f := by
  have hle : LinearMap.ker v ≤ LinearMap.ker f := by
    intro b hb
    obtain ⟨a, rfl⟩ := hex b hb
    simpa using LinearMap.congr_fun hf a
  let f₁ : (B ⧸ LinearMap.ker v) →ₗ[S] N := (LinearMap.ker v).liftQ f hle
  let f₂ : LinearMap.range v →ₗ[S] N := f₁ ∘ₗ (v.quotKerEquivRange).symm.toLinearMap
  obtain ⟨g, hg⟩ := hN.extension_property (LinearMap.range v).subtype (LinearMap.range v).injective_subtype f₂
  refine ⟨g, LinearMap.ext fun b => ?_⟩
  have h1 := LinearMap.congr_fun hg ⟨v b, b, rfl⟩
  have h2 : (v.quotKerEquivRange).symm ⟨v b, b, rfl⟩ = Submodule.Quotient.mk b := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.comp_apply, Submodule.coe_subtype] at h1
  rw [LinearMap.comp_apply, h1]
  simp only [f₂, f₁, LinearMap.comp_apply, LinearEquiv.coe_coe, h2, Submodule.liftQ_apply]

theorem lift_homSh : ∀ (R : Type) [CommRing R] (J X : Shv R), Module.Injective (ULift.{1} R) (X ⟶ J) → ∀ (A B C : ModuleCat.{1} (ULift.{1} R)) (u : A ⟶ B) (v : B ⟶ C), (∀ b, v.hom b = 0 → ∃ a, u.hom a = b) → ∀ f : X ⟶ (homSh J).obj (op B), f ≫ (homSh J).map u.op = 0 → ∃ g : X ⟶ (homSh J).obj (op C), g ≫ (homSh J).map v.op = f := by
  intro R _ J X hinj A B C u v hex f hf
  obtain ⟨e, hnat, -⟩ := GlobalTheory.T.exists_sheafHom_linearMapsSheaf_curry_equiv R J
  have he0 : ∀ M : ModuleCat.{1} (ULift.{1} R), e X M 0 = 0 := by
    intro M
    have := hnat X M M 0 0
    rw [zero_comp, ModuleCat.hom_zero, LinearMap.comp_zero] at this
    exact this
  have hf' : e X B f ∘ₗ u.hom = 0 := by rw [← hnat, hf, he0]
  obtain ⟨g', hg'⟩ := lift_linear_of_injective (Module.Baer.of_injective hinj) u.hom v.hom hex (e X B f) hf'
  refine ⟨(e X C).symm g', (e X B).injective ?_⟩
  rw [hnat, Equiv.apply_symm_apply, hg']
end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_etaleSheafOfLinearMaps_exact : ∀ (R : Type) [CommRing R] (J X : Shv R), Module.Injective (ULift.{1} R) (X ⟶ J) → ∀ (A B C : ModuleCat.{1} (ULift.{1} R)) (u : A ⟶ B) (v : B ⟶ C), (∀ b, v.hom b = 0 → ∃ a, u.hom a = b) → ∀ f : X ⟶ (homSh J).obj (op B), f ≫ (homSh J).map u.op = 0 → ∃ g : X ⟶ (homSh J).obj (op C), g ≫ (homSh J).map v.op = f := by
  first | (exact @GlobalTheory.EtC.lift_homSh) | (exact GlobalTheory.EtC.lift_homSh) | (intros; apply GlobalTheory.EtC.lift_homSh  <;> assumption)
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

variable {R : Type} [CommRing R]

theorem coindQ_map_res {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map f (Sec.res g x) = Sec.res g (Sec.map f x) := by
  have := congrArg (fun h => h.hom x) (f.hom.naturality g.op)
  simpa using this

theorem coindQ_res_res (F : Shv R) {W V U : Scheme.{0}} (g : W ⟶ V) (x : V ⟶ U) (s : Sec F U) :
    Sec.res g (Sec.res x s) = Sec.res (g ≫ x) s := by
  simp [Sec.res]

def coindQ_gen (J : Shv R) (U : Scheme.{0}) : ((free R).obj (yoneda.obj U) ⟶ J) →ₗ[ULift.{1} R] Sec J U where
  toFun ψ := Sec.map ψ (freeGen R (yoneda.obj U) U (𝟙 U))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]

theorem coindQ_gen_bijective (J : Shv R) (U : Scheme.{0}) : Function.Bijective (coindQ_gen J U) := by
  obtain ⟨hex, huniq, hres, -⟩ := GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj U) J
  have key : ∀ (V : Scheme.{0}) (x : V ⟶ U),
      freeGen R (yoneda.obj U) V x = Sec.res x (freeGen R (yoneda.obj U) U (𝟙 U)) := by
    intro V x
    rw [hres V U x (𝟙 U)]
    simp
  constructor
  · intro ψ ψ' h
    apply huniq
    intro V x
    rw [key V x, coindQ_map_res, coindQ_map_res]
    exact congrArg (Sec.res x) h
  · intro s
    obtain ⟨ψ, hψ⟩ := hex (fun V x => Sec.res x s) (fun W V g x => by
      rw [coindQ_res_res]; rfl)
    refine ⟨ψ, ?_⟩
    show Sec.map ψ (freeGen R (yoneda.obj U) U (𝟙 U)) = s
    rw [hψ U (𝟙 U)]
    simp [Sec.res]

theorem coindQ_injSec (J : Shv R) (hJ : ∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J))
    (U : Scheme.{0}) : Injective (J.obj.obj (op U)) := by
  have := hJ (yoneda.obj U)
  have hI : Injective (ModuleCat.of (ULift.{1} R) ((free R).obj (yoneda.obj U) ⟶ J)) :=
    Module.injective_object_of_injective_module _ _
  exact Injective.of_iso (LinearEquiv.ofBijective (coindQ_gen J U) (coindQ_gen_bijective J U)).toModuleIso hI

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]

theorem coindQ_exactAt_succ {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R)
    (hJ : ∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) (n : ℕ) :
    (coindCx φ J).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  rw [GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
  intro U b hb
  have := coindQ_injSec J hJ U
  let b' : (scalarsRes φ).complex.X (n + 1) ⟶ J.obj.obj (op U) := b
  have hb' : (scalarsRes φ).complex.d (n + 2) (n + 1) ≫ b' = 0 := by
    have h2 : (coindCx φ J).d (n + 1) (n + 2) = (homSh J).map ((scalarsRes φ).complex.d (n + 2) (n + 1)).op :=
      coindCx_d φ J (n + 1)
    have hb2 : Sec.map ((coindCx φ J).d (n + 1) (n + 2)) b = 0 := hb
    rw [h2] at hb2
    exact hb2
  let a' := ((scalarsRes φ).exact_succ n).descToInjective b' hb'
  have ha' : (scalarsRes φ).complex.d (n + 1) n ≫ a' = b' :=
    ((scalarsRes φ).exact_succ n).comp_descToInjective b' hb'
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ?_⟩
  have h1 : (coindCx φ J).d n (n + 1) = (homSh J).map ((scalarsRes φ).complex.d (n + 1) n).op :=
    coindCx_d φ J n
  have key : Sec.map ((coindCx φ J).d n (n + 1)) (a' : Sec ((coindCx φ J).X n) U) = b := by
    rw [h1]; exact ha'
  exact ⟨Sec.res g (a' : Sec ((coindCx φ J).X n) U),
    (coindQ_map_res ((coindCx φ J).d n (n + 1)) g _).trans (congrArg (Sec.res g) key)⟩

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]

abbrev coindQ_p {S : Type} [CommRing S] (φ : R →+* S) :
    (scalarsRes φ).complex.X 0 ⟶ scalarsMod φ :=
  (scalarsRes φ).π.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (scalarsMod φ)).hom

instance {S : Type} [CommRing S] (φ : R →+* S) : Epi (coindQ_p φ) := by
  exact epi_comp _ _

theorem coindQ_d_p {S : Type} [CommRing S] (φ : R →+* S) :
    (scalarsRes φ).complex.d 1 0 ≫ coindQ_p φ = 0 := by
  show _ ≫ (_ ≫ _) = 0
  rw [ProjectiveResolution.complex_d_comp_π_f_zero_assoc, zero_comp]

def coindQ_sc {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R) : ShortComplex (Shv R) :=
  ShortComplex.mk (coindToHom φ J ≫ (homSh J).map (coindQ_p φ).op)
    ((homSh J).map ((scalarsRes φ).complex.d 1 0).op) (by
      rw [Category.assoc, ← Functor.map_comp, ← op_comp, coindQ_d_p, op_zero, Functor.map_zero, comp_zero])

theorem coindQ_sc_f_sec {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R) (U : Scheme.{0})
    (a : Sec ((restr φ).obj ((coind φ).obj J)) U) :
    Sec.map (coindQ_sc φ J).f a =
      (coindQ_p φ ≫ homOfLin (ModuleCat.CoextendScalars.equiv (liftHom φ) _ a) : _ ⟶ J.obj.obj (op U)) := rfl

theorem coindQ_sc_inj {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R) (U : Scheme.{0}) :
    Function.Injective (Sec.map (coindQ_sc φ J).f (U := U)) := by
  intro a a' h
  have h' := (coindQ_sc_f_sec φ J U a).symm.trans (h.trans (coindQ_sc_f_sec φ J U a'))
  have h3 := (cancel_epi (coindQ_p φ)).1 h'
  apply ModuleCat.CoextendScalars.ext
  exact congrArg ModuleCat.Hom.hom h3

theorem coindQ_sc_mono {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R) : Mono (coindQ_sc φ J).f := by
  suffices h : Mono (coindQ_sc φ J).f.hom from Sheaf.Hom.mono_of_presheaf_mono _ _ _
  have hU : ∀ U, Mono ((coindQ_sc φ J).f.hom.app U) := by
    intro U
    rw [ModuleCat.mono_iff_injective]
    exact coindQ_sc_inj φ J U.unop
  exact NatTrans.mono_of_mono_app _

theorem coindQ_sc_exact {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R) : (coindQ_sc φ J).Exact := by
  rw [GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
  intro U b hb
  let b' : (scalarsRes φ).complex.X 0 ⟶ J.obj.obj (op U) := b
  have hb' : (scalarsRes φ).complex.d 1 0 ≫ b' = 0 := hb
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' (scalarsRes φ).isColimitCokernelCofork b' hb'
  let c : scalarsMod φ ⟶ J.obj.obj (op U) :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (scalarsMod φ)).inv ≫ l
  have hc : coindQ_p φ ≫ c = b' := by
    simp only [c, coindQ_p, Category.assoc, Iso.hom_inv_id_assoc]
    exact hl
  let a : Sec ((restr φ).obj ((coind φ).obj J)) U := (ModuleCat.CoextendScalars.equiv (liftHom φ) _).symm c.hom
  have key : Sec.map (coindQ_sc φ J).f a = b := by
    rw [coindQ_sc_f_sec]
    exact hc
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨Sec.res g a, ?_⟩⟩
  exact (coindQ_map_res _ g _).trans (congrArg (Sec.res g) key)

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]

theorem coindAug_quasiIso : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (J : Shv R),
    (∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) → QuasiIso (coindAug φ J) := by
  intro R S _ _ φ J hJ
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨coindQ_sc_exact φ J, coindQ_sc_mono φ J⟩
      refine ShortComplex.isoMk (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 _) (Iso.refl _) (Iso.refl _) ?_ ?_
      · simp only [Iso.refl_hom, Category.comp_id]
        exact (coindAug_f_zero φ J).symm
      · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        exact (coindCx_d φ J 0).symm
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)]
    exact coindQ_exactAt_succ φ J hJ n

end GlobalTheory.EtC
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCoinductionComplexAugmentation_quasiIso : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (J : Shv R), (∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) → QuasiIso (coindAug φ J) := by
  first | (exact @GlobalTheory.EtC.coindAug_quasiIso) | (exact GlobalTheory.EtC.coindAug_quasiIso) | (intros; apply GlobalTheory.EtC.coindAug_quasiIso  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.EtC.coindRes_exists : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (J : Shv R) [Injective J], (∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) → ∃ (C : Cx R) (ε : sgl ((restr φ).obj ((coind φ).obj J)) ⟶ C), C.IsStrictlyGE 0 ∧ (∀ t, Injective (C.X t)) ∧ QuasiIso ε ∧ ∀ (P : PSh) (n : ℤ), 0 < n → Subsingleton (CohomologyClass (sgl ((free R).obj P)) C n) := by
  intro R S _ _ φ J _ hJ
  haveI := GlobalTheory.T.etaleCoinductionComplexAugmentation_quasiIso R S φ J hJ
  let I : InjectiveResolution ((restr φ).obj ((coind φ).obj J)) :=
    { cocomplex := coindCx φ J
      injective := fun n => GlobalTheory.T.injective_etaleSheafOfLinearMapsFromModule R J ((scalarsRes φ).complex.X n)
      ι := coindAug φ J }
  refine ⟨I.cochainComplex, I.ι', inferInstance, inferInstance, inferInstance, ?_⟩
  intro P n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ x : CohomologyClass (sgl ((free R).obj P)) I.cochainComplex ((k : ℤ) + 1), x = 0 by
    rw [h x, h y]
  intro x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective α ((k : ℤ) + 1) (zero_add _) ((k : ℤ) + 1 + 1) rfl
  rw [CohomologyClass.mk_eq_zero_iff, Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (k : ℤ) rfl]
  have hex : ∀ b, ((scalarsRes φ).complex.d (k + 1) k).hom b = 0 → ∃ a, ((scalarsRes φ).complex.d (k + 2) (k + 1)).hom a = b := by
    intro b hb
    exact ((ShortComplex.moduleCat_exact_iff _).1 ((scalarsRes φ).exact_succ k)) b hb
  have hd1 := I.cochainComplex_d ((k : ℤ) + 1) ((k : ℤ) + 1 + 1) (k + 1) (k + 2) (by simp) (by push_cast; ring)
  rw [hd1] at hf
  have h2 : (f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom) ≫ I.cocomplex.d (k + 1) (k + 2) = 0 := by
    rw [← cancel_mono (I.cochainComplexXIso ((k : ℤ) + 1 + 1) (k + 2) (by push_cast; ring)).inv]
    simpa using hf
  have hf' : (f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom) ≫
      (homSh J).map ((scalarsRes φ).complex.d (k + 2) (k + 1)).op = 0 := by
    rw [← coindCx_d]
    exact h2
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_lift_etaleSheafOfLinearMaps_exact R J ((free R).obj P) (hJ P) _ _ _ _ _ hex _ hf'
  refine ⟨g ≫ (I.cochainComplexXIso (k : ℤ) k rfl).inv, ?_⟩
  rw [I.cochainComplex_d (k : ℤ) ((k : ℤ) + 1) k (k + 1) rfl (by simp)]
  erw [Category.assoc, Iso.inv_hom_id_assoc]
  have hg' : g ≫ I.cocomplex.d k (k + 1) = f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom := by
    rw [← hg, ← coindCx_d]
    rfl
  erw [← Category.assoc, hg', Category.assoc, Iso.hom_inv_id, Category.comp_id]
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coinducedSheaf_injectiveResolution_freeExact : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (J : Shv R) [Injective J], (∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) → ∃ (C : Cx R) (ε : sgl ((restr φ).obj ((coind φ).obj J)) ⟶ C), C.IsStrictlyGE 0 ∧ (∀ t, Injective (C.X t)) ∧ QuasiIso ε ∧ ∀ (P : PSh) (n : ℤ), 0 < n → Subsingleton (CohomologyClass (sgl ((free R).obj P)) C n) := by
  first | (exact @GlobalTheory.EtC.coindRes_exists) | (exact GlobalTheory.EtC.coindRes_exists) | (intros; apply GlobalTheory.EtC.coindRes_exists  <;> assumption)
end

section
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.EtC.restr_injective_acyclic : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Shv S) [Injective I]
    (P : PSh) (n : ℤ), 0 < n → Subsingleton (H R (disc.obj P) ((restr φ).obj I) n) := by
  intro R S _ _ φ I _ P n hn
  obtain ⟨J, hJ, i, r, hir⟩ := GlobalTheory.T.injective_etaleSheaf_retract_of_coinduced R S φ I
  obtain ⟨C, ε, hC0, hCi, hqi, hCz⟩ := GlobalTheory.T.exists_coinducedSheaf_injectiveResolution_freeExact R S φ J (GlobalTheory.T.moduleInjective_hom_free_etaleSheaf_injective R J)
  have h1 : Subsingleton (HK R (sgl ((free R).obj P)) ((restr φ).obj ((coind φ).obj J)) n) := by
    obtain ⟨e⟩ := GlobalTheory.T.etaleHypercohomology_iso_of_injective_resolution R _ C ε hC0 hCi hqi (sgl ((free R).obj P)) n
    have := hCz P n hn
    exact e.injective.subsingleton
  have h2 : Subsingleton (HK R (sgl ((free R).obj P)) ((restr φ).obj I) n) :=
    GlobalTheory.T.subsingleton_etaleHypercohomology_of_retract R _ _ ((restr φ).map i) ((restr φ).map r)
      (by rw [← Functor.map_comp, hir]; exact (restr φ).map_id I) _ n h1
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  exact (GlobalTheory.T.quasiIso_hypercohomology_bijective R (e P).hom ((restr φ).obj I) n).1.subsingleton
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictScalars_injective_sheaf_acyclic : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Shv S) [Injective I] (P : PSh) (n : ℤ), 0 < n → Subsingleton (H R (disc.obj P) ((restr φ).obj I) n) := by
  atlas_forward_decl GlobalTheory.EtC.restr_injective_acyclic
end
