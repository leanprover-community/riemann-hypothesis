import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMappingConeResolutionHomotopyEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafExcisionShortExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyLongExactFirstOfInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceChainsMayerVietorisShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBiprodInlInrBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoFreeEtaleMayerVietorisLeftMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMayerVietorisFreeRightEpiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMayerVietorisFreeSequenceExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafExcisionShortExact

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

theorem chains_spMap_comp (R : Type) [CommRing R] {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B)
    (h : B →+* C) : (chains R).map (spMap h) ≫ (chains R).map (spMap g) = (chains R).map (spMap (h.comp g)) := by
  rw [← Functor.map_comp]
  congr 1
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem awayMap_comp_algebraMap {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (f : A) :
    (Localization.awayMap g f).comp (algebraMap A (Localization.Away f)) = (algebraMap B (Localization.Away (g f))).comp g :=
  IsLocalization.map_comp _

theorem excision_square_comm (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    (chains R).map (spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))) ≫ (chains R).map (spMap (algebraMap A A')) =
      (chains R).map (spMap (Localization.awayMap (algebraMap A A') f)) ≫
        (chains R).map (spMap (algebraMap A (Localization.Away f))) := by
  rw [chains_spMap_comp, chains_spMap_comp, awayMap_comp_algebraMap]

def excisionConeMap (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    mappingCone ((chains R).map (spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))) ⟶
      mappingCone ((chains R).map (spMap (algebraMap A (Localization.Away f)))) :=
  mappingCone.map _ _ _ _ (excision_square_comm R A A' f)

end GlobalTheory.EtC
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ExcisionQis

theorem map_descShortComplex {C : Type*} [Category C] [Abelian C] {K₁ K₂ L₁ L₂ M : CochainComplex C ℤ}
    (f' : K₁ ⟶ K₂) (g' : K₂ ⟶ M) (w' : f' ≫ g' = 0) (f : L₁ ⟶ L₂) (g : L₂ ⟶ M) (w : f ≫ g = 0)
    (a : K₁ ⟶ L₁) (b : K₂ ⟶ L₂) (comm : f' ≫ b = a ≫ f) (hg : g' = b ≫ g) :
    mappingCone.map f' f a b comm ≫ mappingCone.descShortComplex (ShortComplex.mk f g w) =
      mappingCone.descShortComplex (ShortComplex.mk f' g' w') := by
  ext n : 1
  apply mappingCone.ext_from _ (n + 1) n rfl
  · simp [mappingCone.map, mappingCone.descShortComplex, HomComplex.Cochain.zero_cochain_comp_v]
  · simp [mappingCone.map, mappingCone.descShortComplex, hg]

theorem cone_single_qis {C : Type*} [Category C] [Abelian C] {F1 F2 F3 F4 : C} (u' : F1 ⟶ F2) (u : F3 ⟶ F4)
    (a : F1 ⟶ F3) (b : F2 ⟶ F4) (comm : u' ≫ b = a ≫ u) [Mono u] (w : biprod.lift a (-u') ≫ biprod.desc u b = 0)
    (hS : (ShortComplex.mk _ _ w).ShortExact) :
    QuasiIso (mappingCone.map ((singleFunctor C 0).map u') ((singleFunctor C 0).map u) ((singleFunctor C 0).map a)
      ((singleFunctor C 0).map b) (by rw [← Functor.map_comp, ← Functor.map_comp, comm])) := by
  haveI : Mono (biprod.lift a (-u')) := hS.mono_f
  haveI : Epi (biprod.desc u b) := hS.epi_g
  let T : ShortComplex C := ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  have hT : T.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel u))
    inferInstance inferInstance
  have w' : u' ≫ b ≫ cokernel.π u = 0 := by
    rw [← Category.assoc, comm, Category.assoc, cokernel.condition, Limits.comp_zero]
  let T' : ShortComplex C := ShortComplex.mk u' (b ≫ cokernel.π u) w'
  have hmono : Mono u' := by
    refine Preadditive.mono_of_cancel_zero _ fun {Q} g hg => ?_
    have hga : g ≫ a = 0 := by
      rw [← cancel_mono u, Category.assoc, ← comm, ← Category.assoc, hg, Limits.zero_comp, Limits.zero_comp]
    have : g ≫ biprod.lift a (-u') = 0 := by
      apply biprod.hom_ext <;> simp [hga, hg]
    rw [← cancel_mono (biprod.lift a (-u')), this, Limits.zero_comp]
  have hepi : Epi (b ≫ cokernel.π u) := by
    refine Preadditive.epi_of_cancel_zero _ fun {Q} h hh => ?_
    have h1 : biprod.desc u b ≫ cokernel.π u ≫ h = 0 := by
      apply biprod.hom_ext'
      · simp
      · simpa using hh
    have h2 : cokernel.π u ≫ h = 0 := by
      rw [← cancel_epi (biprod.desc u b), h1, Limits.comp_zero]
    rw [← cancel_epi (cokernel.π u), h2, Limits.comp_zero]
  have hexact : T'.Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A₀ y hy
    have hy' : (y ≫ b) ≫ T.g = 0 := by simpa using hy
    obtain ⟨A₁, e₁, he₁, z, hz⟩ := (ShortComplex.exact_iff_exact_up_to_refinements T).1 hT.exact (y ≫ b) hy'
    have hw : biprod.lift (-z) (e₁ ≫ y) ≫ (ShortComplex.mk _ _ w).g = 0 := by
      change biprod.lift (-z) (e₁ ≫ y) ≫ biprod.desc u b = 0
      rw [biprod.lift_desc, Preadditive.neg_comp, Category.assoc, hz]
      exact neg_add_cancel _
    obtain ⟨A₂, e₂, he₂, x, hx⟩ := (ShortComplex.exact_iff_exact_up_to_refinements _).1 hS.exact _ hw
    refine ⟨A₂, e₂ ≫ e₁, inferInstance, -x, ?_⟩
    have h2 := congrArg (· ≫ biprod.snd) hx
    simp only [Category.assoc] at h2
    rw [biprod.lift_snd, biprod.lift_snd] at h2
    show (e₂ ≫ e₁) ≫ y = (-x) ≫ u'
    rw [Category.assoc, h2, Preadditive.neg_comp, Preadditive.comp_neg]
  have hT' : T'.ShortExact := ShortComplex.ShortExact.mk' hexact hmono hepi
  have z1 : (singleFunctor C 0).map u ≫ (singleFunctor C 0).map (cokernel.π u) = 0 := by
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  have z2 : (singleFunctor C 0).map u' ≫ (singleFunctor C 0).map (b ≫ cokernel.π u) = 0 := by
    rw [← Functor.map_comp, w', Functor.map_zero]
  have c2 : (singleFunctor C 0).map u' ≫ (singleFunctor C 0).map b = (singleFunctor C 0).map a ≫ (singleFunctor C 0).map u := by
    rw [← Functor.map_comp, ← Functor.map_comp, comm]
  have hST : (ShortComplex.mk _ _ z1).ShortExact := hT.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)
  have hST' : (ShortComplex.mk _ _ z2).ShortExact := hT'.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)
  haveI := mappingCone.quasiIso_descShortComplex hST
  haveI := mappingCone.quasiIso_descShortComplex hST'
  have key := map_descShortComplex _ _ z2 _ _ z1 ((singleFunctor C 0).map a) ((singleFunctor C 0).map b) c2
    (Functor.map_comp _ _ _)
  haveI : QuasiIso (mappingCone.map _ _ _ _ c2 ≫ mappingCone.descShortComplex (ShortComplex.mk _ _ z1)) := by
    rw [key]; exact mappingCone.quasiIso_descShortComplex hST'
  exact quasiIso_of_comp_right _ (mappingCone.descShortComplex (ShortComplex.mk _ _ z1))

theorem mono_free_away (R : Type) [CommRing R] (A : Type) [CommRing A] (f : A) :
    Mono ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) := by
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))) :=
    IsOpenImmersion.of_isLocalization f
  have h1 : Mono (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))) := inferInstance
  have h2 : Mono ((freeP R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) := by
    have happ : ∀ U, Mono (((freeP R).map (yoneda.map (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away f)))))).app U) := fun U => by
      have hinj : Function.Injective
          ((yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))).app U) :=
        (mono_iff_injective _).1 inferInstance
      rw [ModuleCat.mono_iff_injective]
      change Function.Injective (Finsupp.mapDomain _)
      exact Finsupp.mapDomain_injective (fun x y hxy => ULift.ext _ _ (hinj (congrArg ULift.down hxy)))
    exact NatTrans.mono_of_mono_app _
  change Mono ((presheafToSheaf _ _).map ((freeP R).map _))
  infer_instance

theorem quasiIso_map_of_corners {C : Type*} [Category C] [Abelian C] {K₁ K₂ K₃ K₄ L₁ L₂ L₃ L₄ : CochainComplex C ℤ}
    (φ' : K₁ ⟶ K₂) (φ : K₃ ⟶ K₄) (α : K₁ ⟶ K₃) (β : K₂ ⟶ K₄) (c₀ : φ' ≫ β = α ≫ φ)
    (ψ' : L₁ ⟶ L₂) (ψ : L₃ ⟶ L₄) (α' : L₁ ⟶ L₃) (β' : L₂ ⟶ L₄) (c₁ : ψ' ≫ β' = α' ≫ ψ)
    (e₁ : K₁ ⟶ L₁) (e₂ : K₂ ⟶ L₂) (e₃ : K₃ ⟶ L₃) (e₄ : K₄ ⟶ L₄) (q₁ : QuasiIso e₁) (q₂ : QuasiIso e₂)
    (q₃ : QuasiIso e₃) (q₄ : QuasiIso e₄) (h₁₂ : φ' ≫ e₂ = e₁ ≫ ψ') (h₃₄ : φ ≫ e₄ = e₃ ≫ ψ) (h₁₃ : α ≫ e₃ = e₁ ≫ α')
    (h₂₄ : β ≫ e₄ = e₂ ≫ β') [QuasiIso (mappingCone.map φ' φ α β c₀)] :
    QuasiIso (mappingCone.map ψ' ψ α' β' c₁) := by
  haveI := q₁; haveI := q₂; haveI := q₃; haveI := q₄
  have key : mappingCone.map φ' ψ' e₁ e₂ h₁₂ ≫ mappingCone.map ψ' ψ α' β' c₁ =
      mappingCone.map φ' φ α β c₀ ≫ mappingCone.map φ ψ e₃ e₄ h₃₄ := by
    rw [← mappingCone.map_comp, ← mappingCone.map_comp]
    congr 1
    · exact h₁₃.symm
    · exact h₂₄.symm
  haveI := GlobalTheory.EtC.ConeRes.quasiIso_mappingCone_map φ' ψ' e₁ e₂ h₁₂
  haveI := GlobalTheory.EtC.ConeRes.quasiIso_mappingCone_map φ ψ e₃ e₄ h₃₄
  haveI : QuasiIso (mappingCone.map φ' ψ' e₁ e₂ h₁₂ ≫ mappingCone.map ψ' ψ α' β' c₁) := by
    rw [key]; infer_instance
  exact quasiIso_of_comp_left (mappingCone.map φ' ψ' e₁ e₂ h₁₂) _

theorem _root_.GlobalTheory.EtC.excisionConeMap_quasiIso : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → QuasiIso (excisionConeMap R A A' f) := by
  intro R _ A A' _ _ _ f h
  obtain ⟨e, -, he⟩ := chains_disc_homotopyEquiv R
  haveI : Algebra.Etale A A' := h.1
  have comm : (free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))) ≫
      (free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))) =
      (free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f)))) ≫
      (free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))) := by
    simp only [← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, awayMap_comp_algebraMap]
  have w : biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f)))))
      (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))) ≫
      biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))))
        ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A'))))) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, ← comm, add_neg_cancel]
  have hS := GlobalTheory.T.freeEtaleSheaf_excision_shortExact R A A' f ⟨h.2.1, h.2.2⟩ w
  haveI := mono_free_away R A f
  haveI := cone_single_qis _ _ _ _ comm w hS
  exact quasiIso_map_of_corners _ _ _ _ _ _ _ _ _ _ _ _ _ _ (e _).quasiIso_hom (e _).quasiIso_hom
    (e _).quasiIso_hom (e _).quasiIso_hom (he _).symm (he _).symm (he _).symm (he _).symm

end GlobalTheory.EtC.ExcisionQis

end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.excisionConeMap_quasiIso' : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → QuasiIso (excisionConeMap R A A' f) := by
  first | (exact @GlobalTheory.EtC.excisionConeMap_quasiIso) | (exact GlobalTheory.EtC.excisionConeMap_quasiIso) | (intros; apply GlobalTheory.EtC.excisionConeMap_quasiIso <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.NatRef

variable {R : Type} [CommRing R]

theorem cpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = CohomologyClass.mk _
  congr 1; ext1; simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem cpull_inr_map {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (I : Cx R) (n : ℤ) (x : CohomologyClass (mappingCone φ₂) I n) :
    cpull (mappingCone.inr φ₁) I n (cpull (mappingCone.map φ₁ φ₂ a b comm) I n x) =
      cpull b I n (cpull (mappingCone.inr φ₂) I n x) := by
  rw [← cpull_comp, ← cpull_comp]
  congr 2
  simp [mappingCone.map]

theorem cpull_map_fst {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (I : Cx R) (n : ℤ) (x : CohomologyClass K₂ I n) :
    cpull (mappingCone.map φ₁ φ₂ a b comm) I (n + 1) (cpre (mappingCone.fst φ₂) I n (n + 1) (by omega) x) =
      cpre (mappingCone.fst φ₁) I n (n + 1) (by omega) (cpull a I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = CohomologyClass.mk _
  congr 1; ext1
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
  have key : (Cochain.ofHom (mappingCone.map φ₁ φ₂ a b comm)).comp (mappingCone.fst φ₂).1 (zero_add 1) =
      (mappingCone.fst φ₁).1.comp (Cochain.ofHom a) (add_zero 1) := by
    refine (mappingCone.ext_cochain_from_iff φ₁ 0 1 rfl).2 ⟨?_, ?_⟩
    · rw [← Cochain.comp_assoc _ _ _ (show -1 + 0 = -1 by omega) (zero_add 1) (by omega), ← Cochain.comp_assoc _ _ _ (show -1 + 1 = 0 by omega) (add_zero 1) (by omega)]
      simp [mappingCone.map, Cochain.comp_assoc_of_second_is_zero_cochain]
    · rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain]
      simp [mappingCone.map, Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, key, Cochain.comp_assoc_of_second_is_zero_cochain]

end GlobalTheory.EtC.NatRef

namespace GlobalTheory.EtC.NatRef
variable {R : Type} [CommRing R]

theorem abstract_nat {K L K' L' : Cx R} (φ : K ⟶ L) (φ' : K' ⟶ L') (a : K' ⟶ K) (b : L' ⟶ L)
    (comm : φ' ≫ b = a ≫ φ) (I : Cx R) (n : ℤ)
    (hbij : Function.Bijective (cpull (mappingCone.map φ' φ a b comm) I (n + 1))) :
    ∃ δ : CohomologyClass K' I n →+ CohomologyClass L I (n + 1),
      Function.Exact δ (fun x : CohomologyClass L I (n + 1) => (cpull φ I (n + 1) x, cpull b I (n + 1) x)) ∧
      ∀ {K₂ L₂ : Cx R} (φ₂ : K₂ ⟶ L₂) (a₂ : K₂ ⟶ K') (b₂ : L₂ ⟶ L') (comm₂ : φ₂ ≫ b₂ = a₂ ≫ φ')
        (a₃ : K₂ ⟶ K) (b₃ : L₂ ⟶ L) (comm₃ : φ₂ ≫ b₃ = a₃ ≫ φ), a₂ ≫ a = a₃ → b₂ ≫ b = b₃ →
        Function.Injective (cpull (mappingCone.map φ₂ φ a₃ b₃ comm₃) I (n + 1)) →
        ∀ (w : CohomologyClass K' I n) (c : CohomologyClass K I n), cpull a₂ I n w = cpull a₃ I n c → δ w = 0 := by
  set m := mappingCone.map φ' φ a b comm
  let e := AddEquiv.ofBijective _ hbij
  have he : ∀ y, cpull m I (n + 1) (e.symm y) = y := e.apply_symm_apply
  have he' : ∀ r, e.symm (cpull m I (n + 1) r) = r := e.symm_apply_apply
  have P1 := (coneSeq_exact R φ I (n + 1)).1
  have P3 := (coneSeq_exact R φ' I n).2.2
  have P3φ := (coneSeq_exact R φ I n).2.2
  refine ⟨(cpull (mappingCone.inr φ) I (n + 1)).comp
    (e.symm.toAddMonoidHom.comp (cpre (mappingCone.fst φ') I n (n + 1) (by omega))), ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hx1 : cpull φ I (n + 1) x = 0 := congrArg Prod.fst hx
      have hx2 : cpull b I (n + 1) x = 0 := congrArg Prod.snd hx
      obtain ⟨r, rfl⟩ := (P1 x).1 hx1
      have h0 : cpull (mappingCone.inr φ') I (n + 1) (cpull m I (n + 1) r) = 0 := by
        rw [cpull_inr_map]; exact hx2
      obtain ⟨w, hw⟩ := (P3 _).1 h0
      refine ⟨w, ?_⟩
      change cpull (mappingCone.inr φ) I (n + 1) (e.symm (cpre (mappingCone.fst φ') I n (n + 1) _ w)) = _
      rw [hw, he']
    · rintro ⟨w, rfl⟩
      refine Prod.ext ((P1 _).2 ⟨_, rfl⟩) ?_
      change cpull b I (n + 1) (cpull (mappingCone.inr φ) I (n + 1) (e.symm (cpre (mappingCone.fst φ') I n (n + 1) _ w))) = 0
      rw [← cpull_inr_map φ' φ a b comm, he]
      exact (P3 _).2 ⟨w, rfl⟩
  · intro K₂ L₂ φ₂ a₂ b₂ comm₂ a₃ b₃ comm₃ ha hb hinj w c hwc
    subst ha hb
    have hM : mappingCone.map φ₂ φ (a₂ ≫ a) (b₂ ≫ b) comm₃ =
        mappingCone.map φ₂ φ' a₂ b₂ comm₂ ≫ m := mappingCone.map_comp φ₂ φ' φ a₂ b₂ comm₂ a b comm
    have hr : e.symm (cpre (mappingCone.fst φ') I n (n + 1) (by omega) w) =
        cpre (mappingCone.fst φ) I n (n + 1) (by omega) c := by
      apply hinj
      rw [cpull_map_fst, ← hwc, hM, cpull_comp, he, cpull_map_fst]
    change cpull (mappingCone.inr φ) I (n + 1) (e.symm (cpre (mappingCone.fst φ') I n (n + 1) _ w)) = 0
    rw [hr]
    exact (P3φ _).2 ⟨c, rfl⟩

end GlobalTheory.EtC.NatRef

namespace GlobalTheory.EtC

open NatRef in

theorem excision_boundary_natural_refine : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ), ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A₂ : Type) [CommRing A₂] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂], IsExcisionNbhd A A₂ f → ∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ∀ (w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i) (b : Ht q (sp (Localization.Away f)) n i), pull _ (spMap φ) _ _ w = pull _ (spMap (Localization.awayMap (algebraMap A A₂) f)) _ _ b → δ w = 0 := by
  intro q A A' _ _ _ f hN n i
  have hbij : ∀ (B : Type) [CommRing B] [Algebra A B], IsExcisionNbhd A B f →
      Function.Bijective (cpull (excisionConeMap (ZMod q) A B f) (res (ZMod q) (tw q i)) (n + 1)) := by
    intro B _ _ hB
    haveI := GlobalTheory.T.excisionConeMap_quasiIso' (ZMod q) A B f hB
    exact quasiIso_hypercohomology_bijective' (ZMod q) (excisionConeMap (ZMod q) A B f) (tw q i) (n + 1)
  obtain ⟨δ, hex, hnat⟩ := abstract_nat _ _ _ _ (excision_square_comm (ZMod q) A A' f) (res (ZMod q) (tw q i)) n
    (hbij A' hN)
  refine ⟨δ, hex, ?_⟩
  intro A₂ _ _ _ _ h₂ φ hφ w b hwb
  refine hnat ((chains (ZMod q)).map (spMap (algebraMap A₂ (Localization.Away (algebraMap A A₂ f)))))
    ((chains (ZMod q)).map (spMap φ)) ((chains (ZMod q)).map (spMap (algebraMap A' A₂))) ?_ _ _
    (excision_square_comm (ZMod q) A A₂ f) ?_ ?_ (hbij A₂ h₂).1 w b hwb
  · rw [chains_spMap_comp, chains_spMap_comp, hφ]
  · rw [chains_spMap_comp]
    congr 2
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    rw [RingHom.comp_assoc, awayMap_comp_algebraMap, awayMap_comp_algebraMap, ← RingHom.comp_assoc, hφ,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  · rw [chains_spMap_comp, ← IsScalarTower.algebraMap_eq]

end GlobalTheory.EtC
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_natural_excision_boundary_etaleNbhd : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ), ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A₂ : Type) [CommRing A₂] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂], IsExcisionNbhd A A₂ f → ∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ∀ (w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i) (b : Ht q (sp (Localization.Away f)) n i), pull _ (spMap φ) _ _ w = pull _ (spMap (Localization.awayMap (algebraMap A A₂) f)) _ _ b → δ w = 0 := by
  first | (exact @GlobalTheory.EtC.excision_boundary_natural_refine) | (exact GlobalTheory.EtC.excision_boundary_natural_refine) | (intros; apply GlobalTheory.EtC.excision_boundary_natural_refine <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.MVEtale

theorem cpull_neg {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull (-g) I n x = -cpull g I n x := by
  have h := BiprodCls.cpull_add g (-g) I n x
  rw [add_neg_cancel, BiprodCls.cpull_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped TensorProduct in
theorem _root_.GlobalTheory.EtC.MVEtale.cpull_lift_neg {R : Type} [CommRing R] {K M N : _root_.GlobalTheory.EtC.Cx R} (a : K ⟶ M) (b : K ⟶ N) (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ)
    (x : CohomologyClass (M ⊞ N) I n) :
    _root_.GlobalTheory.EtC.cpull (biprod.lift a (-b)) I n x =
      _root_.GlobalTheory.EtC.cpull a I n (_root_.GlobalTheory.EtC.cpull (biprod.inl : M ⟶ M ⊞ N) I n x) - _root_.GlobalTheory.EtC.cpull b I n (_root_.GlobalTheory.EtC.cpull (biprod.inr : N ⟶ M ⊞ N) I n x) := by
  rw [biprod.lift_eq, _root_.GlobalTheory.EtC.BiprodCls.cpull_add, Preadditive.neg_comp,
    _root_.GlobalTheory.EtC.MayerVietoris.cpull_neg, _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull,
    _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, sub_eq_add_neg]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped TensorProduct in
theorem _root_.GlobalTheory.EtC.MVEtale.cpull_desc_pair {R : Type} [CommRing R] {M N L : _root_.GlobalTheory.EtC.Cx R} (c : M ⟶ L) (d : N ⟶ L) (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ)
    (z : CohomologyClass L I n) :
    (_root_.GlobalTheory.EtC.cpull (biprod.inl : M ⟶ M ⊞ N) I n (_root_.GlobalTheory.EtC.cpull (biprod.desc c d) I n z),
      _root_.GlobalTheory.EtC.cpull (biprod.inr : N ⟶ M ⊞ N) I n (_root_.GlobalTheory.EtC.cpull (biprod.desc c d) I n z)) = (_root_.GlobalTheory.EtC.cpull c I n z, _root_.GlobalTheory.EtC.cpull d I n z) := by
  rw [_root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, biprod.inl_desc,
    biprod.inr_desc]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped TensorProduct in
theorem _root_.GlobalTheory.EtC.MVEtale.chains_shortExact (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (f : A)
    (h1 : ∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f})
    (h2 : ∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) :
    ∃ w, (ShortComplex.mk (biprod.lift ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (Localization.awayMap (algebraMap A A') f)))
      (-(_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))))
      (biprod.desc ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A (Localization.Away f)))) ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A A')))) w).ShortExact := by
  have hcomp : (Localization.awayMap (algebraMap A A') f).comp (algebraMap A (Localization.Away f)) =
      (algebraMap A' (Localization.Away (algebraMap A A' f))).comp (algebraMap A A') :=
    IsLocalization.map_comp _
  have hsq : _root_.GlobalTheory.EtC.spMap (Localization.awayMap (algebraMap A A') f) ≫
      _root_.GlobalTheory.EtC.spMap (algebraMap A (Localization.Away f)) =
      _root_.GlobalTheory.EtC.spMap (algebraMap A' (Localization.Away (algebraMap A A' f))) ≫
      _root_.GlobalTheory.EtC.spMap (algebraMap A A') := by
    unfold _root_.GlobalTheory.EtC.spMap
    rw [← Functor.map_comp, ← Functor.map_comp, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomp]
  have hchains := ((_root_.GlobalTheory.EtC.chains R).map_comp _ _).symm.trans
    ((congrArg (_root_.GlobalTheory.EtC.chains R).map hsq).trans
      ((_root_.GlobalTheory.EtC.chains R).map_comp _ _))
  obtain ⟨w', hw'⟩ := _root_.GlobalTheory.EtC.MVExact.mv_exact R A A' f h1 h2
  have hfree := _root_.GlobalTheory.EtC.MVFree.shortExact R A A' f ⟨h1, h2⟩ w'
  have w : biprod.lift ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (Localization.awayMap (algebraMap A A') f)))
      (-(_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))) ≫
      biprod.desc ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A (Localization.Away f))))
        ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A A'))) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, hchains, add_neg_cancel]
  refine ⟨w, HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_⟩
  rcases lt_or_ge 0 i with hi | hi
  · have hX₁ := _root_.GlobalTheory.EtC.chains_isZero_pos R
      (_root_.GlobalTheory.EtC.sp (Localization.Away (algebraMap A A' f))) i hi
    have hX₃ := _root_.GlobalTheory.EtC.chains_isZero_pos R (_root_.GlobalTheory.EtC.sp A) i hi
    have hX₂ : IsZero (((_root_.GlobalTheory.EtC.chains R).obj (_root_.GlobalTheory.EtC.sp (Localization.Away f)) ⊞
        (_root_.GlobalTheory.EtC.chains R).obj (_root_.GlobalTheory.EtC.sp A')).X i) :=
      IsZero.of_iso ((biprod_isZero_iff _ _).2
        ⟨_root_.GlobalTheory.EtC.chains_isZero_pos R _ i hi, _root_.GlobalTheory.EtC.chains_isZero_pos R _ i hi⟩)
        (HomologicalComplex.biprodXIso _ _ i)
    exact
      { exact := ShortComplex.exact_of_isZero_X₂ _ hX₂
        mono_f := ⟨fun _ _ _ => hX₁.eq_of_tgt _ _⟩
        epi_g := ⟨fun _ _ _ => hX₃.eq_of_src _ _⟩ }
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨i.natAbs, by omega⟩
    exact _root_.GlobalTheory.EtC.mv_map_shortExact (HomologicalComplex.eval _ _ (-(p : ℤ)))
      (a := (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (Localization.awayMap (algebraMap A A') f)))
      (b := (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))))
      (f := (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A (Localization.Away f))))
      (g := (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A A')))
      (W' := (_root_.GlobalTheory.EtC.free R).obj (yoneda.obj (Spec (CommRingCat.of (Localization.Away ((algebraMap A A') f))))))
      (X' := (_root_.GlobalTheory.EtC.free R).obj (yoneda.obj (Spec (CommRingCat.of (Localization.Away f)))))
      (Y' := (_root_.GlobalTheory.EtC.free R).obj (yoneda.obj (Spec (CommRingCat.of A'))))
      (Z' := (_root_.GlobalTheory.EtC.free R).obj (yoneda.obj (Spec (CommRingCat.of A))))
      (a' := (_root_.GlobalTheory.EtC.free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f)))))
      (b' := (_root_.GlobalTheory.EtC.free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))))
      (f' := (_root_.GlobalTheory.EtC.free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))))
      (g' := (_root_.GlobalTheory.EtC.free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))
      (_root_.GlobalTheory.EtC.chainsXIso R _ p) (_root_.GlobalTheory.EtC.chainsXIso R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso R _ p) (_root_.GlobalTheory.EtC.chainsXIso R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R _ p) w w' hfree

end GlobalTheory.EtC.MVEtale
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.MVEtale

theorem mv_etale_mid : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → ∀ (n i : ℤ) (x : Ht q (sp (Localization.Away f)) n i) (y : Ht q (sp A') n i), pull _ (spMap (Localization.awayMap (algebraMap A A') f)) _ _ x = pull _ (spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))) _ _ y → ∃ b : Ht q (sp A) n i, pull _ (spMap (algebraMap A (Localization.Away f))) _ _ b = x ∧ pull _ (spMap (algebraMap A A')) _ _ b = y := by
  intro q A A' _ _ _ _ f h1 h2 n i x y hxy
  obtain ⟨w, hS⟩ := chains_shortExact (ZMod q) A A' f h1 h2
  obtain ⟨d, hd, -⟩ := GlobalTheory.T.hypercohomology_longExact_first_of_injective (ZMod q) (res (ZMod q) (tw q i)) (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)).2.1
  obtain ⟨e1, -, -⟩ := hd _ hS n
  have hb := cpull_biprod_bijective (ZMod q) ((chains (ZMod q)).obj (sp (Localization.Away f)))
    ((chains (ZMod q)).obj (sp A')) (res (ZMod q) (tw q i))
  obtain ⟨P, hP⟩ := (hb n).2 (x, y)
  have h0 : cpull (biprod.lift ((chains (ZMod q)).map (spMap (Localization.awayMap (algebraMap A A') f)))
      (-(chains (ZMod q)).map (spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))))
      (res (ZMod q) (tw q i)) n P = 0 := by
    rw [cpull_lift_neg]
    have hP1 := congrArg Prod.fst hP
    have hP2 := congrArg Prod.snd hP
    simp only at hP1 hP2
    rw [hP1, hP2]
    exact sub_eq_zero.2 hxy
  obtain ⟨b, hb'⟩ := (e1 P).1 h0
  refine ⟨b, ?_, ?_⟩
  · have := congrArg Prod.fst (cpull_desc_pair ((chains (ZMod q)).map (spMap (algebraMap A (Localization.Away f))))
      ((chains (ZMod q)).map (spMap (algebraMap A A'))) (res (ZMod q) (tw q i)) n b)
    simp only at this
    have hb1 : cpull (biprod.desc ((chains (ZMod q)).map (spMap (algebraMap A (Localization.Away f))))
      ((chains (ZMod q)).map (spMap (algebraMap A A')))) (res (ZMod q) (tw q i)) n b = P := hb'
    rw [hb1] at this
    exact this.symm.trans (congrArg Prod.fst hP)
  · have := congrArg Prod.snd (cpull_desc_pair ((chains (ZMod q)).map (spMap (algebraMap A (Localization.Away f))))
      ((chains (ZMod q)).map (spMap (algebraMap A A'))) (res (ZMod q) (tw q i)) n b)
    simp only at this
    have hb1 : cpull (biprod.desc ((chains (ZMod q)).map (spMap (algebraMap A (Localization.Away f))))
      ((chains (ZMod q)).map (spMap (algebraMap A A')))) (res (ZMod q) (tw q i)) n b = P := hb'
    rw [hb1] at this
    exact this.symm.trans (congrArg Prod.snd hP)

end GlobalTheory.EtC.MVEtale
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_pullback_injective : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → ∀ (n i : ℤ) (x : Ht q (sp (Localization.Away f)) n i) (y : Ht q (sp A') n i), pull _ (spMap (Localization.awayMap (algebraMap A A') f)) _ _ x = pull _ (spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))) _ _ y → ∃ b : Ht q (sp A) n i, pull _ (spMap (algebraMap A (Localization.Away f))) _ _ b = x ∧ pull _ (spMap (algebraMap A A')) _ _ b = y := by
  first | (exact @GlobalTheory.EtC.MVEtale.mv_etale_mid) | (exact GlobalTheory.EtC.MVEtale.mv_etale_mid) | (intros; apply GlobalTheory.EtC.MVEtale.mv_etale_mid <;> assumption)
end

section
theorem GlobalTheory.away_congr_of_isCoprime : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → (∀ c : C, ∃ a : A, c - algebraMap A C a ∈ Ideal.span {algebraMap A C g}) → ∀ c' : Localization.Away (algebraMap A C f), ∃ b : Localization.Away f, c' - Localization.awayMap (algebraMap A C) f b ∈ Ideal.span {Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) g)} := by
  intro A C _ _ _ f g hfg hC c'
  obtain ⟨u, v, huv⟩ := hfg
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A C f)) c'
  obtain ⟨k, hk⟩ := s.2
  obtain ⟨a, ha⟩ := hC c
  refine ⟨algebraMap A (Localization.Away f) (a * u ^ k), ?_⟩
  have hmap : ∀ x : A, Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) x)
      = algebraMap C (Localization.Away (algebraMap A C f)) (algebraMap A C x) :=
    fun x => IsLocalization.map_eq _ _
  rw [hmap, hmap]
  rw [Ideal.mem_span_singleton] at ha ⊢
  have hunit : IsUnit (algebraMap C (Localization.Away (algebraMap A C f)) (s : C)) :=
    IsLocalization.map_units _ s
  rw [← hunit.dvd_mul_right]
  have key : (IsLocalization.mk' (Localization.Away (algebraMap A C f)) c s
      - algebraMap C (Localization.Away (algebraMap A C f)) (algebraMap A C (a * u ^ k)))
      * algebraMap C (Localization.Away (algebraMap A C f)) (s : C)
      = algebraMap C (Localization.Away (algebraMap A C f)) (c - algebraMap A C (a * (u * f) ^ k)) := by
    rw [sub_mul, IsLocalization.mk'_spec, ← hk]
    simp only [map_sub, map_mul, map_pow]
    ring
  rw [key]
  apply map_dvd
  have h1 : g ∣ a * (1 - (u * f) ^ k) := by
    have h2 : g ∣ 1 - u * f := ⟨v, by rw [← huv]; ring⟩
    have h3 : 1 - u * f ∣ 1 ^ k - (u * f) ^ k := sub_dvd_pow_sub_pow 1 (u * f) k
    rw [one_pow] at h3
    exact Dvd.dvd.mul_left (h2.trans h3) a
  have h4 := map_dvd (algebraMap A C) h1
  have : c - algebraMap A C (a * (u * f) ^ k) = (c - algebraMap A C a) + algebraMap A C (a * (1 - (u * f) ^ k)) := by
    simp only [map_sub, map_mul, map_pow, map_one]; ring
  rw [this]
  exact dvd_add ha h4
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.away_congr_mod_of_isCoprime : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → (∀ c : C, ∃ a : A, c - algebraMap A C a ∈ Ideal.span {algebraMap A C g}) → ∀ c' : Localization.Away (algebraMap A C f), ∃ b : Localization.Away f, c' - Localization.awayMap (algebraMap A C) f b ∈ Ideal.span {Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) g)} := by
  first | (exact @GlobalTheory.away_congr_of_isCoprime) | (exact GlobalTheory.away_congr_of_isCoprime) | (intros; apply GlobalTheory.away_congr_of_isCoprime <;> assumption)
end

section
namespace GlobalTheory

theorem awayMap_descends_divisibility : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), (∀ a : A, algebraMap A C a ∈ Ideal.span {algebraMap A C g} → a ∈ Ideal.span {g}) → ∀ b : Localization.Away f, Localization.awayMap (algebraMap A C) f b ∈ Ideal.span {Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) g)} → b ∈ Ideal.span {algebraMap A (Localization.Away f) g} := by
  intro A C _ _ _ f g H b hb
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) b
  rw [Ideal.mem_span_singleton'] at hb
  obtain ⟨d, hd⟩ := hb
  obtain ⟨⟨c, ⟨_, m, rfl⟩⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A C f)) d
  simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk',
    IsLocalization.map_eq] at hd
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq,
    IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap A C f))] at hd
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := hd
  simp only [map_pow] at hn
  have key : algebraMap A C (f ^ (n + m) * a) ∈ Ideal.span {algebraMap A C g} := by
    rw [Ideal.mem_span_singleton']
    refine ⟨algebraMap A C f ^ (n + k) * c, ?_⟩
    rw [map_mul, map_pow, pow_add, pow_add]
    linear_combination hn
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp (H _ key)
  rw [Ideal.mem_span_singleton']
  refine ⟨IsLocalization.mk' (Localization.Away f) e
    (⟨f ^ (n + m + k), n + m + k, rfl⟩ : Submonoid.powers f), ?_⟩
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq]
  congr 1
  simp only
  rw [pow_add, mul_comm g e, he]
  ring

end GlobalTheory
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.awayMap_span_singleton_divisibility_descends : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), (∀ a : A, algebraMap A C a ∈ Ideal.span {algebraMap A C g} → a ∈ Ideal.span {g}) → ∀ b : Localization.Away f, Localization.awayMap (algebraMap A C) f b ∈ Ideal.span {Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) g)} → b ∈ Ideal.span {algebraMap A (Localization.Away f) g} := by
  first | (exact @GlobalTheory.awayMap_descends_divisibility) | (exact GlobalTheory.awayMap_descends_divisibility) | (intros; apply GlobalTheory.awayMap_descends_divisibility <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.MVGlue

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem etale_awayMap : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] [Algebra.Etale A C] (f : A), @Algebra.Etale (Localization.Away f) (Localization.Away (algebraMap A C f)) _ _ (Localization.awayMap (algebraMap A C) f).toAlgebra := by
  intro A C _ _ _ _ f
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap A C f)) :=
    (Localization.awayMap (algebraMap A C) f).toAlgebra
  haveI : Algebra.Etale C (Localization.Away (algebraMap A C f)) := Algebra.Etale.of_isLocalizationAway (algebraMap A C f)
  haveI : Algebra.Etale A (Localization.Away f) := Algebra.Etale.of_isLocalizationAway f
  haveI : Algebra.Etale A (Localization.Away (algebraMap A C f)) := Algebra.Etale.comp A C _
  haveI : IsScalarTower A (Localization.Away f) (Localization.Away (algebraMap A C f)) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    show _ = Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) a)
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq, IsScalarTower.algebraMap_apply A C (Localization.Away (algebraMap A C f))]
  exact Algebra.Etale.of_restrictScalars A _ _

theorem pull_spMap_comp (q : ℕ) {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (n i : ℤ) (x : Ht q (sp A) n i) :
    pull _ (spMap (g.comp f)) _ _ x = pull _ (spMap g) _ _ (pull _ (spMap f) _ _ x) := by
  rw [spMap_comp', pull_comp]

theorem pull_spMap_id (q : ℕ) {A : Type} [CommRing A] (n i : ℤ) (x : Ht q (sp A) n i) :
    pull _ (spMap (RingHom.id A)) _ _ x = x := by
  have : spMap (RingHom.id A) = 𝟙 (sp A) := by
    simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
    exact sch.map_id _
  rw [this, pull_id]

theorem glue : ∀ (q : ℕ) (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → IsExcisionNbhd A C g → ∀ (n i : ℤ) (a : Ht q (sp (Localization.Away (f * g))) n i), pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → ∃ b : Ht q (sp (Localization.Away f)) n i, ∀ ρ : Localization.Away f →+* Localization.Away (f * g), ρ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ρ) _ _ b = a := by
  intro q A C _ _ _ f g hfg hC n i a ha
  obtain ⟨hEt, h1, h2⟩ := hC
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap A C f)) :=
    (Localization.awayMap (algebraMap A C) f).toAlgebra
  haveI : Algebra.Etale (Localization.Away f) (Localization.Away (algebraMap A C f)) := etale_awayMap A C f
  have hB : algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) =
      Localization.awayMap (algebraMap A C) f := rfl
  set h : Localization.Away f := algebraMap A (Localization.Away f) g with hh
  have c1 := GlobalTheory.T.away_congr_mod_of_isCoprime A C f g hfg h1
  have c2 := GlobalTheory.T.awayMap_span_singleton_divisibility_descends A C f g h2
  rw [← hB] at c1 c2

  have hu1 : IsUnit (((algebraMap (Localization.Away f) (Localization.Away h)).comp
      (algebraMap A (Localization.Away f))) (f * g)) := by
    rw [map_mul, RingHom.comp_apply, RingHom.comp_apply]
    refine IsUnit.mul ?_ ?_
    · exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f).map
        (algebraMap (Localization.Away f) (Localization.Away h))
    · exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away h) h
  let ψ : Localization.Away (f * g) →+* Localization.Away h :=
    IsLocalization.Away.lift (S := Localization.Away (f * g)) (f * g) hu1
  have hψ : ∀ x : A, ψ (algebraMap A _ x) = algebraMap _ _ (algebraMap A (Localization.Away f) x) := fun x => by
    simp only [ψ, IsLocalization.Away.lift_eq, RingHom.comp_apply]
  have hgB : algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) h =
      algebraMap C (Localization.Away (algebraMap A C f)) (algebraMap A C g) := by
    rw [hB, hh]
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have hu2 : IsUnit (((algebraMap (Localization.Away (algebraMap A C f))
      (Localization.Away (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) h))).comp
      (algebraMap C (Localization.Away (algebraMap A C f)))) (algebraMap A C (f * g))) := by
    rw [map_mul, map_mul, RingHom.comp_apply, RingHom.comp_apply, ← hgB]
    refine IsUnit.mul ?_ (IsLocalization.Away.algebraMap_isUnit _)
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap A C f)) (algebraMap A C f)).map _
  let χ : Localization.Away (algebraMap A C (f * g)) →+*
      Localization.Away (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) h) :=
    IsLocalization.Away.lift (S := Localization.Away (algebraMap A C (f * g))) (algebraMap A C (f * g)) hu2
  have hsq : (Localization.awayMap (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f))) h).comp ψ =
      χ.comp (Localization.awayMap (algebraMap A C) (f * g)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f * g))
    ext x
    simp only [RingHom.comp_apply, hψ, χ]
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq, IsLocalization.Away.lift_eq, hB]
  obtain ⟨b, hb, -⟩ := GlobalTheory.T.localization_pullback_injective q (Localization.Away f) (Localization.Away (algebraMap A C f)) h c1 c2 n i
    (pull _ (spMap ψ) _ _ a) 0 (by
      rw [map_zero, ← pull_spMap_comp, hsq, pull_spMap_comp, ha, map_zero])
  refine ⟨b, fun ρ hρ => ?_⟩
  have hρu : IsUnit (ρ h) := by
    rw [hh, ← RingHom.comp_apply, hρ, map_mul] at *
    exact isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (f * g))
  let ψ' : Localization.Away h →+* Localization.Away (f * g) :=
    IsLocalization.Away.lift (S := Localization.Away h) h hρu
  have h1' : ψ'.comp (algebraMap (Localization.Away f) (Localization.Away h)) = ρ :=
    IsLocalization.Away.lift_comp _ _
  have h2' : ψ'.comp ψ = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f * g))
    ext x
    simp only [RingHom.comp_apply, hψ, ψ', IsLocalization.Away.lift_eq, RingHom.id_apply]
    rw [← RingHom.comp_apply ρ, hρ]
  rw [← h1', pull_spMap_comp, hb, ← pull_spMap_comp, h2', pull_spMap_id]

end GlobalTheory.MVGlue
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mayerVietoris_extend_class_coprime_etaleExcision : ∀ (q : ℕ) (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → IsExcisionNbhd A C g → ∀ (n i : ℤ) (a : Ht q (sp (Localization.Away (f * g))) n i), pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → ∃ b : Ht q (sp (Localization.Away f)) n i, ∀ ρ : Localization.Away f →+* Localization.Away (f * g), ρ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ρ) _ _ b = a := by
  first | (exact @GlobalTheory.MVGlue.glue) | (exact GlobalTheory.MVGlue.glue) | (intros; apply GlobalTheory.MVGlue.glue <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem mvRefine (L1 : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ), ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A₂ : Type) [CommRing A₂] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂], IsExcisionNbhd A A₂ f → ∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ∀ (w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i) (b : Ht q (sp (Localization.Away f)) n i), pull _ (spMap φ) _ _ w = pull _ (spMap (Localization.awayMap (algebraMap A A₂) f)) _ _ b → δ w = 0) (L2 : ∀ (q : ℕ) (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → IsExcisionNbhd A C g → ∀ (n i : ℤ) (a : Ht q (sp (Localization.Away (f * g))) n i), pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → ∃ b : Ht q (sp (Localization.Away f)) n i, ∀ ρ : Localization.Away f →+* Localization.Away (f * g), ρ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ρ) _ _ b = a) : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ) (x : Ht q (sp A) (n + 1) i), pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x = 0 → pull _ (spMap (algebraMap A A')) _ _ x = 0 → ∃ w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i, ∀ (g : A), IsCoprime f g → ∀ (A₂ C : Type) [CommRing A₂] [CommRing C] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂] [Algebra A C], IsExcisionNbhd A A₂ f → IsUnit (algebraMap A A₂ g) → IsExcisionNbhd A C g → ∀ a : Ht q (sp (Localization.Away (f * g))) n i, pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → (∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a) → x = 0 := by
  intro q A A' _ _ _ f hA' n i x hx1 hx2
  obtain ⟨δ, hδex, hδref⟩ := L1 q A A' f hA' n i
  obtain ⟨w, rfl⟩ := (hδex x).1 (by simp [hx1, hx2])
  refine ⟨w, ?_⟩
  intro g hfg A₂ C _ _ _ _ _ _ hA₂ hg hC a ha hcomp
  obtain ⟨b, hb⟩ := L2 q A C f g hfg hC n i a ha
  have hf2 : IsUnit (algebraMap A₂ (Localization.Away (algebraMap A A₂ f)) (algebraMap A A₂ f)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hg2 : IsUnit (algebraMap A₂ (Localization.Away (algebraMap A A₂ f)) (algebraMap A A₂ g)) := hg.map _
  let φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f) :=
    IsLocalization.Away.lift (algebraMap A A' f)
      (g := (algebraMap A₂ (Localization.Away (algebraMap A A₂ f))).comp (algebraMap A' A₂))
      (by simpa [← IsScalarTower.algebraMap_apply] using hf2)
  let ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f) :=
    IsLocalization.Away.lift (f * g)
      (g := (algebraMap A₂ (Localization.Away (algebraMap A A₂ f))).comp (algebraMap A A₂))
      (by simpa using hf2.mul hg2)
  have hfg' : IsUnit (algebraMap A (Localization.Away (f * g)) f) :=
    isUnit_of_mul_isUnit_left (by simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f * g)) (f * g))
  let ρ : Localization.Away f →+* Localization.Away (f * g) :=
    IsLocalization.Away.lift f (g := algebraMap A (Localization.Away (f * g))) hfg'
  have hφ : φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) := IsLocalization.Away.lift_comp _ _
  have hψ : ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) := IsLocalization.Away.lift_comp _ _
  have hρ : ρ.comp (algebraMap A _) = algebraMap A _ := IsLocalization.Away.lift_comp _ _
  have hψρ : ψ.comp ρ = Localization.awayMap (algebraMap A A₂) f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    rw [RingHom.comp_assoc, hρ, hψ]
    exact (IsLocalization.map_comp _).symm
  refine hδref A₂ hA₂ φ hφ w b ?_
  rw [hcomp φ ψ hφ hψ, ← hb ρ hρ, ← pull_comp, ← spMap_comp_ring, hψρ]

theorem mvRefine_main : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ) (x : Ht q (sp A) (n + 1) i), pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x = 0 → pull _ (spMap (algebraMap A A')) _ _ x = 0 → ∃ w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i, ∀ (g : A), IsCoprime f g → ∀ (A₂ C : Type) [CommRing A₂] [CommRing C] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂] [Algebra A C], IsExcisionNbhd A A₂ f → IsUnit (algebraMap A A₂ g) → IsExcisionNbhd A C g → ∀ a : Ht q (sp (Localization.Away (f * g))) n i, pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → (∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a) → x = 0 := mvRefine GlobalTheory.T.exists_natural_excision_boundary_etaleNbhd GlobalTheory.T.mayerVietoris_extend_class_coprime_etaleExcision

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleExcision_vanishing_under_refinement : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ) (x : Ht q (sp A) (n + 1) i), pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x = 0 → pull _ (spMap (algebraMap A A')) _ _ x = 0 → ∃ w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i, ∀ (g : A), IsCoprime f g → ∀ (A₂ C : Type) [CommRing A₂] [CommRing C] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂] [Algebra A C], IsExcisionNbhd A A₂ f → IsUnit (algebraMap A A₂ g) → IsExcisionNbhd A C g → ∀ a : Ht q (sp (Localization.Away (f * g))) n i, pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → (∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a) → x = 0 := by
  first | (exact @GlobalTheory.EtC.mvRefine_main) | (exact GlobalTheory.EtC.mvRefine_main) | (intros; apply GlobalTheory.EtC.mvRefine_main <;> assumption)
end
