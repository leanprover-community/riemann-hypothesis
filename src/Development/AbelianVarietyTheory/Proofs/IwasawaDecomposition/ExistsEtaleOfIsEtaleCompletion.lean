import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionUnramifiedNormal
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorResidueUnramifiedFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationMaximalIdealMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationResidueFiniteUnram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain

section
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory

theorem isDomain_isIntegrallyClosed_of_adicCompletion :
    ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T],
      IsDomain (AdicCompletion (maximalIdeal T) T) → IsIntegrallyClosed (AdicCompletion (maximalIdeal T) T) →
        IsDomain T ∧ IsIntegrallyClosed T := by
  intro T _ _ _ hD hI
  haveI : Module.FaithfullyFlat T (AdicCompletion (maximalIdeal T) T) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  set C := AdicCompletion (maximalIdeal T) T with hC
  set i := algebraMap T C with hi
  have hinj : Function.Injective i := FaithfulSMul.algebraMap_injective T C
  haveI hTD : IsDomain T := hinj.isDomain i
  refine ⟨hTD, ?_⟩
  set g : T →+* FractionRing C := (algebraMap C (FractionRing C)).comp i with hg
  have hginj : Function.Injective g := (IsFractionRing.injective C (FractionRing C)).comp hinj
  set φ : FractionRing T →+* FractionRing C := IsFractionRing.lift hginj with hφ
  rw [isIntegrallyClosed_iff (FractionRing T)]
  intro x hx
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors T) x
  have hφx : IsIntegral C (φ (IsLocalization.mk' (FractionRing T) a ⟨b, hb⟩)) := by
    refine IsIntegral.map_of_comp_eq i φ ?_ hx
    ext t
    simp [hφ, hg, IsFractionRing.lift_algebraMap]
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hφx
  have hmk : φ (IsLocalization.mk' (FractionRing T) a ⟨b, hb⟩) * g b = g a := by
    rw [hφ, IsFractionRing.lift_mk']
    exact div_mul_cancel₀ _ (map_ne_zero_of_mem_nonZeroDivisors g hginj hb)
  have hcb : c * i b = i a := by
    apply IsFractionRing.injective C (FractionRing C)
    rw [map_mul, hc]
    simpa [hg] using hmk
  have ha : a ∈ Ideal.span {b} := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := C) (Ideal.span {b}), Ideal.mem_comap,
      Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
    exact ⟨c, hcb⟩
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp ha
  refine ⟨d, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul]
  show algebraMap T (FractionRing T) (d * b) = _
  rw [hd]

end GlobalTheory
end

open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.domain_integrally_closed_of_completion : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T], IsDomain (AdicCompletion (maximalIdeal T) T) → IsIntegrallyClosed (AdicCompletion (maximalIdeal T) T) → IsDomain T ∧ IsIntegrallyClosed T := by
  atlas_forward_decl GlobalTheory.isDomain_isIntegrallyClosed_of_adicCompletion
end

section
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory.EtaleCompletionCharZero

theorem completion_isDomain_and_isIntegrallyClosed :
    ∀ (D T : Type) [CommRing D] [IsDomain D] [IsLocalRing D] [IsIntegrallyClosed D] [CharZero D]
      [Algebra.EssFiniteType ℤ D] [CommRing T] [IsLocalRing T] (h : D →+* T),
      IsNoetherianRing T → IsLocalHom h → h.Flat → (maximalIdeal D).map h = maximalIdeal T →
      ((residue T).comp h).Finite → ((residue T).comp h).FormallyUnramified →
      IsDomain (AdicCompletion (maximalIdeal T) T) ∧
        IsIntegrallyClosed (AdicCompletion (maximalIdeal T) T) := by
  intro D T _ _ _ _ _ _ _ _ h hT hloc hflat hm hfin hfu
  let R' := AdicCompletion (maximalIdeal T) T
  let ι : T →+* R' := algebraMap T R'
  have hι : IsLocalHom ι := inferInstance
  have hres : Function.Surjective (ResidueField.map ι) :=
    (AdicCompletion.residueField_map_bijective T).right
  have hcomp : (residue R').comp (ι.comp h) = (ResidueField.map ι).comp ((residue T).comp h) := by
    ext b
    simp
  have hD : IsNoetherianRing D := Algebra.EssFiniteType.isNoetherianRing ℤ D
  obtain ⟨h1, h2⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed D
  refine GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed D R' (ι.comp h) hD h1 h2
    (GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion T (maximalIdeal T)) inferInstance
    inferInstance ⟨?_, ?_, ?_⟩ ?_
  · exact RingHom.Flat.comp hflat (RingHom.flat_algebraMap_iff.mpr inferInstance)
  · rw [← Ideal.map_map, hm, AdicCompletion.maximalIdeal_eq_map]
  · rw [hcomp]
    exact RingHom.Finite.comp (RingHom.Finite.of_surjective _ hres) hfin
  · rw [hcomp]
    exact hfu.comp (RingHom.FormallyUnramified.of_surjective hres)

end GlobalTheory.EtaleCompletionCharZero
end

open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_normal_of_unramified : ∀ (D T : Type) [CommRing D] [IsDomain D] [IsLocalRing D] [IsIntegrallyClosed D] [CharZero D] [Algebra.EssFiniteType ℤ D] [CommRing T] [IsLocalRing T] (h : D →+* T), IsNoetherianRing T → IsLocalHom h → h.Flat → (maximalIdeal D).map h = maximalIdeal T → ((residue T).comp h).Finite → ((residue T).comp h).FormallyUnramified → IsDomain (AdicCompletion (maximalIdeal T) T) ∧ IsIntegrallyClosed (AdicCompletion (maximalIdeal T) T) := by
  atlas_forward_decl GlobalTheory.EtaleCompletionCharZero.completion_isDomain_and_isIntegrallyClosed
end

section
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory.LocalChart

theorem localised_base_change_at_prime : ∀ (A D R : Type) [CommRing A] [IsLocalRing A] [CommRing D] [IsLocalRing D] [Algebra A D] [IsLocalHom (algebraMap A D)] [Algebra.EssFiniteType A D] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R], IsEtaleCompletion (algebraMap A R) → ((residue R).comp (algebraMap A R)).FormallyUnramified → ∀ (q : Ideal (D ⊗[A] R)) [q.IsPrime], (∀ d ∈ maximalIdeal D, d ⊗ₜ[A] (1 : R) ∈ q) → IsNoetherianRing (Localization.AtPrime q) ∧ IsLocalHom ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R))) ∧ ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R))).Flat ∧ (maximalIdeal D).map ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R))) = maximalIdeal (Localization.AtPrime q) ∧ ((residue (Localization.AtPrime q)).comp ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R)))).Finite ∧ ((residue (Localization.AtPrime q)).comp ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R)))).FormallyUnramified := by
  intro A D R _ _ _ _ _ _ _ _ _ _ _ hEt hFU q _ hq
  obtain ⟨hflat, hmax, hfin⟩ := hEt
  haveI : Module.Flat A R := RingHom.flat_algebraMap_iff.1 hflat
  haveI : IsNoetherianRing (D ⊗[A] R) :=
    haveI := Algebra.EssFiniteType.isNoetherianRing R (R ⊗[A] D)
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A R D).toRingEquiv
  set J := (maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] D ⊗[A] R)
  have hJ : J ≤ (maximalIdeal D).map (algebraMap D (D ⊗[A] R)) := by
    show (maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] D ⊗[A] R) ≤ _
    rw [← hmax, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    have e : (Algebra.TensorProduct.includeRight : R →ₐ[A] D ⊗[A] R) (algebraMap A R a) = algebraMap D (D ⊗[A] R) (algebraMap A D a) :=
      ((Algebra.TensorProduct.includeRight : R →ₐ[A] D ⊗[A] R).commutes a).trans
        ((Algebra.TensorProduct.includeLeft : D →ₐ[A] D ⊗[A] R).commutes a).symm
    simp only [Ideal.mem_comap]
    rw [e]
    exact Ideal.mem_map_of_mem _ (map_nonunit (algebraMap A D) a ha)
  have hle : (maximalIdeal D).map (algebraMap D (D ⊗[A] R)) ≤ q := by
    rw [Ideal.map_le_iff_le_comap]
    intro d hd
    rw [Ideal.mem_comap, Algebra.TensorProduct.algebraMap_apply]
    simpa using hq d hd
  obtain ⟨hFU1, hFin1⟩ := GlobalTheory.tensor_quot_maximalIdeal_finite_formallyUnramified A D R hfin hFU
  haveI hqm : q.IsMaximal := by
    have hJq : J ≤ q := hJ.trans hle
    haveI : Module.Finite D ((D ⊗[A] R) ⧸ J) := hFin1
    haveI : Module.Finite D ((D ⊗[A] R) ⧸ q) :=
      Module.Finite.of_surjective (Ideal.Quotient.factorₐ D hJq).toLinearMap (Ideal.Quotient.factor_surjective hJq)
    haveI : Algebra.IsIntegral D ((D ⊗[A] R) ⧸ q) := Algebra.IsIntegral.of_finite D _
    have hcomap : (⊥ : Ideal ((D ⊗[A] R) ⧸ q)).comap (algebraMap D ((D ⊗[A] R) ⧸ q)) = maximalIdeal D := by
      refine ((maximalIdeal.isMaximal D).eq_of_le ?_ ?_).symm
      · intro h
        have h1 : (1 : D) ∈ (⊥ : Ideal ((D ⊗[A] R) ⧸ q)).comap (algebraMap D ((D ⊗[A] R) ⧸ q)) := h ▸ Submodule.mem_top
        rw [Ideal.mem_comap, map_one, Ideal.mem_bot] at h1
        exact one_ne_zero h1
      · intro d hd
        rw [Ideal.mem_comap, Ideal.mem_bot, IsScalarTower.algebraMap_apply D (D ⊗[A] R) ((D ⊗[A] R) ⧸ q), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
        exact hle (Ideal.mem_map_of_mem _ hd)
    haveI : (⊥ : Ideal ((D ⊗[A] R) ⧸ q)).IsPrime := Ideal.bot_prime
    have hbot : (⊥ : Ideal ((D ⊗[A] R) ⧸ q)).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := D) _ (hcomap ▸ maximalIdeal.isMaximal D)
    exact Ideal.Quotient.maximal_of_isField q (Ring.isField_iff_maximal_bot.mpr hbot)
  have e1 := GlobalTheory.map_maximalIdeal_localization_eq_of_formallyUnramified_quotient D (D ⊗[A] R) J q hJ hle hFU1 hFin1
  obtain ⟨e2, e3⟩ := GlobalTheory.residue_atMaximal_finite_formallyUnramified D (D ⊗[A] R) J q (hJ.trans hle) hFU1 hFin1
  refine ⟨IsLocalization.isNoetherianRing q.primeCompl _ inferInstance, ?_, ?_, e1, e2, e3⟩
  · refine ((local_hom_TFAE _).out 0 2).2 ?_
    rw [e1]
  · exact RingHom.Flat.comp ((RingHom.flat_algebraMap_iff).2 (Module.Flat.baseChange A D R)) ((RingHom.flat_algebraMap_iff).2 (IsLocalization.flat (Localization.AtPrime q) q.primeCompl))

end GlobalTheory.LocalChart
end

open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_localization_noetherian : ∀ (A D R : Type) [CommRing A] [IsLocalRing A] [CommRing D] [IsLocalRing D] [Algebra A D] [IsLocalHom (algebraMap A D)] [Algebra.EssFiniteType A D] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R], IsEtaleCompletion (algebraMap A R) → ((residue R).comp (algebraMap A R)).FormallyUnramified → ∀ (q : Ideal (D ⊗[A] R)) [q.IsPrime], (∀ d ∈ maximalIdeal D, d ⊗ₜ[A] (1 : R) ∈ q) → IsNoetherianRing (Localization.AtPrime q) ∧ IsLocalHom ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R))) ∧ ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R))).Flat ∧ (maximalIdeal D).map ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R))) = maximalIdeal (Localization.AtPrime q) ∧ ((residue (Localization.AtPrime q)).comp ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R)))).Finite ∧ ((residue (Localization.AtPrime q)).comp ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R)))).FormallyUnramified := by
  atlas_forward_decl GlobalTheory.LocalChart.localised_base_change_at_prime
end

section
namespace GlobalTheory.FractionalParts

def fracs {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (C : Subalgebra A B) :
    Subalgebra A B where
  carrier := {b | ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a}
  mul_mem' := by
    rintro x y ⟨a, ha, s, hs, hu, h⟩ ⟨a', ha', s', hs', hu', h'⟩
    exact ⟨a * a', C.mul_mem ha ha', s * s', C.mul_mem hs hs', hu.mul hu', by
      rw [← h, ← h']; ring⟩
  add_mem' := by
    rintro x y ⟨a, ha, s, hs, hu, h⟩ ⟨a', ha', s', hs', hu', h'⟩
    exact ⟨s' * a + s * a', C.add_mem (C.mul_mem hs' ha) (C.mul_mem hs ha'), s * s',
      C.mul_mem hs hs', hu.mul hu', by rw [← h, ← h']; ring⟩
  algebraMap_mem' r := ⟨algebraMap A B r, C.algebraMap_mem r, 1, C.one_mem, isUnit_one, one_mul _⟩

theorem exists_finiteType_subalgebra_valuation_le_one (A B k : Type) [CommRing A] [CommRing B]
    [IsLocalRing B] [Algebra A B] [Algebra.EssFiniteType A B] [Field k] (φ : B →+* k)
    (V : ValuationSubring k) (hker : RingHom.ker φ = IsLocalRing.maximalIdeal B)
    (hA : ∀ a : A, V.valuation (φ (algebraMap A B a)) ≤ 1) :
    ∃ C : Subalgebra A B, Algebra.FiniteType A C ∧ (∀ c ∈ C, V.valuation (φ c) ≤ 1) ∧
      ∀ b : B, ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a := by
  classical
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff A B).mp inferInstance
  have key : ∀ x : B, ∃ y : B, φ y ∈ V ∧ (y = x ∨ y * x = 1) := by
    intro x
    by_cases hx : φ x ∈ V
    · exact ⟨x, hx, Or.inl rfl⟩
    · have hne : φ x ≠ 0 := fun h => hx (h ▸ V.zero_mem)
      have hu : IsUnit x := by
        by_contra hnu
        have : x ∈ RingHom.ker φ := by
          rw [hker]; exact (IsLocalRing.mem_maximalIdeal x).mpr hnu
        exact hne this
      obtain ⟨y, hy⟩ := hu.exists_left_inv
      refine ⟨y, ?_, Or.inr hy⟩
      have h1 : φ y * φ x = 1 := by rw [← map_mul, hy, map_one]
      rw [eq_inv_of_mul_eq_one_left h1]
      exact (V.mem_or_inv_mem (φ x)).resolve_left hx
  choose f hfV hf using key
  let C : Subalgebra A B := Algebra.adjoin A ((σ.image f : Finset B) : Set B)
  have hfC : ∀ x ∈ σ, f x ∈ C := fun x hx =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem f hx))
  refine ⟨C, ?_, ?_, ?_⟩
  · exact (Subalgebra.fg_iff_finiteType C).mp (Subalgebra.fg_adjoin_finset _)
  · intro c hc
    rw [ValuationSubring.valuation_le_one_iff]
    induction hc using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact hfV z
    | algebraMap r => exact (V.valuation_le_one_iff _).mp (hA r)
    | add x y _ _ hx hy => rw [map_add]; exact V.add_mem _ _ hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact V.mul_mem _ _ hx hy
  · have hle : Algebra.adjoin A (σ : Set B) ≤ fracs C := by
      refine Algebra.adjoin_le ?_
      intro x hx
      have hx' := hfC x (Finset.mem_coe.mp hx)
      rcases hf x with h | h
      · exact ⟨x, h ▸ hx', 1, C.one_mem, isUnit_one, one_mul _⟩
      · exact ⟨1, C.one_mem, f x, hx', IsUnit.of_mul_eq_one _ h, h⟩
    intro b
    obtain ⟨t, ht, htu, hbt⟩ := hσ b
    obtain ⟨a1, ha1, s1, hs1, hu1, h1⟩ := hle ht
    obtain ⟨a2, ha2, s2, hs2, hu2, h2⟩ := hle hbt
    refine ⟨s1 * a2, C.mul_mem hs1 ha2, s2 * a1, C.mul_mem hs2 ha1,
      hu2.mul (h1 ▸ hu1.mul htu), ?_⟩
    rw [← h1, ← h2]; ring

end GlobalTheory.FractionalParts
end

section
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory

theorem valuativeChart_exists_fg_subalgebra :
    ∀ (A B k : Type) [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
      [Algebra.EssFiniteType A B] [Field k] (φ : B →+* k) (V : ValuationSubring k),
      RingHom.ker φ = maximalIdeal B → (∀ a : A, V.valuation (φ (algebraMap A B a)) ≤ 1) →
      ∃ C : Subalgebra A B, Algebra.FiniteType A C ∧ (∀ c ∈ C, V.valuation (φ c) ≤ 1) ∧
        ∀ b : B, ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a := by
  first
  | exact @_root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one
  | exact _root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one
  | (apply _root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one ..)

end GlobalTheory
end

open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_type_valuation_center : ∀ (A B k : Type) [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [Algebra.EssFiniteType A B] [Field k] (φ : B →+* k) (V : ValuationSubring k), RingHom.ker φ = maximalIdeal B → (∀ a : A, V.valuation (φ (algebraMap A B a)) ≤ 1) → ∃ C : Subalgebra A B, Algebra.FiniteType A C ∧ (∀ c ∈ C, V.valuation (φ c) ≤ 1) ∧ ∀ b : B, ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a := by
  atlas_forward_decl GlobalTheory.valuativeChart_exists_fg_subalgebra
end

section
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory

theorem isFractionRing_of_forall_eq_div {B : Type} [CommRing B] [IsDomain B]
    (K : Type) [Field K] [Algebra B K] [IsFractionRing B K]
    (R : Type) [CommRing R] [Algebra R B] [Algebra R K]
    [IsScalarTower R B K] (hinj : Function.Injective (algebraMap R B))
    (h : ∀ b : B, ∃ a s : R, s ≠ 0 ∧ algebraMap R B s * b = algebraMap R B a) :
    IsFractionRing R K := by
  have hcomp : algebraMap R K = (algebraMap B K).comp (algebraMap R B) :=
    IsScalarTower.algebraMap_eq R B K
  have hinjK : Function.Injective (algebraMap R K) := by
    rw [hcomp]; exact (IsFractionRing.injective B K).comp hinj
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr hinjK
  refine IsFractionRing.of_field R K (fun z => ?_)
  obtain ⟨b₁, b₂, -, rfl⟩ := IsFractionRing.div_surjective (A := B) z
  obtain ⟨a₁, s₁, hs₁, e₁⟩ := h b₁
  obtain ⟨a₂, s₂, hs₂, e₂⟩ := h b₂
  refine ⟨a₁ * s₂, s₁ * a₂, ?_⟩
  have n₁ : algebraMap B K (algebraMap R B s₁) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective B K), map_ne_zero_iff _ hinj]; exact hs₁
  have n₂ : algebraMap B K (algebraMap R B s₂) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective B K), map_ne_zero_iff _ hinj]; exact hs₂
  simp only [hcomp, RingHom.comp_apply, map_mul, ← e₁, ← e₂]
  set u := algebraMap B K (algebraMap R B s₁)
  set v := algebraMap B K (algebraMap R B s₂)
  rw [show u * algebraMap B K b₁ * v = (u * v) * algebraMap B K b₁ by ring,
    show u * (v * algebraMap B K b₂) = (u * v) * algebraMap B K b₂ by ring,
    mul_div_mul_left _ _ (mul_ne_zero n₁ n₂)]

theorem exists_finiteType_isIntegrallyClosed_integral_over :
    ∀ (A B : Type) [CommRing A] [Algebra.EssFiniteType ℤ A] [CommRing B] [IsDomain B]
      [IsIntegrallyClosed B] [Algebra A B] (C : Subalgebra A B), Algebra.FiniteType A C →
      (∀ b : B, ∃ a ∈ C, ∃ s ∈ C, s ≠ 0 ∧ s * b = a) →
      ∃ C' : Subalgebra A B, C ≤ C' ∧ Algebra.FiniteType A C' ∧ IsIntegrallyClosed C' ∧
        ∀ x ∈ C', IsIntegral C x := by
  intro A B _ _ _ _ _ _ C hC hfrac
  haveI : Algebra.FiniteType A C := hC
  haveI : Algebra.EssFiniteType ℤ C := Algebra.EssFiniteType.comp ℤ A C
  haveI : IsNoetherianRing C := Algebra.EssFiniteType.isNoetherianRing ℤ C
  set K := FractionRing B
  set D : Subalgebra C B := integralClosure C B with hD
  haveI hCK : IsFractionRing C K := by
    refine isFractionRing_of_forall_eq_div (B := B) K C Subtype.val_injective
      (fun b => ?_)
    obtain ⟨a, ha, s, hs, hne, e⟩ := hfrac b
    refine ⟨⟨a, ha⟩, ⟨s, hs⟩, ?_, e⟩
    intro h0; apply hne; simpa using congrArg Subtype.val h0
  haveI hDK : IsFractionRing D K := by
    refine isFractionRing_of_forall_eq_div (B := B) K D Subtype.val_injective
      (fun b => ?_)
    obtain ⟨a, ha, s, hs, hne, e⟩ := hfrac b
    refine ⟨⟨a, D.algebraMap_mem ⟨a, ha⟩⟩, ⟨s, D.algebraMap_mem ⟨s, hs⟩⟩, ?_, e⟩
    intro h0; apply hne; simpa using congrArg Subtype.val h0
  have hinjBK : Function.Injective (IsScalarTower.toAlgHom C B K) :=
    IsFractionRing.injective B K

  have hfinK : Module.Finite C (integralClosure C K) := by
    haveI := finite_integralClosure_of_essFiniteType_int C
    let e : FractionRing C ≃ₐ[C] K := IsLocalization.algEquiv (nonZeroDivisors C) _ _
    exact Module.Finite.equiv e.mapIntegralClosure.toLinearEquiv
  have hfinD : Module.Finite C D := by
    let f : D →ₗ[C] integralClosure C K :=
      { toFun := fun x => ⟨algebraMap B K x, x.2.map (IsScalarTower.toAlgHom C B K)⟩
        map_add' := fun x y => by ext; simp
        map_smul' := fun c x => by
          ext; simp [Algebra.smul_def]; left; exact (IsScalarTower.algebraMap_apply C B K c).symm }
    refine Module.Finite.of_injective f (fun x y hxy => ?_)
    apply Subtype.ext; apply IsFractionRing.injective B K
    exact congrArg Subtype.val hxy
  have hftD : Algebra.FiniteType A D := Algebra.FiniteType.trans hC inferInstance
  have hicD : IsIntegrallyClosed D := by
    refine (isIntegrallyClosed_iff K).mpr (fun {x} hx => ?_)
    have hxB : IsIntegral B x := hx.tower_top
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxB
    have hxC : IsIntegral C (algebraMap B K y) := isIntegral_trans _ hx
    have hyC : IsIntegral C y := (isIntegral_algHom_iff _ hinjBK).mp hxC
    exact ⟨⟨y, hyC⟩, rfl⟩
  refine ⟨D.restrictScalars A, fun x hx => ?_, hftD, hicD, fun x hx => hx⟩
  exact isIntegral_algebraMap (R := C) (A := B) (x := ⟨x, hx⟩)

end GlobalTheory
end

open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_finite_type_over : ∀ (A B : Type) [CommRing A] [Algebra.EssFiniteType ℤ A] [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] (C : Subalgebra A B), Algebra.FiniteType A C → (∀ b : B, ∃ a ∈ C, ∃ s ∈ C, s ≠ 0 ∧ s * b = a) → ∃ C' : Subalgebra A B, C ≤ C' ∧ Algebra.FiniteType A C' ∧ IsIntegrallyClosed C' ∧ ∀ x ∈ C', IsIntegral C x := by
  atlas_forward_decl GlobalTheory.exists_finiteType_isIntegrallyClosed_integral_over
end

section
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory

theorem valuativeChart_localise :
    ∀ (A B k : Type) [CommRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B] [Field k]
      (φ : B →+* k) (V : ValuationSubring k) (C : Subalgebra A B), RingHom.ker φ = maximalIdeal B →
      Algebra.FiniteType A C → IsIntegrallyClosed C → (∀ c ∈ C, V.valuation (φ c) ≤ 1) →
      (∀ b : B, ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a) →
      ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsLocalRing D) (_ : Algebra A D) (ι : D →ₐ[A] B),
        IsIntegrallyClosed D ∧ Algebra.EssFiniteType A D ∧ Function.Injective ι ∧
        (∀ d, V.valuation (φ (ι d)) ≤ 1) ∧ (∀ d ∈ maximalIdeal D, V.valuation (φ (ι d)) < 1) ∧
        ∀ b : B, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a := by
  intro A B k _ _ _ _ _ _ φ V C hker hft hic hle hfrac
  let ψ : C →+* V := (φ.comp C.val.toRingHom).codRestrict V
    (fun c => (V.valuation_le_one_iff _).1 (hle c c.2))
  let p : Ideal C := (maximalIdeal V).comap ψ
  have hmem : ∀ c : C, c ∈ p ↔ V.valuation (φ c) < 1 := by
    intro c
    exact V.valuation_lt_one_iff (ψ c)
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let D := Localization.AtPrime p
  haveI : IsDomain D := IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors
  have hval1 : ∀ y : p.primeCompl, V.valuation (φ (y : C)) = 1 := by
    intro y
    have h1 := hle (y : C) (y : C).2
    have h2 : ¬ V.valuation (φ (y : C)) < 1 := fun h => y.2 ((hmem _).2 h)
    exact le_antisymm h1 (not_lt.1 h2)
  have hunit : ∀ y : p.primeCompl, IsUnit (C.val (y : C)) := by
    intro y
    by_contra hnu
    have hm : ((y : C) : B) ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).2 hnu
    rw [← hker, RingHom.mem_ker] at hm
    have := hval1 y
    rw [hm, map_zero] at this
    exact zero_ne_one this
  let ι : D →ₐ[A] B := IsLocalization.liftAlgHom (M := p.primeCompl) (S := D) (f := C.val) hunit
  have hιalg : ∀ c : C, ι (algebraMap C D c) = c := by
    intro c
    simp [ι, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  have hrep : ∀ d : D, ∃ c : C, ∃ s : p.primeCompl, ((s : C) : B) * ι d = c ∧
      d * algebraMap C D s = algebraMap C D c := by
    intro d
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl d
    refine ⟨c, s, ?_, IsLocalization.mk'_spec _ _ _⟩
    have := (IsLocalization.lift_mk'_spec (M := p.primeCompl) (S := D) (hg := hunit) c
      (IsLocalization.lift hunit (IsLocalization.mk' D c s)) s).1 rfl
    simpa [ι, IsLocalization.liftAlgHom_apply] using this.symm
  have hvald : ∀ d : D, ∃ c : C, V.valuation (φ (ι d)) = V.valuation (φ c) ∧
      (d ∈ maximalIdeal D → c ∈ p) := by
    intro d
    obtain ⟨c, s, h1, h2⟩ := hrep d
    refine ⟨c, ?_, ?_⟩
    · rw [← h1, map_mul, Valuation.map_mul, hval1 s, one_mul]
    · intro hd
      have : algebraMap C D c ∈ maximalIdeal D := by
        rw [← h2]; exact Ideal.mul_mem_right _ _ hd
      have h3 : c ∈ (maximalIdeal D).under C := Ideal.mem_comap.2 this
      rwa [IsLocalization.AtPrime.comap_maximalIdeal D p] at h3
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, ι, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isIntegrallyClosed_of_isLocalization D p.primeCompl p.primeCompl_le_nonZeroDivisors
  · infer_instance
  · show Function.Injective (IsLocalization.lift hunit : D → B)
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      have := congrArg (IsLocalization.lift (S := D) hunit) h
      simpa [IsLocalization.lift_eq] using this
    · intro h
      rw [Subtype.ext (show (x : B) = y from h)]
  · intro d
    obtain ⟨c, hc, -⟩ := hvald d
    rw [hc]; exact hle c c.2
  · intro d hd
    obtain ⟨c, hc, hp⟩ := hvald d
    rw [hc]; exact (hmem c).1 (hp hd)
  · intro b
    obtain ⟨a, ha, s, hs, hu, hsb⟩ := hfrac b
    refine ⟨algebraMap C D ⟨a, ha⟩, algebraMap C D ⟨s, hs⟩, ?_, ?_⟩
    · rw [hιalg]; exact hu
    · rw [hιalg, hιalg]; exact hsb

end GlobalTheory
end

open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_domain_valuation_center : ∀ (A B k : Type) [CommRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B] [Field k] (φ : B →+* k) (V : ValuationSubring k) (C : Subalgebra A B), RingHom.ker φ = maximalIdeal B → Algebra.FiniteType A C → IsIntegrallyClosed C → (∀ c ∈ C, V.valuation (φ c) ≤ 1) → (∀ b : B, ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a) → ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsLocalRing D) (_ : Algebra A D) (ι : D →ₐ[A] B), IsIntegrallyClosed D ∧ Algebra.EssFiniteType A D ∧ Function.Injective ι ∧ (∀ d, V.valuation (φ (ι d)) ≤ 1) ∧ (∀ d ∈ maximalIdeal D, V.valuation (φ (ι d)) < 1) ∧ ∀ b : B, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a := by
  atlas_forward_decl GlobalTheory.valuativeChart_localise
end

section
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory

theorem valuation_le_one_of_isIntegral_subalgebra : ∀ (A B k : Type) [CommRing A] [CommRing B] [Algebra A B] [Field k] (φ : B →+* k) (V : ValuationSubring k) (C : Subalgebra A B), (∀ c ∈ C, V.valuation (φ c) ≤ 1) → ∀ x : B, IsIntegral C x → V.valuation (φ x) ≤ 1 := by
  intro A B k _ _ _ _ φ V C hC x hx
  let ψ : C →+* V := (φ.comp C.val.toRingHom).codRestrict V.toSubring (fun c => (V.valuation_le_one_iff _).mp (hC c c.2))
  have h := IsIntegral.map_of_comp_eq ψ φ (by ext c; rfl) hx
  have h2 : φ x ∈ V := by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
    rw [← hy]; exact y.2
  exact (V.valuation_le_one_iff _).mpr h2

theorem exists_normal_localization_chart_centred : ∀ (A B k : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B] [Algebra A B] [Algebra.EssFiniteType A B] [Field k] (φ : B →+* k) (V : ValuationSubring k), RingHom.ker φ = maximalIdeal B → (∀ a : A, V.valuation (φ (algebraMap A B a)) ≤ 1) → (∀ a ∈ maximalIdeal A, V.valuation (φ (algebraMap A B a)) < 1) → ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsLocalRing D) (_ : Algebra A D) (ι : D →ₐ[A] B), IsIntegrallyClosed D ∧ Algebra.EssFiniteType A D ∧ Function.Injective ι ∧ (∀ d, V.valuation (φ (ι d)) ≤ 1) ∧ (∀ d ∈ maximalIdeal D, V.valuation (φ (ι d)) < 1) ∧ ∀ b : B, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a := by
  intro A B k _ _ _ _ _ _ _ _ _ _ φ V hker hA _
  obtain ⟨C, hCft, hCv, hCfrac⟩ := GlobalTheory.T.exists_finite_type_valuation_center A B k φ V hker hA
  obtain ⟨C', hle, hft', hic', hint⟩ := GlobalTheory.T.exists_normal_finite_type_over A B C hCft (fun b => by
    obtain ⟨a, ha, s, hs, hu, he⟩ := hCfrac b
    exact ⟨a, ha, s, hs, hu.ne_zero, he⟩)
  have hv' : ∀ c ∈ C', V.valuation (φ c) ≤ 1 := fun c hc =>
    valuation_le_one_of_isIntegral_subalgebra A B k φ V C hCv c (hint c hc)
  exact GlobalTheory.T.exists_local_domain_valuation_center A B k φ V C' hker hft' hic' hv' (fun b => by
    obtain ⟨a, ha, s, hs, hu, he⟩ := hCfrac b
    exact ⟨a, hle ha, s, hle hs, hu, he⟩)

end GlobalTheory
end

open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_domain_valuation_dominated : ∀ (A B k : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B] [Algebra A B] [Algebra.EssFiniteType A B] [Field k] (φ : B →+* k) (V : ValuationSubring k), RingHom.ker φ = maximalIdeal B → (∀ a : A, V.valuation (φ (algebraMap A B a)) ≤ 1) → (∀ a ∈ maximalIdeal A, V.valuation (φ (algebraMap A B a)) < 1) → ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsLocalRing D) (_ : Algebra A D) (ι : D →ₐ[A] B), IsIntegrallyClosed D ∧ Algebra.EssFiniteType A D ∧ Function.Injective ι ∧ (∀ d, V.valuation (φ (ι d)) ≤ 1) ∧ (∀ d ∈ maximalIdeal D, V.valuation (φ (ι d)) < 1) ∧ ∀ b : B, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a := by
  atlas_forward_decl GlobalTheory.exists_normal_localization_chart_centred
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory.BaseChangeLoc

theorem localization_atPrime_tensor (A C R : Type) [CommRing A] [CommRing C] [CommRing R] [Algebra A C]
    [Algebra A R] (Q : Ideal (C ⊗[A] R)) [Q.IsPrime] :
    ∃ (Q' : Ideal (Localization.AtPrime (Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R)) ⊗[A] R))
      (_ : Q'.IsPrime),
      Q'.comap (Algebra.TensorProduct.includeLeft :
        Localization.AtPrime (Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R)) →ₐ[A] _ ⊗[A] R) =
          maximalIdeal _ ∧
      (IsDomain (Localization.AtPrime Q') → IsIntegrallyClosed (Localization.AtPrime Q') →
        IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) := by
  set P : Ideal C := Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R) with hP
  let B := Localization.AtPrime P
  let φ : C ⊗[A] R →ₐ[A] B ⊗[A] R :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A C B) (AlgHom.id A R)
  letI : Algebra (C ⊗[A] R) (B ⊗[A] R) := φ.toRingHom.toAlgebra
  have hφ : ∀ x, algebraMap (C ⊗[A] R) (B ⊗[A] R) x = φ x := fun _ => rfl
  haveI : IsScalarTower C (C ⊗[A] R) (B ⊗[A] R) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    rw [hφ]
    simp [φ, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have H : (algebraMap (C ⊗[A] R) (B ⊗[A] R)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
    ext r
    simp [hφ, φ]
  let M : Submonoid (C ⊗[A] R) := Algebra.algebraMapSubmonoid (C ⊗[A] R) P.primeCompl
  haveI hL : IsLocalization M (B ⊗[A] R) :=
    IsLocalization.tensorProduct_tensorProduct A R P.primeCompl B H
  have hdisj : Disjoint (M : Set (C ⊗[A] R)) (Q : Set (C ⊗[A] R)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨c, hc, rfl⟩ h
    exact hc h
  have hQ' := IsLocalization.isPrime_of_isPrime_disjoint M (B ⊗[A] R) Q inferInstance hdisj
  have hc := IsLocalization.comap_map_of_isPrime_disjoint M (B ⊗[A] R) (inferInstance : Q.IsPrime) hdisj
  refine ⟨Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R)), hQ', ?_, ?_⟩
  · haveI := hQ'
    have hne : (Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R))).comap
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) ≠ ⊤ :=
      Ideal.IsPrime.ne_top inferInstance
    symm
    refine (IsLocalRing.maximalIdeal.isMaximal B).eq_of_le hne ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro c hcP
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e1 : (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) (algebraMap C B c) =
        algebraMap (C ⊗[A] R) (B ⊗[A] R) ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R) c) := by
      simp [hφ, φ]
    rw [e1]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mp hcP)
  · intro h3 h4
    have h1 := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime (Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R)))) (Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R)))
    have h2 : IsLocalization Q.primeCompl
        (Localization.AtPrime (Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R)))) := by
      convert h1 using 1
      ext x
      simp [Ideal.primeCompl, hc]
    let e : Localization.AtPrime (Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R))) ≃ₐ[C ⊗[A] R]
        Localization.AtPrime Q :=
      IsLocalization.algEquiv Q.primeCompl _ _
    exact ⟨e.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

end GlobalTheory.BaseChangeLoc
end

open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_prime_contraction_maximal : ∀ (A C R : Type) [CommRing A] [CommRing C] [CommRing R] [Algebra A C] [Algebra A R] (Q : Ideal (C ⊗[A] R)) [Q.IsPrime], ∃ (Q' : Ideal (Localization.AtPrime (Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R)) ⊗[A] R)) (_ : Q'.IsPrime), Q'.comap (Algebra.TensorProduct.includeLeft : Localization.AtPrime (Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R)) →ₐ[A] _ ⊗[A] R) = maximalIdeal _ ∧ (IsDomain (Localization.AtPrime Q') → IsIntegrallyClosed (Localization.AtPrime Q') → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) := by
  atlas_forward_decl GlobalTheory.BaseChangeLoc.localization_atPrime_tensor
end

section
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory

theorem normal_atPrime_tensor_of_chart_localization : ∀ (A B D R : Type) [CommRing A] [CommRing B] [CommRing D] [CommRing R] [Algebra A B] [Algebra A D] [Algebra A R] (ι : D →ₐ[A] B), Function.Injective ι → (∀ b, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a) → ∀ (Q : Ideal (B ⊗[A] R)) [Q.IsPrime] (q : Ideal (D ⊗[A] R)) [q.IsPrime], Q.comap (Algebra.TensorProduct.map ι (AlgHom.id A R)) ≤ q → IsDomain (Localization.AtPrime q) → IsIntegrallyClosed (Localization.AtPrime q) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  intro A B D R _ _ _ _ _ _ _ ι hinj hsurj Q _ q _ hle hdom hic
  letI : Algebra D B := ι.toRingHom.toAlgebra
  haveI : IsScalarTower A D B := .of_algebraMap_eq fun a ↦ (ι.commutes a).symm
  let M : Submonoid D := (IsUnit.submonoid B).comap ι.toRingHom
  haveI : IsLocalization M B :=
    { map_units := fun y ↦ y.2
      surj := fun b ↦ by
        obtain ⟨a, s, hs, h⟩ := hsurj b
        exact ⟨(a, ⟨s, hs⟩), by rw [mul_comm]; exact h⟩
      exists_of_eq := fun {x y} h ↦ ⟨1, by rw [hinj h]⟩ }
  let φ := Algebra.TensorProduct.map ι (AlgHom.id A R)
  letI : Algebra (D ⊗[A] R) (B ⊗[A] R) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower D (D ⊗[A] R) (B ⊗[A] R) := .of_algebraMap_eq fun x ↦ by
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply, φ]
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (D ⊗[A] R) M) (B ⊗[A] R) :=
    IsLocalization.tensorProduct_tensorProduct A R M B (by
      ext x; simp [RingHom.algebraMap_toAlgebra, φ])
  set QD := Q.comap (algebraMap (D ⊗[A] R) (B ⊗[A] R)) with hQD
  haveI : QD.IsPrime := Ideal.comap_isPrime _ _
  haveI hL : IsLocalization QD.primeCompl (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid (D ⊗[A] R) M) (Localization.AtPrime Q) Q
  have hle' : q.primeCompl ≤ QD.primeCompl := fun x hx hx' ↦ hx (hle hx')
  letI : Algebra (Localization.AtPrime q) (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ q.primeCompl QD.primeCompl hle'
  haveI : IsScalarTower (D ⊗[A] R) (Localization.AtPrime q) (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ q.primeCompl QD.primeCompl hle'
  haveI : IsLocalization (QD.primeCompl.map (algebraMap (D ⊗[A] R) (Localization.AtPrime q)))
      (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ q.primeCompl QD.primeCompl hle'
  have hN : QD.primeCompl.map (algebraMap (D ⊗[A] R) (Localization.AtPrime q)) ≤
      nonZeroDivisors (Localization.AtPrime q) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    have hu : IsUnit (algebraMap (D ⊗[A] R) (Localization.AtPrime Q) c) :=
      IsLocalization.map_units (Localization.AtPrime Q) (⟨c, hc⟩ : QD.primeCompl)
    rw [IsScalarTower.algebraMap_apply (D ⊗[A] R) (Localization.AtPrime q)
      (Localization.AtPrime Q), h0, map_zero] at hu
    exact not_isUnit_zero hu
  exact ⟨IsLocalization.isDomain_of_le_nonZeroDivisors _ hN,
    isIntegrallyClosed_of_isLocalization _ _ hN⟩

end GlobalTheory
end

open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_localization_normal_domain : ∀ (A B D R : Type) [CommRing A] [CommRing B] [CommRing D] [CommRing R] [Algebra A B] [Algebra A D] [Algebra A R] (ι : D →ₐ[A] B), Function.Injective ι → (∀ b, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a) → ∀ (Q : Ideal (B ⊗[A] R)) [Q.IsPrime] (q : Ideal (D ⊗[A] R)) [q.IsPrime], Q.comap (Algebra.TensorProduct.map ι (AlgHom.id A R)) ≤ q → IsDomain (Localization.AtPrime q) → IsIntegrallyClosed (Localization.AtPrime q) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  atlas_forward_decl GlobalTheory.normal_atPrime_tensor_of_chart_localization
end

section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.TensorNormal.localization_tensor_normal_of_charZero : ∀ (A C R : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing C] [Algebra A C] [Algebra.EssFiniteType A C] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R], (∀ (P : Ideal C) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P) ∧ CharZero (Localization.AtPrime P)) → IsEtaleCompletion (algebraMap A R) → ((residue R).comp (algebraMap A R)).FormallyUnramified → ∀ (Q : Ideal (TensorProduct A C R)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) ∧ IsNoetherianRing (Localization.AtPrime Q) := by
  intro A C R _ _ _ _ _ _ _ _ _ _ hC hEt hFU Q _
  have hnoeth : IsNoetherianRing (Localization.AtPrime Q) := by
    haveI : IsNoetherianRing (R ⊗[A] C) := Algebra.EssFiniteType.isNoetherianRing R (R ⊗[A] C)
    haveI : IsNoetherianRing (C ⊗[A] R) :=
      isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A R C).toRingEquiv
    infer_instance
  suffices h : IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) from
    ⟨h.1, h.2, hnoeth⟩
  obtain ⟨Q', _, hQ'm, htr⟩ := GlobalTheory.T.tensor_prime_contraction_maximal A C R Q
  set P := Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R) with hP
  set B := Localization.AtPrime P
  obtain ⟨hBd, hBi, hBc⟩ := hC P
  haveI := hBd; haveI := hBi; haveI := hBc
  haveI : Algebra.EssFiniteType C B := .of_isLocalization B P.primeCompl
  haveI : Algebra.EssFiniteType A B := .comp A C B
  set W' := Localization.AtPrime Q'
  let k := ResidueField W'
  let φ : B →+* k := (residue W').comp ((algebraMap (B ⊗[A] R) W').comp
    (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R).toRingHom)
  let ρ : R →+* k := (residue W').comp ((algebraMap (B ⊗[A] R) W').comp
    (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).toRingHom)
  obtain ⟨V, hV, hVloc⟩ := IsLocalRing.exists_factor_valuationRing ρ
  have hker : RingHom.ker φ = maximalIdeal B := by
    ext b
    rw [RingHom.mem_ker, ← hQ'm, Ideal.mem_comap]
    change residue W' (algebraMap _ W' ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) b)) = 0 ↔ _
    rw [residue_eq_zero_iff]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff W' Q' _
  have hφρ : ∀ a : A, φ (algebraMap A B a) = ρ (algebraMap A R a) := fun a => by
    simp only [φ, ρ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  have ha1 : ∀ a : A, V.valuation (φ (algebraMap A B a)) ≤ 1 := fun a => by
    rw [hφρ, ValuationSubring.valuation_le_one_iff]; exact hV _
  have ha2 : ∀ a ∈ maximalIdeal A, V.valuation (φ (algebraMap A B a)) < 1 := fun a ha => by
    have hR : algebraMap A R a ∈ maximalIdeal R := hEt.2.1 ▸ Ideal.mem_map_of_mem _ ha
    have hm : ρ.codRestrict V.toSubring hV (algebraMap A R a) ∈ maximalIdeal V := fun hu =>
      hR (IsUnit.of_map (ρ.codRestrict V.toSubring hV) _ hu)
    rw [hφρ]
    exact (ValuationSubring.valuation_lt_one_iff V _).1 hm
  obtain ⟨D, _, _, _, _, ι, hDi, hDe, hinj, hv1, hvm, hsurj⟩ := GlobalTheory.T.exists_local_domain_valuation_dominated A B k φ V hker ha1 ha2
  haveI := hDi; haveI := hDe
  haveI : CharZero D := ⟨fun m n h => Nat.cast_injective (R := B) (by simpa using congrArg ι h)⟩
  haveI : Algebra.EssFiniteType ℤ D := .comp ℤ A D
  have hunit1 : ∀ d : D, IsUnit d → V.valuation (φ (ι d)) = 1 := fun d hd => by
    obtain ⟨u, rfl⟩ := hd
    have h1 := hv1 u
    have h2 := hv1 ↑u⁻¹
    have h3 : V.valuation (φ (ι u)) * V.valuation (φ (ι ↑u⁻¹)) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, map_one]
    exact le_antisymm h1 (by
      by_contra hlt
      push_neg at hlt
      have := mul_lt_one_of_lt_of_le hlt h2
      rw [h3] at this
      exact lt_irrefl _ this)
  haveI : IsLocalHom (algebraMap A D) := ⟨fun a ha => by
    by_contra hna
    have hv := hunit1 _ ha
    rw [AlgHom.commutes] at hv
    exact (ha2 a ((mem_maximalIdeal a).2 hna)).ne hv⟩
  let ψ : D ⊗[A] R →ₐ[A] W' := (IsScalarTower.toAlgHom A (B ⊗[A] R) W').comp
    (Algebra.TensorProduct.map ι (AlgHom.id A R))
  let θ : D ⊗[A] R →+* k := (residue W').comp ψ.toRingHom
  have hθt : ∀ (d : D) (r : R), θ (d ⊗ₜ r) = φ (ι d) * ρ r := fun d r => by
    simp only [θ, φ, ρ, ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom',
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hθt1 : ∀ d : D, θ (d ⊗ₜ[A] (1 : R)) = φ (ι d) := fun d => by
    simp only [θ, φ, ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom',
      Algebra.TensorProduct.includeLeft_apply]
  have hθ0 : ∀ x, θ x = residue W' (algebraMap (B ⊗[A] R) W' (Algebra.TensorProduct.map ι (AlgHom.id A R) x)) :=
    fun x => rfl
  clear_value θ
  have hθV : ∀ x, θ x ∈ V := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simpa using V.zero_mem
    | tmul d r => rw [hθt]; exact V.mul_mem _ _ ((ValuationSubring.valuation_le_one_iff V _).1 (hv1 d)) (hV r)
    | add x y hx hy => rw [map_add]; exact V.add_mem _ _ hx hy
  let θV : D ⊗[A] R →+* V := θ.codRestrict V.toSubring hθV
  let q : Ideal (D ⊗[A] R) := (maximalIdeal V).comap θV
  have hmq : ∀ d ∈ maximalIdeal D, d ⊗ₜ[A] (1 : R) ∈ q := by
    intro d hd
    rw [Ideal.mem_comap]
    refine (ValuationSubring.valuation_lt_one_iff V _).2 ?_
    have e2 := hθt1 d
    have e : ((θV (d ⊗ₜ[A] (1 : R)) : V) : k) = θ (d ⊗ₜ[A] (1 : R)) := rfl
    exact (congrArg V.valuation (e.trans e2)).trans_lt (hvm d hd)
  have hQq : Q'.comap (Algebra.TensorProduct.map ι (AlgHom.id A R)) ≤ q := by
    intro x hx
    have h0 : θ x = 0 := by
      rw [hθ0, residue_eq_zero_iff]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff W' Q' _).2 hx
    show θV x ∈ maximalIdeal V
    have : θV x = 0 := Subtype.ext h0
    rw [this]; exact zero_mem _
  obtain ⟨hTn, hTl, hTf, hTm, hTfin, hTfu⟩ := GlobalTheory.T.tensor_localization_noetherian A D R hEt hFU q hmq
  obtain ⟨c1, c2⟩ := GlobalTheory.T.completion_normal_of_unramified D (Localization.AtPrime q) _ hTn hTl hTf hTm hTfin hTfu
  haveI := hTn
  obtain ⟨t1, t2⟩ := GlobalTheory.T.domain_integrally_closed_of_completion _ c1 c2
  obtain ⟨w1, w2⟩ := GlobalTheory.T.tensor_localization_normal_domain A B D R ι hinj hsurj Q' q hQq t1 t2
  exact htr w1 w2
end

section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.TorRef TensorProduct

namespace GlobalTheory.NormalBaseChange

theorem exists_etale_of_isEtaleCompletion (A R : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] [IsNoetherianRing A] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (het : IsEtaleCompletion (algebraMap A R)) (hfu : ((residue R).comp (algebraMap A R)).FormallyUnramified) :
    ∃ g : AdicCompletion (maximalIdeal A) A →+* R, g.comp (algebraMap A _) = algebraMap A R ∧
      @Algebra.Etale _ R _ _ g.toAlgebra := by
  obtain ⟨hflat, hmap, hfin⟩ := het
  set h := algebraMap A R with hh
  let D := AdicCompletion (maximalIdeal A) A
  haveI : IsNoetherianRing D := AdicNoeth.isNoetherianRing_adicCompletion A _
  haveI : IsAdicComplete ((maximalIdeal A).map h) R := by rw [hmap]; infer_instance
  obtain ⟨g, hg⟩ := exists_adicCompletion_ringHom_extend (maximalIdeal A) h
  letI : Algebra D R := g.toAlgebra
  have hgA : ∀ a, g (algebraMap A D a) = h a := fun a => RingHom.congr_fun hg a
  have hmA : (maximalIdeal D).map (algebraMap D R) = maximalIdeal R := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map]
    change (maximalIdeal A).map (g.comp _) = _
    rw [hg, hmap]
  haveI : IsLocalHom (algebraMap D R) := ((local_hom_TFAE _).out 0 2).mpr hmA.le
  have hres : ((residue R).comp g).Finite :=
    RingHom.Finite.of_comp_finite (f := algebraMap A D) (by rw [RingHom.comp_assoc, hg]; exact hfin)
  haveI : Module.Finite D (R ⧸ (maximalIdeal D).map (algebraMap D R)) := by
    rw [← RingHom.finite_algebraMap]
    show ((Ideal.Quotient.mk _).comp (algebraMap D R)).Finite
    rw [hmA]
    exact hres
  haveI : IsHausdorff ((maximalIdeal D).map (algebraMap D R)) R := by rw [hmA]; infer_instance
  haveI : Module.Finite D R := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal D)
  haveI : Module.Flat D R := by
    refine LocalFlat.flat_of_relationsLift R (I := maximalIdeal D)
      (hmA.le.trans (maximalIdeal_le_jacobson _)) fun n => ?_
    haveI : Module.Flat A R := RingHom.flat_algebraMap_iff.mp hflat
    have fg := (maximalIdeal A).fg_of_isNoetherianRing
    have hkerA : ∀ x : D, AdicCompletion.evalₐ (maximalIdeal A) n x = 0 ↔ x ∈ maximalIdeal D ^ n := by
      intro x
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem A,
        ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval fg, LinearMap.mem_ker]
      constructor
      · intro h0
        rw [← AdicCompletion.factor_evalₐ_eq_eval _ x (by simp), h0, map_zero]
      · intro h0
        rw [← AdicCompletion.factor_eval_eq_evalₐ _ x (by simp), h0, map_zero]
    have hmapn : (maximalIdeal D ^ n).map (algebraMap D R) = (maximalIdeal A ^ n).map (algebraMap A R) := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_map]
      change (maximalIdeal A ^ n).map (g.comp _) = _
      rw [hg]
    refine LocalFlat.relationsLift_of_square
      (AdicCompletion.evalₐ (maximalIdeal A) n).toRingHom
      (Ideal.Quotient.mk ((maximalIdeal A ^ n).map (algebraMap A R)))
      (algebraMap _ _) (AdicCompletion.surjective_evalₐ _ n) Ideal.Quotient.mk_surjective ?_ ?_ ?_ ?_
    · ext x
      exact (hkerA x)
    · rw [Ideal.mk_ker, hmapn]
    · ext x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal A) n x)
      have hx : x - algebraMap A D a ∈ maximalIdeal D ^ n := by
        rw [← hkerA, map_sub, ← ha, AlgHom.commutes, sub_eq_zero]
        rfl
      have hx' : algebraMap D R x - h a ∈ (maximalIdeal A ^ n).map (algebraMap A R) := by
        rw [← hmapn, ← hgA]
        rw [show algebraMap D R x - g (algebraMap A D a) = algebraMap D R (x - algebraMap A D a) from
          (map_sub g _ _).symm]
        exact Ideal.mem_map_of_mem _ hx
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← ha]
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient, eq_comm, Ideal.Quotient.eq]
      exact hx'
    · rw [RingHom.flat_algebraMap_iff]
      exact Module.Flat.of_linearEquiv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R (maximalIdeal A ^ n)).toLinearEquiv
  haveI : Algebra.FormallyUnramified D (ResidueField R) := by
    rw [← RingHom.formallyUnramified_algebraMap]
    have e : (algebraMap D (ResidueField R)).comp (algebraMap A D) = (residue R).comp h := by
      rw [← hg]; rfl
    exact RingHom.FormallyUnramified.of_comp (f := algebraMap A D) (by rw [e]; exact hfu)
  haveI : Algebra.FormallyUnramified D R :=
    GlobalTheory.EtaleCompletionNormal.formallyUnramified_of_map_maximalIdeal hmA
  haveI : Algebra.FinitePresentation D R :=
    (Algebra.FinitePresentation.of_finiteType (R := D) (A := R)).1 inferInstance
  exact ⟨g, hg, Algebra.Etale.of_formallyUnramified_of_flat⟩


theorem normal_noetherian_tensor : ∀ (A C R : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing C] [Algebra A C] [Algebra.EssFiniteType A C] [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra A R], (∀ (P : Ideal C) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P) ∧ CharZero (Localization.AtPrime P)) → IsCN R → IsEtaleCompletion (algebraMap A R) → ((residue R).comp (algebraMap A R)).FormallyUnramified → ∀ (Q : Ideal (TensorProduct A C R)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) ∧ IsNoetherianRing (Localization.AtPrime Q) := by
  intro A C R _ _ _ _ _ _ _ _ _ _ hC hCN het hfu
  haveI := hCN.1
  exact GlobalTheory.TensorNormal.localization_tensor_normal_of_charZero A C R hC het hfu

end GlobalTheory.NormalBaseChange
end
