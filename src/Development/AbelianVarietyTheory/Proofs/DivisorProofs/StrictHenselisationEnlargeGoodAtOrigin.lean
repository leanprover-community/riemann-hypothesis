import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeStrictHenselisationRetractModStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeBaseSeparablePointIntegralClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorExistsPointFiniteSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedOfFormallyEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstants
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationAtPrimeIsDiscreteValuationRingOfHeig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureEtaleAtOfHeightLeOnePurityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeIntegralClosureEtaleHeightOneStatement

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enlarge_base_separable_point_integralClosure : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ GlobalTheory.KeyOriginEnlarge.PointAtZero A' (Localization.AtPrime QA') DA' ρ') ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  first | (exact @GlobalTheory.KeyOriginEnlargePoint.enlarge_point) | (exact GlobalTheory.KeyOriginEnlargePoint.enlarge_point) | (intros; apply GlobalTheory.KeyOriginEnlargePoint.enlarge_point  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

theorem finite_closure (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Algebra A R] [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D] :
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  letI iRD : Algebra R D := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GlobalTheory.LocAcyc.GenFib A R) D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  haveI : Module.Flat R (GlobalTheory.LocAcyc.GenFib A R) := IsLocalization.flat _ M
  haveI : Module.Flat R D := Module.Flat.trans R (GlobalTheory.LocAcyc.GenFib A R) D
  haveI : Algebra.FormallyEtale R (GlobalTheory.LocAcyc.GenFib A R) := Algebra.FormallyEtale.of_isLocalization M
  haveI : Algebra.FormallyEtale R D := Algebra.FormallyEtale.comp R (GlobalTheory.LocAcyc.GenFib A R) D
  haveI : Algebra.EssFiniteType R (GlobalTheory.LocAcyc.GenFib A R) := Algebra.EssFiniteType.of_isLocalization _ M
  haveI : Algebra.EssFiniteType R D := Algebra.EssFiniteType.comp R (GlobalTheory.LocAcyc.GenFib A R) D
  have h1 : Module.Finite R (integralClosure R (R ⊗[R] D)) :=
    GlobalTheory.RootFibre.finite_integralClosure R D R
  have e := AlgEquiv.mapIntegralClosure (Algebra.TensorProduct.lid R D)
  have h2 : Module.Finite R (integralClosure R D) := Module.Finite.equiv e.toLinearEquiv
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  let f : integralClosure R D ≃ₗ[R] GlobalTheory.KeyOriginNoeth.closure A R D :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        apply Subtype.ext
        show r • x.1 = (baseHom A R D r) * x.1
        rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Finite.equiv f

end GlobalTheory.KeyOriginNoeth
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_integralClosureOverGenericFibre_of_etale : ∀ (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Algebra A R] [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  first | (exact @GlobalTheory.KeyOriginNoeth.finite_closure) | (exact GlobalTheory.KeyOriginNoeth.finite_closure) | (intros; apply GlobalTheory.KeyOriginNoeth.finite_closure <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

theorem isEtaleAt_closure_of_disjoint : ∀ (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    ∀ (Q : Ideal (GlobalTheory.KeyOriginNoeth.closure A R D)) [Q.IsPrime],
      (∀ a : A, a ≠ 0 → algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) (algebraMap A R a) ∉ Q) →
      Algebra.IsEtaleAt R Q := by
  intro A R D _ _ _ _ _ _ _ _
  letI := closureAlg A R D
  intro Q _ hQ
  letI : Algebra R D := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GlobalTheory.LocAcyc.GenFib A R) D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let SR : Submonoid R := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  let SC : Submonoid (closure A R D) := Algebra.algebraMapSubmonoid (closure A R D) SR
  have hCD : ∀ r : R, algebraMap (closure A R D) D (algebraMap R (closure A R D) r) = algebraMap R D r :=
    fun _ => rfl
  haveI : IsScalarTower R (closure A R D) D := IsScalarTower.of_algebraMap_eq (fun r => (hCD r).symm)
  have hunit : ∀ a : A, a ∈ nonZeroDivisors A → IsUnit (algebraMap R D (algebraMap A R a)) := by
    intro a ha
    have h1 : IsUnit (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) (algebraMap A R a)) :=
      IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A R) (⟨algebraMap A R a, a, ha, rfl⟩ : SR)
    rw [IsScalarTower.algebraMap_apply R (GlobalTheory.LocAcyc.GenFib A R) D]
    exact h1.map _
  haveI hloc : IsLocalization SC D := by
    refine (isLocalization_iff SC D).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩⟩
      exact hCD _ ▸ hunit a ha
    · intro d
      have hd : IsIntegral (GlobalTheory.LocAcyc.GenFib A R) d := Algebra.IsIntegral.isIntegral d
      obtain ⟨⟨m, hm⟩, hmi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization SR
        (Rₘ := GlobalTheory.LocAcyc.GenFib A R) d hd
      obtain ⟨a, ha, rfl⟩ := hm
      refine ⟨(⟨_, hmi⟩, ⟨algebraMap R (closure A R D) (algebraMap A R a), _, ⟨a, ha, rfl⟩, rfl⟩), ?_⟩
      show d * algebraMap (closure A R D) D (algebraMap R (closure A R D) (algebraMap A R a)) = _
      rw [hCD, mul_comm, ← Algebra.smul_def]
      rfl
    · intro x y h
      exact ⟨1, by rw [Subtype.ext h]⟩
  have hle : SC ≤ Q.primeCompl := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact hQ a (nonZeroDivisors.ne_zero ha)
  letI : Algebra D (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe D (Localization.AtPrime Q) SC Q.primeCompl hle
  haveI : IsScalarTower (closure A R D) D (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le D (Localization.AtPrime Q) SC Q.primeCompl hle
  haveI : IsLocalization (Algebra.algebraMapSubmonoid D Q.primeCompl) (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le D (Localization.AtPrime Q) SC Q.primeCompl hle
  haveI : Algebra.FormallyEtale D (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization (Algebra.algebraMapSubmonoid D Q.primeCompl)
  haveI : Algebra.FormallyEtale R (GlobalTheory.LocAcyc.GenFib A R) := Algebra.FormallyEtale.of_isLocalization SR
  haveI : Algebra.FormallyEtale R D := Algebra.FormallyEtale.comp R (GlobalTheory.LocAcyc.GenFib A R) D
  haveI : IsScalarTower R D (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply R (closure A R D) (Localization.AtPrime Q),
      IsScalarTower.algebraMap_apply (closure A R D) D (Localization.AtPrime Q), hCD])
  exact Algebra.FormallyEtale.comp R D (Localization.AtPrime Q)

end GlobalTheory.KeyOriginNoeth
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_prime_regular_height : ∀ (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    ∀ (Q : Ideal (GlobalTheory.KeyOriginNoeth.closure A R D)) [Q.IsPrime],
      (∀ a : A, a ≠ 0 → algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) (algebraMap A R a) ∉ Q) →
      Algebra.IsEtaleAt R Q := by
  first | (exact @GlobalTheory.KeyOriginNoeth.isEtaleAt_closure_of_disjoint) | (exact GlobalTheory.KeyOriginNoeth.isEtaleAt_closure_of_disjoint) | (intros; apply GlobalTheory.KeyOriginNoeth.isEtaleAt_closure_of_disjoint <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem etale_away_of_isEtaleAt_off_submonoid :
  ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] [Algebra.FinitePresentation R C]
    (M : Submonoid R),
    (∀ (Q : Ideal C) [Q.IsPrime], (∀ m ∈ M, algebraMap R C m ∉ Q) → Algebra.IsEtaleAt R Q) →
    ∃ m ∈ M, Algebra.Etale R (Localization.Away (algebraMap R C m)) := by
  intro R C _ _ _ _ M hM
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (Algebra.etaleLocus R C)ᶜ).1
    (Algebra.isOpen_etaleLocus (R := R) (A := C)).isClosed_compl
  by_cases hd : Disjoint (I : Set C) (M.map (algebraMap R C) : Set C)
  · exfalso
    obtain ⟨Q, hQ, hIQ, hQd⟩ := Ideal.exists_le_prime_disjoint I (M.map (algebraMap R C)) hd
    have hE : Algebra.IsEtaleAt R Q := by
      refine hM Q fun m hm hmQ => ?_
      exact Set.disjoint_left.1 hQd hmQ ⟨m, hm, rfl⟩
    have h1 : (⟨Q, hQ⟩ : PrimeSpectrum C) ∈ Algebra.etaleLocus R C := hE
    have h2 : (⟨Q, hQ⟩ : PrimeSpectrum C) ∈ (Algebra.etaleLocus R C)ᶜ := by
      rw [hI]; exact hIQ
    exact h2 h1
  · rw [Set.not_disjoint_iff] at hd
    obtain ⟨x, hxI, m, hm, rfl⟩ := hd
    refine ⟨m, hm, ?_⟩
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale]
    intro p hp
    by_contra hc
    have : p ∈ (Algebra.etaleLocus R C)ᶜ := hc
    rw [hI] at this
    exact hp (this hxI)

end GlobalTheory
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_away_of_isEtaleAt : ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] [Algebra.FinitePresentation R C]
    (M : Submonoid R),
    (∀ (Q : Ideal C) [Q.IsPrime], (∀ m ∈ M, algebraMap R C m ∉ Q) → Algebra.IsEtaleAt R Q) →
    ∃ m ∈ M, Algebra.Etale R (Localization.Away (algebraMap R C m)) := by
  first | (exact @GlobalTheory.etale_away_of_isEtaleAt_off_submonoid) | (exact GlobalTheory.etale_away_of_isEtaleAt_off_submonoid) | (intros; apply GlobalTheory.etale_away_of_isEtaleAt_off_submonoid <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem etale_localization_atPrime_tensor_of_etale_away : ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (b : R),
    Algebra.Etale R (Localization.Away (algebraMap R C b)) →
    ∀ (P : Ideal R) [P.IsPrime], b ∉ P →
      Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) C) := by
  intro R C _ _ _ b hE P _ hb
  let Rp := Localization.AtPrime P
  let Cb := Localization.Away (algebraMap R C b)
  haveI : Algebra.Etale Rp (Rp ⊗[R] Cb) := Algebra.Etale.baseChange R Cb Rp
  have hu : IsUnit ((Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C).toRingHom
      (algebraMap R C b)) := by
    change IsUnit ((Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C) (algebraMap R C b))
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R Rp (Rp ⊗[R] C)]
    exact (IsLocalization.map_units Rp (⟨b, hb⟩ : P.primeCompl)).map _
  let g0 : Cb →+* Rp ⊗[R] C := IsLocalization.Away.lift (algebraMap R C b) hu
  have hg0 : ∀ c : C, g0 (algebraMap C Cb c) = (1 : Rp) ⊗ₜ[R] c := fun c =>
    IsLocalization.Away.lift_eq (algebraMap R C b) hu c
  let g : Cb →ₐ[R] Rp ⊗[R] C :=
    { g0 with
      commutes' := fun r => by
        change g0 (algebraMap R Cb r) = _
        rw [IsScalarTower.algebraMap_apply R C Cb, hg0]
        exact (Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C).commutes r }
  let Φ : Rp ⊗[R] Cb →ₐ[Rp] Rp ⊗[R] C :=
    Algebra.TensorProduct.lift (Algebra.ofId Rp _) g (fun _ _ => Commute.all _ _)
  let Ψ : Rp ⊗[R] C →ₐ[Rp] Rp ⊗[R] Cb :=
    Algebra.TensorProduct.map (AlgHom.id Rp Rp) (IsScalarTower.toAlgHom R C Cb)
  have h1 : Φ.comp Ψ = AlgHom.id Rp _ := by
    ext c
    simp [Φ, Ψ, g, hg0]
  have h2 : Ψ.comp Φ = AlgHom.id Rp _ := by
    ext x
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    change Ψ (Φ ((1 : Rp) ⊗ₜ[R] algebraMap C Cb x)) = (1 : Rp) ⊗ₜ[R] algebraMap C Cb x
    have : Φ ((1 : Rp) ⊗ₜ[R] algebraMap C Cb x) = (1 : Rp) ⊗ₜ[R] x := by
      simp [Φ, g, hg0]
    rw [this]
    simp [Ψ]
  exact Algebra.Etale.of_equiv (AlgEquiv.ofAlgHom Ψ Φ h2 h1).symm

end GlobalTheory
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_localization_atPrime_tensor_of_etale_away' : ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (b : R),
    Algebra.Etale R (Localization.Away (algebraMap R C b)) →
    ∀ (P : Ideal R) [P.IsPrime], b ∉ P →
      Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) C) := by
  first | (exact @GlobalTheory.etale_localization_atPrime_tensor_of_etale_away) | (exact GlobalTheory.etale_localization_atPrime_tensor_of_etale_away) | (intros; apply GlobalTheory.etale_localization_atPrime_tensor_of_etale_away <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

theorem etale_of_isZTorsor (B D : Type) [CommRing B] [IsNoetherianRing B] [CommRing D] [Algebra B D]
    (q : ℕ) (hq : 0 < q) (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D))
    (h : GlobalTheory.KeyOriginCut.IsZTorsor B D q act) : Algebra.Etale B D := by
  haveI := GlobalTheory.TorsorFieldPoint.formallyUnramified_of_isZTorsor B D q hq act h
  obtain ⟨hfin, hproj, _, _⟩ := h
  haveI := hfin
  haveI := hproj
  haveI : Algebra.FinitePresentation B D :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

theorem exists_ne_zero_closureEtaleAt : ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime]
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ a : A, a ≠ 0 ∧ ∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P := by
  intro q A _ _ _ _ _ _ EA _ _ _ _ _ QA _ DA _ _ actA hq _ htor
  haveI : IsNoetherianRing EA := Algebra.FiniteType.isNoetherianRing (Polynomial A) EA
  obtain ⟨_, _⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed (Polynomial A) EA QA
  set R := Localization.AtPrime QA
  haveI : Module.Finite (GlobalTheory.LocAcyc.GenFib A R) DA := htor.1
  haveI := etale_of_isZTorsor _ DA q hq actA htor
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R DA
  haveI : Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R DA) := GlobalTheory.T.finite_integralClosureOverGenericFibre_of_etale A R DA
  haveI : Algebra.FinitePresentation R (GlobalTheory.KeyOriginNoeth.closure A R DA) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨m, hm, hE⟩ := GlobalTheory.T.exists_etale_away_of_isEtaleAt R (GlobalTheory.KeyOriginNoeth.closure A R DA)
    (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (fun Q _ hQ =>
      GlobalTheory.T.closure_prime_regular_height A R DA Q (fun a ha => hQ _ ⟨a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩))
  obtain ⟨a, ha, rfl⟩ := hm
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun P _ hP => ?_⟩
  exact GlobalTheory.T.etale_localization_atPrime_tensor_of_etale_away' R _ _ hE P hP

end GlobalTheory.KeyOriginEnlarge
end
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_closureEtaleAt_alt : ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime]
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ a : A, a ≠ 0 ∧ ∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.exists_ne_zero_closureEtaleAt) | (exact GlobalTheory.KeyOriginEnlarge.exists_ne_zero_closureEtaleAt) | (intros; apply GlobalTheory.KeyOriginEnlarge.exists_ne_zero_closureEtaleAt  <;> assumption)
end

section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KummerEnlarge

open GlobalTheory.NormalApprox

theorem height_comap_eq_one_of_goingDown {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Algebra.HasGoingDown A B] (Q : Ideal B) [Q.IsPrime] (hQ : Q.height = 1)
    (hne : Q.comap (algebraMap A B) ≠ ⊥) : (Q.comap (algebraMap A B)).height = 1 := by
  set p : Ideal A := Q.comap (algebraMap A B) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver p := ⟨rfl⟩
  apply le_antisymm
  · rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
    intro r hr hrp
    by_contra hcon
    have hr0 : r ≠ ⊥ := by
      rintro rfl
      simp at hcon
    haveI := hr
    obtain ⟨P₁, hP₁Q, hP₁, hP₁o⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := r) (q := p) Q hrp
    haveI := hP₁
    haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    obtain ⟨P₀, hP₀P₁, hP₀, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := r) P₁
      (bot_lt_iff_ne_bot.mpr hr0)
    haveI := hP₀
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hP₀P₁
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP₁Q
    rw [hQ] at h2
    have h4 : (1 : ℕ∞) ≤ P₁.height := le_trans le_add_self h1
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
    exact absurd h3 (by decide)
  · haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hne)
    simpa using this

theorem exists_uniformiser (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (p : Ideal A) :
    ∃ π : A, ∀ [p.IsPrime], p.height = 1 → Irreducible (algebraMap A (Localization.AtPrime p) π) := by
  by_cases h : p.IsPrime ∧ p.height = 1
  · obtain ⟨hp, h1⟩ := h
    haveI := GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one A p h1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj p.primeCompl ϖ
    refine ⟨x, fun _ => ?_⟩
    have hu : IsUnit (algebraMap A (Localization.AtPrime p) s) := IsLocalization.map_units _ s
    have e : algebraMap A (Localization.AtPrime p) x = ϖ * algebraMap A (Localization.AtPrime p) s :=
      hxs.symm
    rw [e]
    exact (irreducible_mul_isUnit hu).mpr hϖ
  · exact ⟨1, fun h1 => absurd ⟨inferInstance, h1⟩ h⟩

end GlobalTheory.KummerEnlarge

namespace GlobalTheory.KummerEnlarge

open GlobalTheory.NormalApprox

theorem exists_kummer_enlargement : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ a : A, a ≠ 0 →
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (f : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective f ∧ Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp f = i ∧
      ∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π := by
  intro T _ _ _ hT q hq hqT A _ _ _ _ _ _ i hi hloc a ha
  classical
  haveI : IsIntegrallyClosed T := GlobalTheory.VertUnitsNoeth.isIntegrallyClosed_of_absIntClosed' T hT
  choose π hπ using exists_uniformiser A
  have hy : ∀ p : Ideal A, ∃ y : T, y ^ q = i (π p) := by
    intro p
    obtain ⟨y, hy⟩ := hT (X ^ q - C (i (π p))) (monic_X_pow_sub_C _ hq.ne')
      (by rw [natDegree_X_pow_sub_C]; exact hq)
    refine ⟨y, ?_⟩
    simpa [sub_eq_zero] using hy
  choose y hy using hy
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})
  set S : Finset T := (Algebra.EssFiniteType.finset ℤ A).image i ∪ hfin.toFinset.image y with hS

  have hgen : ∀ z ∈ Algebra.adjoin ℤ ((Algebra.EssFiniteType.finset ℤ A : Finset A) : Set A),
      i z ∈ gen S := by
    intro z hz
    have h2 : i.toIntAlgHom z ∈ (Algebra.adjoin ℤ ((Algebra.EssFiniteType.finset ℤ A : Finset A) : Set A)).map
        i.toIntAlgHom := Subalgebra.mem_map.mpr ⟨z, hz, rfl⟩
    rw [AlgHom.map_adjoin] at h2
    refine Algebra.adjoin_mono ?_ h2
    rintro t ⟨u, hu, rfl⟩
    simp only [hS, Finset.coe_union, Finset.coe_image]
    exact Or.inl ⟨u, hu, rfl⟩
  have hmem : ∀ x : A, i x ∈ loc S := by
    intro x
    haveI := Algebra.EssFiniteType.isLocalization ℤ A
    obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj (Algebra.EssFiniteType.submonoid ℤ A) x
    refine ⟨i (m.1 : A), gen_le_norm S (hgen _ m.1.2), ?_, ?_⟩
    · exact (IsLocalization.map_units A m).map i
    · rw [mul_comm, ← map_mul]
      have e : x * (m.1 : A) = (r : A) := hrm
      rw [e]
      exact gen_le_norm S (hgen _ r.2)
  let f : A →+* loc S := i.codRestrict (loc S) hmem
  have hfinj : Function.Injective f := fun x x' h => hi (congrArg Subtype.val h)
  haveI := loc_isLocalization S
  haveI : IsNoetherianRing (loc S) :=
    IsLocalization.isNoetherianRing (unitsIn S) _ (norm_isNoetherianRing S)
  haveI : IsIntegrallyClosed (norm S) := norm_isIntegrallyClosed S
  haveI : IsIntegrallyClosed (loc S) :=
    isIntegrallyClosed_of_isLocalization (loc S) (unitsIn S) (unitsIn_le S)
  haveI : IsLocalRing (loc S) := loc_isLocalRing S
  refine ⟨loc S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    GlobalTheory.VertUnitsNoeth.essFiniteType_loc S, f, (loc S).subtype, hfinj, Subtype.val_injective,
    ⟨fun x hx => isUnit_of_isUnit_coe S x hx⟩, RingHom.ext fun _ => rfl, ?_⟩
  intro p₁ _ hp₁ hfa
  letI : Algebra A (loc S) := f.toAlgebra
  letI : Algebra A T := i.toAlgebra

  have hyint : ∀ p : Ideal A, IsIntegral A (y p) := by
    intro p
    refine ⟨X ^ q - C (π p), monic_X_pow_sub_C _ hq.ne', ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hy]
    exact sub_self _
  have hgenC : ∀ z ∈ gen S, z ∈ integralClosure A T := by
    intro z hz
    have hle : gen S ≤ (integralClosure A T).restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      intro t ht
      simp only [hS, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image] at ht
      rcases ht with ⟨u, -, rfl⟩ | ⟨p, -, rfl⟩
      · exact isIntegral_algebraMap
      · exact hyint p
    exact hle hz
  have hnormint : ∀ x (hx : x ∈ norm S), IsIntegral A (⟨x, norm_le_loc S hx⟩ : loc S) := by
    intro x hx
    let φ : gen S →+* integralClosure A T :=
      (gen S).val.toRingHom.codRestrict (integralClosure A T) (fun z => hgenC _ z.2)
    have h1 : IsIntegral (integralClosure A T) x :=
      IsIntegral.map_of_comp_eq φ (RingHom.id T) rfl hx.1
    have h2 : IsIntegral A x := isIntegral_trans x h1
    let g : loc S →ₐ[A] T := { (loc S).subtype with commutes' := fun _ => rfl }
    exact (isIntegral_algHom_iff g Subtype.val_injective).mp h2
  let B := integralClosure A (loc S)
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr
    (fun x x' h => hfinj (congrArg Subtype.val h))
  haveI : Algebra.HasGoingDown A B := inferInstance
  let M : Submonoid B := (IsUnit.submonoid (loc S)).comap (algebraMap B (loc S))
  haveI hML : IsLocalization M (loc S) := by
    refine ⟨fun m => m.2, fun z => ?_, fun {u v} h => ⟨1, ?_⟩⟩
    · obtain ⟨s, hs, hsu, hsz⟩ := z.2
      let sB : B := ⟨⟨s, norm_le_loc S hs⟩, hnormint s hs⟩
      let tB : B := ⟨⟨s * z, norm_le_loc S hsz⟩, hnormint _ hsz⟩
      have hsM : sB ∈ M := isUnit_of_isUnit_coe S _ hsu
      refine ⟨(tB, ⟨sB, hsM⟩), Subtype.ext ?_⟩
      change (z : T) * s = s * z
      ring
    · have : u = v := Subtype.val_injective h
      rw [this]
  set P : Ideal B := p₁.comap (algebraMap B (loc S)) with hP
  have hPh : P.height = 1 := by
    rw [hP, ← hp₁]
    exact IsLocalization.height_comap M p₁
  have hcomap : p₁.comap f = P.comap (algebraMap A B) := by
    rw [hP, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    rfl
  have hne : P.comap (algebraMap A B) ≠ ⊥ := by
    rw [← hcomap]
    intro h
    have : a ∈ p₁.comap f := hfa
    rw [h, Ideal.mem_bot] at this
    exact ha this
  have hheight : (p₁.comap f).height = 1 := by
    rw [hcomap]
    exact height_comap_eq_one_of_goingDown P hPh hne

  have hmin : p₁.comap f ∈ (Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hfa⟩, fun r hr hrp => ?_⟩
    obtain ⟨hrprime, har⟩ := hr
    by_contra hlt
    have hlt' : r < p₁.comap f := lt_of_le_of_ne hrp (fun e => hlt (e ▸ le_rfl))
    haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    have hr0 : (⊥ : Ideal A) < r := by
      refine bot_lt_iff_ne_bot.mpr fun h => ha ?_
      have : a ∈ r := har (Ideal.mem_span_singleton_self a)
      rw [h, Ideal.mem_bot] at this
      exact this
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hr0
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt'
    rw [hheight] at h2
    have h4 : (1 : ℕ∞) ≤ r.height := le_trans le_add_self h1
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
    exact absurd h3 (by decide)
  have hyS : y (p₁.comap f) ∈ S := by
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hmin))
  refine ⟨hheight, π (p₁.comap f), hπ _ hheight, ⟨y (p₁.comap f), mem_loc_of_mem S hyS⟩, ?_⟩
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  exact hy _

end GlobalTheory.KummerEnlarge
end
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummerEnlargement_rootsOfUniformisers : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ a : A, a ≠ 0 →
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (f : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective f ∧ Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp f = i ∧
      ∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π := by
  first | (exact @GlobalTheory.KummerEnlarge.exists_kummer_enlargement) | (exact GlobalTheory.KummerEnlarge.exists_kummer_enlargement) | (intros; apply GlobalTheory.KummerEnlarge.exists_kummer_enlargement  <;> assumption)
end

section
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginEnlarge

theorem etale_enlarge : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ GlobalTheory.KeyOriginNoeth.Good A' (Localization.AtPrime QA') DA' ρ') ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq hqT A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA hFits ρ hρ hpt
  have htor := hFits.2.2.2.2.2.2
  obtain ⟨a, ha0, ha⟩ := GlobalTheory.T.exists_ne_zero_closureEtaleAt_alt q A EA QA DA actA hq hFits.2.2.1 htor
  obtain ⟨A₁, _, _, _, _, _, _, f, i₁, hf, hi₁, hloc₁, hcomp, hK⟩ :=
    GlobalTheory.T.exists_kummerEnlargement_rootsOfUniformisers T hT q hq hqT A i hFits.1 hFits.2.1 a ha0
  obtain ⟨EA₁, _, _, _, _, _, QA₁, _, jA₁, ψA₁, DA₁, _, _, actA₁, hFits₁, ⟨ρ₁, hρ₁, hpt₁⟩, hEt, β, h, hβ, hh⟩ :=
    GlobalTheory.T.baseChange_integralClosure_etale_height_one T O hT P φ hφ hsh hP q hq hqT A i EA QA jA ψA DA actA hFits ρ hρ hpt a ha0 ha
      A₁ f i₁ hf hi₁ hloc₁ hcomp hK
  refine ⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, i₁,
    EA₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₁, inferInstance, jA₁, ψA₁,
    DA₁, inferInstance, inferInstance, actA₁, hFits₁, ⟨ρ₁, hρ₁, ?_⟩, β, h, hβ, hh⟩
  exact (GlobalTheory.KeyOriginEnlarge.good_iff_etaleAt _ _ _ _).2
    ⟨GlobalTheory.T.integralClosureEtaleAt_of_height_le_one_purity q A₁ EA₁ QA₁ DA₁ actA₁ hFits₁.2.2.2.2.2.2 hEt, hpt₁⟩

end GlobalTheory.KeyOriginEnlarge
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_enlarge_by_uniformiser_roots : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ GlobalTheory.KeyOriginNoeth.Good A' (Localization.AtPrime QA') DA' ρ') ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.etale_enlarge) | (exact GlobalTheory.KeyOriginEnlarge.etale_enlarge) | (intros; apply GlobalTheory.KeyOriginEnlarge.etale_enlarge  <;> assumption)
end

section
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginEnlarge

theorem enlarge_good : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A')
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime),
      QA'.comap (algebraMap (Polynomial A') EA') = GlobalTheory.KeyOriginCut.originIdeal A' ∧ IsUnit (q : A') ∧
      ∃ (ρ' : Localization.AtPrime QA' →+* A'),
        ρ'.comp (algebraMap A' (Localization.AtPrime QA')) = RingHom.id A' ∧
        RingHom.ker ρ' = Ideal.span {algebraMap (Polynomial A') (Localization.AtPrime QA') Polynomial.X} ∧
      ∃ (jA' : Localization.AtPrime QA' →+* O)
        (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O),
        ψA'.comp (algebraMap (Localization.AtPrime QA') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA' ∧
      ∃ (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
        (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA' q actA' ∧
        GlobalTheory.KeyOriginNoeth.Good A' (Localization.AtPrime QA') DA' ρ' ∧
        ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))
          (h : DA →+* DA'),
          ψA'.comp β = ψA ∧
          h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
            (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq0 hqT A _ _ _ _ _ _ i hi hil hqA EA _ _ _ _ _ QA _ hQA jA hjA
    ψA hψA DA _ _ actA htor
  have hF : GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA :=
    ⟨hi, hil, hqA, hQA, hjA, hψA, htor⟩
  obtain ⟨A₁, _, _, _, _, _, _, i₁, EA₁, _, _, _, _, _, QA₁, _, jA₁, ψA₁, DA₁, _, _, act₁, hF₁,
    ⟨ρ₁, hR₁, -⟩, β₁, h₁, hβ₁, hh₁⟩ := GlobalTheory.T.enlarge_strictHenselisation_retract_mod T O hT P φ hφ hsh hP q hq0 hqT A i EA QA jA ψA DA actA hF
  obtain ⟨A₂, _, _, _, _, _, _, i₂, EA₂, _, _, _, _, _, QA₂, _, jA₂, ψA₂, DA₂, _, _, act₂, hF₂,
    ⟨ρ₂, hR₂, hpt₂⟩, β₂, h₂, hβ₂, hh₂⟩ :=
    GlobalTheory.T.enlarge_base_separable_point_integralClosure T O hT P φ hφ hsh hP q hq0 hqT A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ act₁ hF₁ ρ₁ hR₁
  obtain ⟨A₃, _, _, _, _, _, _, i₃, EA₃, _, _, _, _, _, QA₃, _, jA₃, ψA₃, DA₃, _, _, act₃, hF₃,
    ⟨ρ₃, hR₃, hgood⟩, β₃, h₃, hβ₃, hh₃⟩ :=
    GlobalTheory.T.etale_enlarge_by_uniformiser_roots T O hT P φ hφ hsh hP q hq0 hqT A₂ i₂ EA₂ QA₂ jA₂ ψA₂ DA₂ act₂ hF₂ ρ₂ hR₂ hpt₂
  refine ⟨A₃, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    EA₃, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₃, inferInstance,
    hF₃.2.2.2.1, hF₃.2.2.1, ρ₃, hR₃.1, hR₃.2.1, jA₃, ψA₃, hF₃.2.2.2.2.2.1, DA₃, inferInstance,
    inferInstance, act₃, hF₃.2.2.2.2.2.2, hgood, β₃.comp (β₂.comp β₁), h₃.comp (h₂.comp h₁), ?_, ?_⟩
  · ext x
    have a1 := RingHom.congr_fun hβ₁ x
    have a2 := RingHom.congr_fun hβ₂ (β₁ x)
    have a3 := RingHom.congr_fun hβ₃ (β₂ (β₁ x))
    simp only [RingHom.comp_apply] at a1 a2 a3 ⊢
    rw [a3, a2, a1]
  · ext x
    have a1 := RingHom.congr_fun hh₁ x
    have a2 := RingHom.congr_fun hh₂ (β₁ x)
    have a3 := RingHom.congr_fun hh₃ (β₂ (β₁ x))
    simp only [RingHom.comp_apply] at a1 a2 a3 ⊢
    rw [a1, a2, a3]

end GlobalTheory.KeyOriginEnlarge
end
