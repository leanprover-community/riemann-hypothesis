import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionQuotientRingEquivStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPrimeLocalizationDvr
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasicOpenEqZeroOfMemIInfPowSmul
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDomainOfIsIntegrallyClosedOfIsReduced
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConductorAdicCompletionEssFiniteType

section
section
open IsLocalRing

namespace GlobalTheory

theorem isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes
    (R : Type) [CommRing R] [IsNoetherianRing R] (x : R) (hx : x ∈ nonZeroDivisors R)
    (hloc : ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
      ∃ _ : IsDomain (Localization.AtPrime P), IsIntegrallyClosed (Localization.AtPrime P))
    (hcond : ∀ c : FractionRing R, IsIntegral R c →
      ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) x * c) :
    IsIntegrallyClosed R := by
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro c hc
  obtain ⟨s, hs⟩ := hcond c hc

  suffices hmem : Ideal.Quotient.mk (Ideal.span {x}) s = 0 by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hmem
    obtain ⟨w, rfl⟩ := hmem
    refine ⟨w, ?_⟩
    have hu : IsUnit (algebraMap R (FractionRing R) x) :=
      IsLocalization.map_units (FractionRing R) ⟨x, hx⟩
    apply hu.mul_left_cancel
    rw [← hs, map_mul, mul_comm]
  have key := eq_zero_of_forall_associatedPrimes_exists_smul_eq_zero
    (A := R) (M := R ⧸ Ideal.span {x}) (x := Ideal.Quotient.mk (Ideal.span {x}) s)
  apply key
  intro P hP
  haveI hPp : P.IsPrime := hP.isPrime
  obtain ⟨hdom, hic⟩ := hloc P hP
  let RP := Localization.AtPrime P
  let K := FractionRing RP

  have hreg : ∀ b ∈ nonZeroDivisors R, IsUnit (algebraMap R K b) := by
    intro b hb
    rw [IsScalarTower.algebraMap_apply R RP K]
    refine IsLocalization.map_units K (⟨algebraMap R RP b, ?_⟩ : nonZeroDivisors RP)
    refine mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ?_
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl RP b).1 h0
    have : (t : R) = 0 := (mem_nonZeroDivisors_iff_right.1 hb) t ht
    exact t.2 (this ▸ P.zero_mem)
  let φ : FractionRing R →+* K :=
    IsLocalization.lift (M := nonZeroDivisors R) (g := algebraMap R K) fun b ↦ hreg b b.2
  have hφ : ∀ r : R, φ (algebraMap R (FractionRing R) r) = algebraMap RP K (algebraMap R RP r) :=
    fun r ↦ by
      rw [IsLocalization.lift_eq, IsScalarTower.algebraMap_apply R RP K]
  have hint : IsIntegral RP (φ c) := by
    refine IsIntegral.map_of_comp_eq (algebraMap R RP) φ ?_ hc
    ext r
    simp only [RingHom.comp_apply]
    rw [hφ]
  obtain ⟨u, hu⟩ := (isIntegrallyClosed_iff K).1 hic hint
  have hxu : algebraMap R RP x * u = algebraMap R RP s := by
    apply IsFractionRing.injective RP K
    rw [map_mul, hu, ← hφ, ← hφ, hs, map_mul]
  obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj P.primeCompl u
  have h2 : algebraMap R RP (x * r) = algebraMap R RP (s * t) := by
    simp only at hrt
    rw [map_mul, map_mul, ← hxu, ← hrt]
    ring
  obtain ⟨t', ht'⟩ := (IsLocalization.eq_iff_exists P.primeCompl RP).1 h2
  refine ⟨t' * t, P.primeCompl.mul_mem t'.2 t.2, ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton']
  refine ⟨t' * r, ?_⟩
  linear_combination ht'

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegrallyClosed_of_integral_mul_mem_of_assocPrimes : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R → (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) → ∃ _ : IsDomain (Localization.AtPrime P), IsIntegrallyClosed (Localization.AtPrime P)) → (∀ c : FractionRing R, IsIntegral R c → ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) x * c) → IsIntegrallyClosed R := by
  atlas_forward_decl GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes
end

section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_of_isIntegrallyClosed_of_isReduced_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R], IsIntegrallyClosed R → IsDomain R := by
  first | exact @GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced | exact GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced | (intros; apply GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced <;> assumption)
end

section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_finite_of_essFiniteType_int : ∀ (D : Type) [CommRing D] [Algebra.EssFiniteType ℤ D], ringKrullDim D < ⊤ := by
  first | exact @GlobalTheory.ringKrullDim_lt_top_of_essFiniteType | exact GlobalTheory.ringKrullDim_lt_top_of_essFiniteType | (intros; apply GlobalTheory.ringKrullDim_lt_top_of_essFiniteType <;> assumption)
end

section
section
open IsLocalRing

namespace GlobalTheory

theorem adicCompletion_evalₐ_of_val {R : Type} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    {n : ℕ} (d : R) (hd : x.val n = Submodule.Quotient.mk d) :
    AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) d := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), AdicCompletion.eval_apply]
  erw [hd]
  rfl

theorem adicCompletion_val_of_le {R : Type} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    {m n : ℕ} (hmn : m ≤ n) (d : R) (hd : x.val n = Submodule.Quotient.mk d) :
    x.val m = Submodule.Quotient.mk d := by
  rw [← x.prop hmn, hd]
  rfl

theorem adicCompletion_injective_ringHom_of_finite
    (D N : Type) [CommRing D] [CommRing N] [IsNoetherianRing D] [Algebra D N]
    [Module.Finite D N] (hinj : Function.Injective (algebraMap D N)) (J : Ideal D) :
    ∃ f : AdicCompletion J D →+* AdicCompletion (J.map (algebraMap D N)) N,
      Function.Injective f := by
  set φ := algebraMap D N with hφ
  have hle : ∀ n : ℕ, J ^ n ≤ ((J.map φ) ^ n).comap φ := fun n => by
    rw [← Ideal.map_pow]; exact Ideal.le_comap_map
  let g : (n : ℕ) → AdicCompletion J D →+* N ⧸ (J.map φ) ^ n := fun n =>
    (Ideal.quotientMap ((J.map φ) ^ n) φ (hle n)).comp (AdicCompletion.evalₐ J n).toRingHom
  have hg : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow (J.map φ) hmn).comp (g n) = g m := by
    intro m n hmn
    ext x
    obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    have hn := adicCompletion_evalₐ_of_val J x d hd.symm
    have hm := adicCompletion_evalₐ_of_val J x d (adicCompletion_val_of_le J x hmn d hd.symm)
    simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hn, hm,
      Ideal.quotientMap_mk]
    rfl
  refine ⟨AdicCompletion.liftRingHom _ g hg, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hmap := AdicCompletion.map_injective J (f := Algebra.linearMap D N) hinj
  apply hmap
  rw [map_zero]
  apply AdicCompletion.ext
  intro n
  obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  have h1 := adicCompletion_evalₐ_of_val J x d hd.symm
  have h2 := congrArg (AdicCompletion.evalₐ (J.map φ) n) hx
  rw [AdicCompletion.evalₐ_liftRingHom, map_zero] at h2
  simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1,
    Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at h2
  rw [AdicCompletion.map_val_apply]
  erw [← hd]
  rw [LinearMap.reduceModIdeal_apply]
  refine ((Submodule.Quotient.mk_eq_zero _).2 ?_).trans rfl
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
  exact h2

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_adicCompletion_map_of_finite : ∀ (D N : Type) [CommRing D] [CommRing N] [IsNoetherianRing D] [Algebra D N] [Module.Finite D N], Function.Injective (algebraMap D N) → ∀ J : Ideal D, ∃ f : AdicCompletion J D →+* AdicCompletion (J.map (algebraMap D N)) N, Function.Injective f := by
  atlas_forward_decl GlobalTheory.adicCompletion_injective_ringHom_of_finite
end

section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_integralClosure_of_essFiniteType_int_domain : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D], Module.Finite D (integralClosure D (FractionRing D)) := by
  first | exact @GlobalTheory.finite_integralClosure_of_essFiniteType_int | exact GlobalTheory.finite_integralClosure_of_essFiniteType_int | (intros; apply GlobalTheory.finite_integralClosure_of_essFiniteType_int <;> assumption)
end

section
section
open IsLocalRing

namespace GlobalTheory

theorem mem_span_singleton_of_isNilpotent_of_associatedPrimes {R : Type} [CommRing R]
    [IsNoetherianRing R] (x : R)
    (hP : ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
      IsDomain (Localization.AtPrime P))
    {n : R} (hn : IsNilpotent n) : n ∈ Ideal.span {x} := by
  by_contra hnx
  have h0 : (Ideal.Quotient.mk (Ideal.span {x}) n) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨P, hPa, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
    (Ideal.Quotient.mk (Ideal.span {x}) n) h0
  haveI : P.IsPrime := hPa.isPrime
  haveI := hP P hPa
  have hz : algebraMap R (Localization.AtPrime P) n = 0 :=
    (hn.map (algebraMap R (Localization.AtPrime P))).eq_zero
  obtain ⟨⟨s, hs⟩, hsn⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ n).1 hz
  apply hs
  apply hle
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
  change Ideal.Quotient.mk (Ideal.span {x}) s * Ideal.Quotient.mk (Ideal.span {x}) n = 0
  rw [← map_mul, hsn, map_zero]

theorem isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R →
      x ∈ Ideal.jacobson (⊥ : Ideal R) →
      (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
        IsDomain (Localization.AtPrime P)) → IsReduced R := by
  intro R _ _ x hx hj hP
  refine ⟨fun n hn => ?_⟩
  have key : ∀ k : ℕ, ∀ m : R, IsNilpotent m → m ∈ Ideal.span {x} ^ k := by
    intro k
    induction k with
    | zero => intro m _; simp
    | succ k ih =>
      intro m hm
      obtain ⟨m', rfl⟩ := Ideal.mem_span_singleton'.1
        (mem_span_singleton_of_isNilpotent_of_associatedPrimes x hP hm)
      have hm' : IsNilpotent m' := by
        obtain ⟨e, he⟩ := hm
        refine ⟨e, ?_⟩
        rw [mul_pow] at he
        exact (mem_nonZeroDivisors_iff_right.1 (pow_mem hx e)) _ he
      rw [pow_succ', mul_comm m' x]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) (ih m' hm')
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := R) (Ideal.span {x})
    ((Ideal.span_singleton_le_iff_mem _).2 hj)
  have : n ∈ (⨅ i : ℕ, (Ideal.span {x}) ^ i • ⊤ : Submodule R R) := by
    rw [Submodule.mem_iInf]
    intro i
    simpa [smul_eq_mul, Ideal.mul_top] using key i n hn
  rw [hK] at this
  simpa using this

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_of_nonZeroDivisor_mem_jacobson_of_assocPrimes : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R → x ∈ Ideal.jacobson (⊥ : Ideal R) → (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) → IsDomain (Localization.AtPrime P)) → IsReduced R := by
  atlas_forward_decl GlobalTheory.isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes
end

section
open IsLocalRing

namespace GlobalTheory.CompletionReduced

theorem map_le_jacobson_of_comap_isMaximal {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : ∀ M : Ideal B, M.IsMaximal → (M.comap f).IsMaximal) (I : Ideal A)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal A)) : I.map f ≤ Ideal.jacobson (⊥ : Ideal B) := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro M ⟨-, hM⟩
  rw [Ideal.map_le_iff_le_comap]
  exact hI.trans (sInf_le ⟨bot_le, hf M hM⟩)

theorem exists_lt_of_add_one_le (e : WithBot ℕ∞) (n : ℕ) (h0 : 0 ≤ e) (h : e + 1 ≤ (n : WithBot ℕ∞)) :
    ∃ m : ℕ, m < n ∧ e ≤ (m : WithBot ℕ∞) := by
  induction e using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe k =>
    induction k using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := h
      rw [WithBot.coe_le_coe, top_add] at h'
      exact absurd h' (by simp)
    | coe k =>
      refine ⟨k, ?_, le_rfl⟩
      have : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by exact_mod_cast h
      exact_mod_cast this

theorem isReduced_of_normal (n : ℕ)
    (ih : ∀ m < n, ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
      ringKrullDim D ≤ (m : WithBot ℕ∞) → ∀ (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) →
        IsReduced (AdicCompletion J D))
    (N : Type) [CommRing N] [IsDomain N] [IsIntegrallyClosed N] [Algebra.EssFiniteType ℤ N]
    (hdimN : ringKrullDim N ≤ (n : WithBot ℕ∞)) (I : Ideal N)
    (hIjac : I ≤ Ideal.jacobson (⊥ : Ideal N)) : IsReduced (AdicCompletion I N) := by
  haveI : IsNoetherianRing N := Algebra.EssFiniteType.isNoetherianRing ℤ N
  by_cases hbot : I = ⊥
  · subst hbot
    exact isReduced_of_injective (AdicCompletion.ofAlgEquiv (⊥ : Ideal N)).symm.toRingEquiv.toRingHom
      (AdicCompletion.ofAlgEquiv (⊥ : Ideal N)).symm.injective
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let R := AdicCompletion I N
  haveI : IsNoetherianRing R := GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian N I
  haveI : Module.Flat N R := AdicCompletion.flat_of_isNoetherian I
  have hxR : algebraMap N R x ∈ nonZeroDivisors R := by
    have hxA : IsSMulRegular N x := IsSMulRegular.of_ne_zero hx0
    have h : IsSMulRegular R (algebraMap N R x) := hxA.of_flat
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    refine h ?_
    simpa [smul_eq_mul, mul_comm] using hy
  have hxjac : algebraMap N R x ∈ Ideal.jacobson (⊥ : Ideal R) := by
    have h1 : IsAdicComplete I R := AdicCompletion.isAdicComplete (IsNoetherian.noetherian I)
    have h2 : IsAdicComplete (I.map (algebraMap N R)) R := (IsAdicComplete.map_algebraMap_iff _ _).2 h1
    exact IsAdicComplete.le_jacobson_bot (I.map (algebraMap N R)) (Ideal.mem_map_of_mem _ hxI)
  have hredq : ∀ q : Ideal N, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap N R)) := by
    intro q hq hxq
    obtain ⟨e⟩ := GlobalTheory.T.nonempty_adicCompletion_quotient_ringEquiv N I q
    haveI : IsDomain (N ⧸ q) := Ideal.Quotient.isDomain q
    haveI : Algebra.EssFiniteType N (N ⧸ q) := inferInstance
    haveI hess : @Algebra.EssFiniteType ℤ (N ⧸ q) _ _ (Ring.toIntAlgebra _) := by
      letI := Ring.toIntAlgebra (N ⧸ q)
      haveI : IsScalarTower ℤ N (N ⧸ q) := .of_algebraMap_eq fun z => by simp
      exact Algebra.EssFiniteType.comp ℤ N (N ⧸ q)
    have hj : I.map (Ideal.Quotient.mk q) ≤ Ideal.jacobson (⊥ : Ideal (N ⧸ q)) :=
      map_le_jacobson_of_comap_isMaximal _
        (fun M hM => Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective) I hIjac
    have hd1 : ringKrullDim (N ⧸ q) + 1 ≤ (n : WithBot ℕ∞) := by
      have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hx0)
      have h2 : ringKrullDim (N ⧸ q) ≤ ringKrullDim (N ⧸ Ideal.span {x}) :=
        ringKrullDim_le_of_surjective _
          (Ideal.Quotient.factor_surjective (by rwa [Ideal.span_singleton_le_iff_mem]))
      exact ((add_le_add h2 le_rfl).trans h1).trans hdimN
    obtain ⟨m, hmn, hm⟩ := exists_lt_of_add_one_le _ n ringKrullDim_nonneg_of_nontrivial hd1
    haveI := ih m hmn (N ⧸ q) hm _ hj
    exact isReduced_of_injective e.toRingHom e.injective
  refine GlobalTheory.T.isReduced_of_nonZeroDivisor_mem_jacobson_of_assocPrimes R (algebraMap N R x) hxR hxjac ?_
  intro P _ hP
  obtain ⟨h1, -⟩ := GlobalTheory.T.associated_prime_localization_dvr N R x hx0 hredq P hP
  exact h1

theorem isReduced_of_dim_le : ∀ (n : ℕ) (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
    ringKrullDim D ≤ (n : WithBot ℕ∞) → ∀ (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) →
      IsReduced (AdicCompletion J D) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D _ _ _ hdim J hJ
  haveI : IsNoetherianRing D := Algebra.EssFiniteType.isNoetherianRing ℤ D

  let N := integralClosure D (FractionRing D)
  haveI : Module.Finite D N := GlobalTheory.T.finite_integralClosure_of_essFiniteType_int_domain D
  haveI : IsIntegrallyClosed N := integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing D)
  have hinj : Function.Injective (algebraMap D N) := by
    intro a b hab
    have := congrArg (fun y : N => (y : FractionRing D)) hab
    exact IsFractionRing.injective D (FractionRing D) this
  have hdimN : ringKrullDim N ≤ (n : WithBot ℕ∞) := by
    rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj]; exact hdim
  haveI : Algebra.EssFiniteType D N := inferInstance
  haveI hessN : @Algebra.EssFiniteType ℤ N _ _ (Ring.toIntAlgebra _) := by
    letI := Ring.toIntAlgebra N
    haveI : IsScalarTower ℤ D N := .of_algebraMap_eq fun z => by simp
    exact Algebra.EssFiniteType.comp ℤ D N
  have hIjac : J.map (algebraMap D N) ≤ Ideal.jacobson (⊥ : Ideal N) :=
    map_le_jacobson_of_comap_isMaximal _
      (fun M hM => Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M) J hJ
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_injective_adicCompletion_map_of_finite D N hinj J
  haveI := isReduced_of_normal n ih N hdimN _ hIjac
  exact isReduced_of_injective f hf

theorem isReduced_adicCompletion : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D]
    (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) → IsReduced (AdicCompletion J D) := by
  intro D _ _ _ J hJ
  have hlt := GlobalTheory.T.ringKrullDim_finite_of_essFiniteType_int D
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim D ≤ (m : WithBot ℕ∞) := by
    generalize ringKrullDim D = e at hlt ⊢
    induction e using WithBot.recBotCoe with
    | bot => exact ⟨0, bot_le⟩
    | coe k =>
      induction k using ENat.recTopCoe with
      | top => exact absurd hlt (by simp)
      | coe k => exact ⟨k, le_rfl⟩
  exact isReduced_of_dim_le m D hm J hJ

end GlobalTheory.CompletionReduced
end

section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adic_completion_reduced_of_jacobson : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D] (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) → IsReduced (AdicCompletion J D) := by
  first | exact @GlobalTheory.CompletionReduced.isReduced_adicCompletion | exact GlobalTheory.CompletionReduced.isReduced_adicCompletion | (intros; apply GlobalTheory.CompletionReduced.isReduced_adicCompletion <;> assumption)
end

section
namespace GlobalTheory.AnalyticNormality

open IsLocalRing

theorem completion_isDomain_and_isIntegrallyClosed :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A]
      [Algebra.EssFiniteType ℤ A], IsDomain (AdicCompletion (maximalIdeal A) A) ∧
        IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) := by
  have hnoeth := GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian
  have hquot := GlobalTheory.T.nonempty_adicCompletion_quotient_ringEquiv
  have hengine := GlobalTheory.T.associated_prime_localization_dvr
  have hclosed := GlobalTheory.T.isIntegrallyClosed_of_integral_mul_mem_of_assocPrimes
  have hdom := GlobalTheory.T.isDomain_of_isIntegrallyClosed_of_isReduced_local
  have hred := GlobalTheory.T.adic_completion_reduced_of_jacobson
  have hcond := GlobalTheory.T.exists_conductor_adicCompletion_essFiniteType
  intro A _ _ _ _ _ _
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  set m := maximalIdeal A with hm
  let R := AdicCompletion m A
  haveI : IsNoetherianRing R := hnoeth A m
  haveI : Module.Flat A R := AdicCompletion.flat_of_isNoetherian m
  haveI : IsReduced R := hred A m (IsLocalRing.maximalIdeal_le_jacobson _)
  obtain ⟨x, hx0, hx⟩ := hcond A
  have hxR : algebraMap A R x ∈ nonZeroDivisors R := by
    have hxA : IsSMulRegular A x := IsSMulRegular.of_ne_zero hx0
    have h : IsSMulRegular R (algebraMap A R x) := hxA.of_flat
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    refine h ?_
    simpa [smul_eq_mul, mul_comm] using hy
  have hredq : ∀ q : Ideal A, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap A R)) := by
    intro q hq _
    obtain ⟨e⟩ := hquot A m q
    haveI : IsDomain (A ⧸ q) := Ideal.Quotient.isDomain q
    haveI : Algebra.EssFiniteType A (A ⧸ q) := inferInstance
    haveI hess : @Algebra.EssFiniteType ℤ (A ⧸ q) _ _ (Ring.toIntAlgebra _) := by
      letI := Ring.toIntAlgebra (A ⧸ q)
      haveI : IsScalarTower ℤ A (A ⧸ q) := .of_algebraMap_eq fun z => by simp
      exact Algebra.EssFiniteType.comp ℤ A (A ⧸ q)
    have hj : m.map (Ideal.Quotient.mk q) ≤ Ideal.jacobson (⊥ : Ideal (A ⧸ q)) := by
      haveI : IsLocalRing (A ⧸ q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      refine Ideal.mem_comap.mpr (IsLocalRing.maximalIdeal_le_jacobson _ ?_)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (hu.unit⁻¹ : (A ⧸ q)ˣ).1
      have h1 : Ideal.Quotient.mk q (a * b) = 1 := by
        rw [map_mul, hb]; exact hu.mul_val_inv
      have h2 : a * b - 1 ∈ q := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
      have h3 : a * b - 1 ∈ m := IsLocalRing.le_maximalIdeal hq.ne_top h2
      have h4 : (1 : A) ∈ m := by
        have := m.sub_mem (m.mul_mem_right b ha) h3
        simpa using this
      exact (Ideal.ne_top_iff_one m).mp (IsLocalRing.maximalIdeal.isMaximal A).ne_top h4
    haveI := hred (A ⧸ q) _ hj
    exact isReduced_of_injective e.toRingHom e.injective
  have hcl : IsIntegrallyClosed R := by
    refine hclosed R (algebraMap A R x) hxR ?_ hx
    intro P _ hP
    obtain ⟨h1, h2⟩ := hengine A R x hx0 hredq P hP
    exact ⟨h1, inferInstance⟩
  exact ⟨hdom R hcl, hcl⟩

end GlobalTheory.AnalyticNormality
end
