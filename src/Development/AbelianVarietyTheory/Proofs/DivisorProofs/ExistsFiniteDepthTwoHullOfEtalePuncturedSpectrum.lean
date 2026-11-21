import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoOfIsIntegrallyClosedOfIsRegularLoca
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ExistsIsRegularAppendOfModDepthGE
import BuildAid.ForwardExisting

section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

def idealTransform (S : Type) [CommRing S] (I : Ideal S) (A : Type) [CommRing A] [Algebra S A] :
    Subalgebra S (FractionRing S ⊗[S] A) where
  carrier := {z | ∃ k : ℕ, ∀ a ∈ I ^ k,
    a • z ∈ (Algebra.TensorProduct.includeRight : A →ₐ[S] FractionRing S ⊗[S] A).range}
  mul_mem' := by
    rintro z w ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, fun a ha => ?_⟩
    rw [pow_add] at ha
    refine Submodule.mul_induction_on ha (fun b hb c hc => ?_) (fun u v hu hv => ?_)
    · rw [← smul_mul_smul_comm]
      exact mul_mem (hk b hb) (hl c hc)
    · rw [add_smul]; exact add_mem hu hv
  add_mem' := by
    rintro z w ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨max k l, fun a ha => ?_⟩
    rw [smul_add]
    exact add_mem (hk a (Ideal.pow_le_pow_right (le_max_left _ _) ha))
      (hl a (Ideal.pow_le_pow_right (le_max_right _ _) ha))
  algebraMap_mem' := by
    intro r
    refine ⟨0, fun a _ => ?_⟩
    exact ⟨algebraMap S A (a * r), by simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul', mul_smul]⟩

theorem mem_idealTransform_of_forall_smul_mem {S : Type} [CommRing S] [IsNoetherianRing S]
    {I : Ideal S} {A : Type} [CommRing A] [Algebra S A] (z : FractionRing S ⊗[S] A)
    (h : ∀ a ∈ I, a • z ∈ idealTransform S I A) : z ∈ idealTransform S I A := by
  let R := (Algebra.TensorProduct.includeRight : A →ₐ[S] FractionRing S ⊗[S] A).range
  let Q : Ideal S := Submodule.comap (LinearMap.toSpanSingleton S _ z) (Subalgebra.toSubmodule R)
  have hQ : ∀ a, a ∈ Q ↔ a • z ∈ R := fun a => by simp [Q]
  have hrad : I ≤ Q.radical := by
    intro a ha
    obtain ⟨k, hk⟩ := h a ha
    refine ⟨k + 1, ?_⟩
    rw [hQ, pow_succ, mul_smul]
    exact hk _ (Ideal.pow_mem_pow ha k)
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian I)
  exact ⟨n, fun a ha => (hQ a).1 (hn ha)⟩

end GlobalTheory
end

section
section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem isSMulRegular_of_etale_punctured_of_depth_pos_domain :
    ∀ (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsDomain S] (A : Type)
      [CommRing A] [Algebra S A], ReciprocityTheory.CA.ModDepthGE S A 1 →
      (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) →
      ∀ s : S, s ≠ 0 → IsSMulRegular A s := by
  intro S _ _ _ _ A _ _ hdepth het f hf
  obtain ⟨rs, hlen, hmem, hreg⟩ := hdepth
  obtain ⟨w, hw⟩ : ∃ w, rs = [w] := List.length_eq_one_iff.mp hlen
  subst hw
  have hwm : w ∈ maximalIdeal S := hmem w (by simp)
  have hwr : IsSMulRegular A w := ((RingTheory.Sequence.isRegular_cons_iff A w []).mp hreg).1
  have hmax : maximalIdeal S ∉ associatedPrimes S A := ReciprocityTheory.CA.max_not_mem_ass_of_reg hwm hwr
  refine IsSMulRegular.of_right_eq_zero_of_smul fun a ha => ?_
  by_contra ha0
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing S a ha0
  have hfP : f ∈ P := hle (Submodule.mem_colon_singleton.mpr (by simpa using ha))
  obtain ⟨hPprime, b, hb⟩ := Submodule.isAssociatedPrime_iff.mp hP
  haveI := hPprime
  have hPm : P ≠ maximalIdeal S := fun h => hmax (h ▸ hP)
  haveI := het P hPm
  set L := Localization.AtPrime P
  haveI : Module.Flat L (TensorProduct S L A) := inferInstance
  have hfb : f • b = 0 := by
    have : f ∈ (⊥ : Submodule S A).colon {b} := hb ▸ hfP
    simpa using Submodule.mem_colon_singleton.mp this
  have hloc : IsLocalizedModule P.primeCompl (TensorProduct.mk S L A 1) :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl L _).mpr (TensorProduct.isBaseChange S A L)
  have hfL : algebraMap S L f ≠ 0 := by
    intro h0
    apply hf
    exact (IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors P)) (by simpa using h0)
  have h1 : (1 : L) ⊗ₜ[S] b = 0 := by
    have : algebraMap S L f • ((1 : L) ⊗ₜ[S] b) = 0 := by
      rw [algebraMap_smul, ← TensorProduct.tmul_smul, hfb, TensorProduct.tmul_zero]
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := TensorProduct S L A)
      (mem_nonZeroDivisors_of_ne_zero hfL)
    exact hreg (show algebraMap S L f • ((1 : L) ⊗ₜ[S] b) = algebraMap S L f • 0 by rw [this, smul_zero])
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff P.primeCompl (TensorProduct.mk S L A 1)).mp h1
  have htP : (t : S) ∈ P := by
    have : (t : S) ∈ (⊥ : Submodule S A).colon {b} :=
      Submodule.mem_colon_singleton.mpr (by simpa [Submonoid.smul_def] using ht)
    exact hb ▸ this
  exact t.2 htP

end GlobalTheory
end

open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos_domain' : ∀ (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsDomain S] (A : Type) [CommRing A] [Algebra S A], ReciprocityTheory.CA.ModDepthGE S A 1 → (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) → ∀ s : S, s ≠ 0 → IsSMulRegular A s := by
  atlas_forward_decl GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos_domain
end

section
section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem isInteger_of_maximalIdeal_smul_isInteger (S : Type) [CommRing S] [IsRegularLocalRing S]
    (hdim : 2 ≤ ringKrullDim S) (c : FractionRing S)
    (hc : ∀ a ∈ maximalIdeal S, IsLocalization.IsInteger S (a • c)) :
    IsLocalization.IsInteger S c := by
  obtain ⟨hD, hI⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing S
  have hinj : Function.Injective (algebraMap S (FractionRing S)) := IsFractionRing.injective S (FractionRing S)
  by_cases hA : ∀ a ∈ maximalIdeal S, ∃ y ∈ maximalIdeal S, algebraMap S (FractionRing S) y = a • c
  ·
    let N : Submodule S (FractionRing S) := Submodule.map (Algebra.linearMap S (FractionRing S)) (maximalIdeal S)
    have hne : maximalIdeal S ≠ ⊥ := by
      intro h
      have hF : IsField S := (isField_iff_maximalIdeal_eq).2 h
      have := ringKrullDim_eq_zero_of_isField hF
      rw [this] at hdim
      exact absurd hdim (by decide)
    have hN : N ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have : Algebra.linearMap S (FractionRing S) x ∈ N := Submodule.mem_map_of_mem hx
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact hinj (by simpa using this)
    have hFG : N.FG := Submodule.FG.map _ (IsNoetherian.noetherian _)
    have hint : IsIntegral S c := by
      refine isIntegral_of_smul_mem_submodule N hN hFG c ?_
      intro n hn
      obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨y, hy, hy'⟩ := hA a ha
      refine Submodule.mem_map.2 ⟨y, hy, ?_⟩
      simp only [Algebra.linearMap_apply, smul_eq_mul]
      rw [hy', Algebra.smul_def, mul_comm]
    exact (IsIntegrallyClosed.isIntegral_iff).1 hint
  · exfalso
    push_neg at hA
    obtain ⟨a, ha, hy⟩ := hA
    obtain ⟨y, hy'⟩ := hc a ha
    have hyu : y ∉ maximalIdeal S := fun h => hy y h hy'
    have hyunit : IsUnit y := by simpa [mem_maximalIdeal, mem_nonunits_iff] using hyu
    have hspan : maximalIdeal S = Ideal.span {a} := by
      apply le_antisymm
      · intro b hb
        obtain ⟨z, hz⟩ := hc b hb
        have key : b * y = a * z := by
          apply hinj
          rw [map_mul, map_mul, hy', hz, ← Algebra.smul_def, ← Algebra.smul_def, smul_comm]
        rw [Ideal.mem_span_singleton']
        obtain ⟨u, rfl⟩ := hyunit
        refine ⟨z * ↑u⁻¹, ?_⟩
        calc z * ↑u⁻¹ * a = (a * z) * ↑u⁻¹ := by ring
          _ = (b * ↑u) * ↑u⁻¹ := by rw [key]
          _ = b := by simp [mul_assoc]
      · rw [Ideal.span_le]
        simpa using ha
    have h1 : (maximalIdeal S).spanFinrank ≤ 1 := by
      rw [hspan]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton a)).trans ?_
      simp
    have h2 := ringKrullDim_le_spanFinrank_maximalIdeal S
    have h3 : ringKrullDim S ≤ 1 := h2.trans (by exact_mod_cast h1)
    have := hdim.trans h3
    exact absurd this (by decide)

theorem isInteger_of_maximalIdeal_pow_smul_isInteger :
    ∀ (S : Type) [CommRing S] [IsRegularLocalRing S], 2 ≤ ringKrullDim S →
      ∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ maximalIdeal S ^ k,
        IsLocalization.IsInteger S (a • c)) → IsLocalization.IsInteger S c := by
  intro S _ _ hdim k
  induction k with
  | zero =>
    intro c hc
    simpa using hc 1 (by simp)
  | succ k ih =>
    intro c hc
    apply isInteger_of_maximalIdeal_smul_isInteger S hdim c
    intro a ha
    apply ih
    intro b hb
    rw [smul_smul]
    apply hc
    rw [pow_succ]
    exact Ideal.mul_mem_mul hb ha

end GlobalTheory
end

open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInteger_of_maximalIdeal_pow_smul_isInteger' : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S], 2 ≤ ringKrullDim S → ∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ maximalIdeal S ^ k, IsLocalization.IsInteger S (a • c)) → IsLocalization.IsInteger S c := by
  atlas_forward_decl GlobalTheory.isInteger_of_maximalIdeal_pow_smul_isInteger
end

section
section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem fg_of_saturated_ideal_power_into_image :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] (I : Ideal S),
      (∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ I ^ k, IsLocalization.IsInteger S (a • c)) →
        IsLocalization.IsInteger S c) →
      ∀ (M : Type) [AddCommGroup M] [Module S M] [Module.Finite S M]
        (N : Submodule S (FractionRing S ⊗[S] M)),
        (∀ z ∈ N, ∃ k : ℕ, ∀ a ∈ I ^ k,
          a • z ∈ LinearMap.range (TensorProduct.mk S (FractionRing S) M 1)) → N.FG := by
  intro S _ _ _ I hsat M _ _ _ N hN
  classical
  set K := FractionRing S
  let V := K ⊗[S] M
  let b := Module.Free.chooseBasis K V
  let ι := Module.Free.ChooseBasisIndex K V
  let T : V →ₗ[S] (ι → K) := (b.equivFun.toLinearMap).restrictScalars S

  let L : Submodule S (ι → K) := LinearMap.range ((Algebra.linearMap S K).compLeft ι)
  have memL : ∀ v : ι → K, (∀ i, IsLocalization.IsInteger S (v i)) → v ∈ L := by
    intro v hv
    choose w hw using hv
    exact ⟨w, funext fun i => hw i⟩
  have memL' : ∀ v ∈ L, ∀ i, IsLocalization.IsInteger S (v i) := by
    rintro v ⟨w, rfl⟩ i
    exact ⟨w i, rfl⟩
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := S) (M := M)
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors S)
    (Finset.univ : Finset (Fin n × ι)) (fun p => T (1 ⊗ₜ g p.1) p.2)
  let F : V →ₗ[S] (ι → K) := (d : S) • T
  have hFM : ∀ m : M, F (1 ⊗ₜ m) ∈ L := by
    intro m
    have hle : Submodule.span S (Set.range g) ≤ L.comap (F ∘ₗ TensorProduct.mk S K M 1) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show F (1 ⊗ₜ g j) ∈ L
      apply memL
      intro i
      exact hd (j, i) (Finset.mem_univ _)
    have : m ∈ Submodule.span S (Set.range g) := by rw [hg]; trivial
    exact hle this
  have hFN : ∀ z ∈ N, F z ∈ L := by
    intro z hz
    obtain ⟨k, hk⟩ := hN z hz
    apply memL
    intro i
    apply hsat k
    intro a ha
    obtain ⟨m, hm⟩ := hk a ha
    have h1 := hFM m
    simp only [TensorProduct.mk_apply] at hm
    rw [hm, map_smul] at h1
    simpa using memL' _ h1 i
  have hFinj : Function.Injective F := by
    intro x y hxy
    have hd0 : algebraMap S K (d : S) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    have : algebraMap S K (d : S) • b.equivFun x = algebraMap S K (d : S) • b.equivFun y := by
      simpa [F, T, algebraMap_smul] using hxy
    exact b.equivFun.injective (smul_right_injective _ hd0 this)
  have hLfg : L.FG := by
    show (LinearMap.range ((Algebra.linearMap S K).compLeft ι)).FG
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  haveI : IsNoetherian S L := isNoetherian_of_fg_of_noetherian L hLfg
  apply Submodule.fg_of_fg_map_injective F hFinj
  exact Submodule.FG.of_le_of_isNoetherian (T := L) (by
    rintro _ ⟨z, hz, rfl⟩
    exact hFN z hz)

end GlobalTheory
end

open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fg_of_ideal_pow_smul_mem_range_tensor : ∀ (S : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] (I : Ideal S), (∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ I ^ k, IsLocalization.IsInteger S (a • c)) → IsLocalization.IsInteger S c) → ∀ (M : Type) [AddCommGroup M] [Module S M] [Module.Finite S M] (N : Submodule S (FractionRing S ⊗[S] M)), (∀ z ∈ N, ∃ k : ℕ, ∀ a ∈ I ^ k, a • z ∈ LinearMap.range (TensorProduct.mk S (FractionRing S) M 1)) → N.FG := by
  atlas_forward_decl GlobalTheory.fg_of_saturated_ideal_power_into_image
end

section
section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem etale_localization_of_cokernel_killed (S : Type) [CommRing S] (A B : Type) [CommRing A]
    [CommRing B] [Algebra S A] [Algebra S B] (ι : A →ₐ[S] B) (hι : Function.Injective ι)
    (p : Ideal S) [p.IsPrime] (s : S) (hs : s ∉ p) (hB : ∀ y : B, s • y ∈ ι.range)
    (hA : Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) :
    Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) B) := by
  let Φ : TensorProduct S (Localization.AtPrime p) A →ₐ[Localization.AtPrime p]
      TensorProduct S (Localization.AtPrime p) B :=
    Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ι
  have inj : Function.Injective Φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := Localization.AtPrime p)
      (ι.toLinearMap.restrictScalars S) hι
  have hu : IsUnit (algebraMap S (Localization.AtPrime p) s) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨s, hs⟩ : p.primeCompl)
  obtain ⟨u, hu'⟩ := hu
  have surj : Function.Surjective Φ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul r y =>
      obtain ⟨a, ha⟩ := hB y
      refine ⟨(r * ↑u⁻¹) ⊗ₜ a, ?_⟩
      simp only [Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [show ι a = s • y from ha, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.smul_def, ← hu', mul_left_comm, Units.mul_inv, mul_one]
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective Φ ⟨inj, surj⟩)

end GlobalTheory
end

open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_localization_of_injective_cokernel_killed : ∀ (S : Type) [CommRing S] (A B : Type) [CommRing A] [CommRing B] [Algebra S A] [Algebra S B] (ι : A →ₐ[S] B), Function.Injective ι → ∀ (p : Ideal S) [p.IsPrime] (s : S), s ∉ p → (∀ y : B, s • y ∈ ι.range) → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A) → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) B) := by
  atlas_forward_decl GlobalTheory.etale_localization_of_cokernel_killed
end

section
section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem modDepthGE_two_of_isSMulRegular_of_quotSMulTop :
    ∀ (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] (M : Type) [AddCommGroup M]
      [Module S M] [Module.Finite S M] [Nontrivial M] (x : S), x ∈ maximalIdeal S →
      IsSMulRegular M x →
      (∀ u : M, (∀ a ∈ maximalIdeal S, a • u ∈ x • (⊤ : Submodule S M)) →
        u ∈ x • (⊤ : Submodule S M)) →
      ReciprocityTheory.CA.ModDepthGE S M 2 := by
  intro S _ _ _ M _ _ _ _ x hxm hreg hsoc
  obtain ⟨y, hym, hyreg⟩ : ∃ y ∈ maximalIdeal S, IsSMulRegular (QuotSMulTop x M) y := by
    by_contra hno
    push_neg at hno
    have hfin := associatedPrimes.finite S (QuotSMulTop x M)
    have hsub : (maximalIdeal S : Set S) ⊆
        ⋃ p ∈ associatedPrimes S (QuotSMulTop x M), (p : Set S) := by
      intro y hy
      rw [biUnion_associatedPrimes_eq_compl_regular]
      exact hno y hy
    obtain ⟨p, hp, hmp⟩ := (Ideal.subset_union_prime (s := hfin.toFinset) (f := id) ⊥ ⊥
      (fun p hp _ _ => (hfin.mem_toFinset.mp hp).isPrime)).mp (by simpa using hsub)
    rw [hfin.mem_toFinset] at hp
    have hpm : p = maximalIdeal S :=
      (le_antisymm (le_maximalIdeal (hp.isPrime.ne_top)) hmp)
    rw [hpm] at hp
    obtain ⟨-, w, hw⟩ := isAssociatedPrime_iff.mp hp
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hu : ∀ a ∈ maximalIdeal S, a • u ∈ x • (⊤ : Submodule S M) := by
      intro a ha
      rw [hw, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero] at ha
      exact ha
    apply (maximalIdeal.isMaximal S).ne_top
    rw [hw, Ideal.eq_top_iff_one, Submodule.mem_colon_singleton, Submodule.mem_bot, one_smul,
      Submodule.Quotient.mk_eq_zero]
    exact hsoc u hu
  refine ⟨[x, y], rfl, (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption), ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption),
    RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_cons_iff]
  exact ⟨hreg, hyreg, RingTheory.Sequence.IsWeaklyRegular.nil _ _⟩

end GlobalTheory
end

open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modDepthGE_two_of_regular_quotient_no_socle : ∀ (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] (M : Type) [AddCommGroup M] [Module S M] [Module.Finite S M] [Nontrivial M] (x : S), x ∈ maximalIdeal S → IsSMulRegular M x → (∀ u : M, (∀ a ∈ maximalIdeal S, a • u ∈ x • (⊤ : Submodule S M)) → u ∈ x • (⊤ : Submodule S M)) → ReciprocityTheory.CA.ModDepthGE S M 2 := by
  atlas_forward_decl GlobalTheory.modDepthGE_two_of_isSMulRegular_of_quotSMulTop
end

section
section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem Submodule.exists_pow_smul_mem_of_forall_exists :
    ∀ (S : Type) [CommRing S] (I : Ideal S) (M : Type) [AddCommGroup M] [Module S M]
      [Module.Finite S M] (N : Submodule S M),
      (∀ y : M, ∃ k : ℕ, ∀ a ∈ I ^ k, a • y ∈ N) → ∃ k : ℕ, ∀ a ∈ I ^ k, ∀ y : M, a • y ∈ N := by
  intro S _ I M _ _ _ N h
  choose f hf using h
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := S) (M := M)
  refine ⟨s.sup f, fun a ha y => ?_⟩
  have key : _root_.Submodule.span S (s : Set M) ≤ N.comap (a • LinearMap.id) := by
    rw [_root_.Submodule.span_le]
    intro x hx
    show (a • LinearMap.id : M →ₗ[S] M) x ∈ N
    rw [LinearMap.smul_apply, LinearMap.id_apply]
    exact hf x a (Ideal.pow_le_pow_right (Finset.le_sup (f := f) hx) ha)
  have hy : y ∈ _root_.Submodule.span S (s : Set M) := by rw [hs]; trivial
  have := key hy
  rwa [_root_.Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] at this

end GlobalTheory
end

open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_mem_of_forall_exists' : ∀ (S : Type) [CommRing S] (I : Ideal S) (M : Type) [AddCommGroup M] [Module S M] [Module.Finite S M] (N : Submodule S M), (∀ y : M, ∃ k : ℕ, ∀ a ∈ I ^ k, a • y ∈ N) → ∃ k : ℕ, ∀ a ∈ I ^ k, ∀ y : M, a • y ∈ N := by
  atlas_forward_decl GlobalTheory.Submodule.exists_pow_smul_mem_of_forall_exists
end

section
section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem exists_finite_depth_two_hull_of_etale_off_closed_point : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S], 2 ≤ ringKrullDim S → ∀ (A : Type) [CommRing A] [Algebra S A] [Module.Finite S A], ReciprocityTheory.CA.ModDepthGE S A 1 → (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) → ∃ (A' : Type) (_ : CommRing A') (_ : Algebra S A'), Module.Finite S A' ∧ ∃ ι : A →ₐ[S] A', Function.Injective ι ∧ ReciprocityTheory.CA.ModDepthGE S A' 2 ∧ (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A')) ∧ ∃ k : ℕ, ∀ x ∈ maximalIdeal S ^ k, ∀ y : A', x • y ∈ ι.range := by
  intro S _ _ hdim A _ _ _ hdep het
  obtain ⟨hSd, hSic⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing S
  have htf : ∀ s : S, s ≠ 0 → IsSMulRegular A s := GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos_domain' S A hdep het
  let K := FractionRing S
  let j : A →ₐ[S] K ⊗[S] A := Algebra.TensorProduct.includeRight
  have hj : ∀ a, j a = TensorProduct.mk S K A 1 a := fun a => rfl
  haveI : IsLocalizedModule (nonZeroDivisors S) (TensorProduct.mk S K A 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors S) K _).mpr (TensorProduct.isBaseChange S A K)
  have hjinj : Function.Injective j := by
    intro a b hab
    rw [hj, hj] at hab
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors S) hab
    exact htf c (nonZeroDivisors.coe_ne_zero c) hc

  have hVtf : ∀ s : S, s ≠ 0 → ∀ v w : K ⊗[S] A, s • v = s • w → v = w := by
    intro s hs v w h
    rw [← algebraMap_smul K s v, ← algebraMap_smul K s w] at h
    have hs' : algebraMap S K s ≠ 0 := by
      rw [ne_eq, ← map_zero (algebraMap S K)]
      exact fun e => hs (IsFractionRing.injective S K e)
    exact smul_right_injective _ hs' h
  let B := idealTransform S (maximalIdeal S) A
  have hjB : ∀ a, j a ∈ B := fun a => ⟨0, fun b _ => ⟨b • a, by simp [j]⟩⟩
  let ι : A →ₐ[S] B := j.codRestrict B hjB
  have hιinj : Function.Injective ι := fun a b h => hjinj (congrArg Subtype.val h)
  have hrange : ∀ y : B, y ∈ ι.range ↔ (y : K ⊗[S] A) ∈ j.range := by
    intro y
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
    · rintro ⟨a, ha⟩; exact ⟨a, Subtype.ext ha⟩

  have hfg : (Subalgebra.toSubmodule B).FG := by
    refine GlobalTheory.T.fg_of_ideal_pow_smul_mem_range_tensor S (maximalIdeal S) (GlobalTheory.T.isInteger_of_maximalIdeal_pow_smul_isInteger' S hdim) A _ fun z hz => ?_
    obtain ⟨k, hk⟩ := hz
    exact ⟨k, fun a ha => by obtain ⟨b, hb⟩ := hk a ha; exact ⟨b, hb⟩⟩
  haveI hfin : Module.Finite S B := Module.Finite.iff_fg.mpr hfg

  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ a ∈ maximalIdeal S ^ k, ∀ y : B, a • y ∈ ι.range.toSubmodule := by
    refine GlobalTheory.T.exists_pow_smul_mem_of_forall_exists' S (maximalIdeal S) B _ fun y => ?_
    obtain ⟨k, hk⟩ := y.2
    exact ⟨k, fun a ha => (hrange _).2 (hk a ha)⟩
  refine ⟨B, inferInstance, inferInstance, hfin, ι, hιinj, ?_, ?_, k, hk⟩
  ·
    obtain ⟨q, -, hq0, hqm⟩ := exists_isPrime_ne_bot_lt_maximalIdeal_of_two_le_ringKrullDim S hdim
    have hm0 : maximalIdeal S ≠ ⊥ := (bot_le.trans_lt hqm).ne'
    obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm0
    haveI : Nontrivial A := by
      obtain ⟨rs, -, -, hreg⟩ := hdep
      by_contra hA
      rw [not_nontrivial_iff_subsingleton] at hA
      exact hreg.2 (Subsingleton.elim _ _)
    haveI : Nontrivial B := nontrivial_of_ne (ι 0) (ι 1) (hιinj.ne zero_ne_one)
    have hxreg : IsSMulRegular B x := fun u v h =>
      Subtype.ext (hVtf x hx0 _ _ (congrArg Subtype.val h))
    refine GlobalTheory.T.modDepthGE_two_of_regular_quotient_no_socle S B x hxm hxreg fun u hu => ?_
    let w : K ⊗[S] A := (algebraMap S K x)⁻¹ • (u : K ⊗[S] A)
    have hxw : x • w = u := by
      simp only [w, ← algebraMap_smul K x, smul_smul]
      rw [mul_inv_cancel₀, one_smul]
      rw [ne_eq, ← map_zero (algebraMap S K)]
      exact fun e => hx0 (IsFractionRing.injective S K e)
    have hwB : w ∈ B := by
      refine mem_idealTransform_of_forall_smul_mem w fun a ha => ?_
      obtain ⟨v, -, hv⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp (hu a ha)
      have : a • w = v := by
        apply hVtf x hx0
        rw [smul_comm, hxw]
        exact (congrArg Subtype.val hv).symm
      rw [this]; exact v.2
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨⟨w, hwB⟩, Submodule.mem_top, Subtype.ext hxw⟩
  · intro p _ hp
    have hnot : ¬ maximalIdeal S ^ k ≤ p := fun h =>
      hp ((maximalIdeal.isMaximal S).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
        (Ideal.IsPrime.le_of_pow_le h)).symm
    obtain ⟨s, hs, hsp⟩ := Set.not_subset.mp hnot
    exact GlobalTheory.T.etale_localization_of_injective_cokernel_killed S A B ι hιinj p s hsp (hk s hs) (het p hp)

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_depth_two_hull_of_etale_punctured_spectrum : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S], 2 ≤ ringKrullDim S → ∀ (A : Type) [CommRing A] [Algebra S A] [Module.Finite S A], ReciprocityTheory.CA.ModDepthGE S A 1 → (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) → ∃ (A' : Type) (_ : CommRing A') (_ : Algebra S A'), Module.Finite S A' ∧ ∃ ι : A →ₐ[S] A', Function.Injective ι ∧ ReciprocityTheory.CA.ModDepthGE S A' 2 ∧ (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A')) ∧ ∃ k : ℕ, ∀ x ∈ maximalIdeal S ^ k, ∀ y : A', x • y ∈ ι.range := by
  atlas_forward_decl GlobalTheory.exists_finite_depth_two_hull_of_etale_off_closed_point
end
