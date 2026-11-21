import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumComapInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisGroupFixedFieldBaseChangeLocalField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import GroundTheory.LocalFields.DifferentGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegerCoboundaryAdditiveModPrimePow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationOfPrimeOfGaloisExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInitialSegmentNotInfLeFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumEqSumRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildLowerRamificationGroupAntitoneEventuallyBot

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem character_kernel_generator (G : Type) [Group G] (p r : ℕ) (a : G → ℤ) (hp : p.Prime)
    (hadd : ∀ σ τ, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ) (hne : ∃ σ, ¬ (p : ℤ) ^ r ∣ a σ) :
    ∃ (J : Subgroup G) (_ : J.Normal) (σ₁ : G) (c : ℤ), (∀ σ, σ ∈ J ↔ (p : ℤ) ^ r ∣ a σ) ∧
      c * (p : ℤ) ^ r = (J.index : ℤ) * a σ₁ ∧ ¬ (p : ℤ) ∣ c := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcast : ∀ x : ℤ, ((x : ZMod (p ^ r)) = 0 ↔ (p : ℤ) ^ r ∣ x) := by
    intro x
    exact_mod_cast ZMod.intCast_zmod_eq_zero_iff_dvd x (p ^ r)
  have hmul : ∀ σ τ, ((a (σ * τ) : ZMod (p ^ r))) = (a σ : ZMod (p ^ r)) + (a τ : ZMod (p ^ r)) := by
    intro σ τ
    have := (hcast _).2 (hadd σ τ)
    push_cast at this
    linear_combination this
  have hone : ((a 1 : ℤ) : ZMod (p ^ r)) = 0 := by
    have := hmul 1 1
    simp only [mul_one] at this
    linear_combination -this
  let f : G →* Multiplicative (ZMod (p ^ r)) :=
    { toFun := fun σ => Multiplicative.ofAdd (a σ : ZMod (p ^ r))
      map_one' := by simp only [hone, ofAdd_zero]
      map_mul' := fun σ τ => by simp only [hmul, ofAdd_add] }
  have hfx : ∀ σ, f σ = Multiplicative.ofAdd (a σ : ZMod (p ^ r)) := fun _ => rfl
  have hker : ∀ σ, σ ∈ f.ker ↔ (p : ℤ) ^ r ∣ a σ := by
    intro σ
    rw [MonoidHom.mem_ker, hfx, ofAdd_eq_one, hcast]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := f.range)
  obtain ⟨σ₁, hσ₁⟩ := g.2
  set x : ZMod (p ^ r) := (a σ₁ : ZMod (p ^ r)) with hxdef
  have hidx : f.ker.index = addOrderOf x := by
    have h1 : f.ker.index = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    rw [h1, ← hg, ← Subgroup.orderOf_coe, ← hσ₁, hfx, orderOf_ofAdd_eq_addOrderOf]
  have hsm : ∀ k : ℕ, k • x = 0 ↔ (p : ℤ) ^ r ∣ (k : ℤ) * a σ₁ := by
    intro k
    rw [← hcast]
    push_cast
    rw [nsmul_eq_mul]
  have hdvd : addOrderOf x ∣ p ^ r :=
    (addOrderOf_dvd_natCard x).trans (by rw [Nat.card_zmod])
  obtain ⟨s, hsr, hs⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hs0 : s ≠ 0 := by
    rintro rfl
    obtain ⟨τ, hτ⟩ := hne
    have : f.ker = ⊤ := Subgroup.index_eq_one.1 (by rw [hidx, hs, pow_zero])
    exact hτ ((hker τ).1 (this ▸ Subgroup.mem_top τ))
  obtain ⟨c, hc⟩ := (hsm (addOrderOf x)).1 (addOrderOf_nsmul_eq_zero x)
  refine ⟨f.ker, inferInstance, σ₁, c, hker, ?_, ?_⟩
  · rw [hidx, hc]; ring
  · rintro ⟨d, rfl⟩
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have key : (p : ℤ) ^ r ∣ ((p ^ (s - 1) : ℕ) : ℤ) * a σ₁ := by
      refine ⟨d, ?_⟩
      apply mul_left_cancel₀ hp0
      have hs' : (p : ℤ) ^ s = p * p ^ (s - 1) := by
        rw [← pow_succ']; congr 1; omega
      have := hc
      rw [hs] at this
      push_cast at this ⊢
      rw [hs'] at this
      linear_combination this
    have h2 : addOrderOf x ∣ p ^ (s - 1) :=
      addOrderOf_dvd_of_nsmul_eq_zero ((hsm _).2 key)
    rw [hs, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h2
    omega

end GlobalTheory.PMon.Ram
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_mod_prime_pow_kernel_generator : ∀ (G : Type) [Group G] (p r : ℕ) (a : G → ℤ), p.Prime → (∀ σ τ, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ) → (∃ σ, ¬ (p : ℤ) ^ r ∣ a σ) → ∃ (J : Subgroup G) (_ : J.Normal) (σ₁ : G) (c : ℤ), (∀ σ, σ ∈ J ↔ (p : ℤ) ^ r ∣ a σ) ∧ c * (p : ℤ) ^ r = (J.index : ℤ) * a σ₁ ∧ ¬ (p : ℤ) ∣ c := by
  atlas_forward_decl GlobalTheory.PMon.Ram.character_kernel_generator
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integer_coboundary_additive_mod_prime_pow : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A : Subgroup (L ≃ₐ[K] L)) (x : L) (a : (L ≃ₐ[K] L) → ℤ), p.Prime → 0 < E → OrdIs L p E → (∀ σ ∈ A, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → ∀ σ ∈ A, ∀ τ ∈ A, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ := by
  first | exact @GlobalTheory.PMon.Ram.coboundary_int_additive_mod | exact GlobalTheory.PMon.Ram.coboundary_int_additive_mod | (intros; apply GlobalTheory.PMon.Ram.coboundary_int_additive_mod <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_add_two_mul_card_inf_le_of_not_le {G : Type} [Group G] [Finite G] (H J : Subgroup G)
    (h : ¬ H ≤ J) : Nat.card ↥H + 2 * Nat.card ↥(H ⊓ J) ≤ 2 * Nat.card ↥H := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (inf_le_left : H ⊓ J ≤ H)
  have hpos : 0 < Nat.card ↥(H ⊓ J) := Nat.card_pos
  have hposH : 0 < Nat.card ↥H := Nat.card_pos
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply h
    have he := Subgroup.eq_of_le_of_card_ge (inf_le_left : H ⊓ J ≤ H) (by rw [hk, mul_one])
    rw [← he]
    exact inf_le_right
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  have hk2 : 2 ≤ k := by omega
  rw [hk]
  nlinarith

open Classical in

theorem ite_add_two_mul_card_inf_sub_one_le {G : Type} [Group G] [Finite G] (H J : Subgroup G) :
    (if H ≤ J then 0 else Nat.card ↥H) + 2 * (Nat.card ↥(H ⊓ J) - 1) ≤ 2 * (Nat.card ↥H - 1) := by
  have h1 : 0 < Nat.card ↥(H ⊓ J) := Nat.card_pos
  have h2 : Nat.card ↥(H ⊓ J) ≤ Nat.card ↥H := Subgroup.card_le_of_le inf_le_left
  split_ifs with h
  · omega
  · have := card_add_two_mul_card_inf_le_of_not_le H J h
    omega

theorem jumpSum_add_two_mul_differentExponent_fixedField_le (F L : Type) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L]
    [IsGalois F L] (J : Subgroup (L ≃ₐ[F] L)) :
    jumpSum (wild F L) ⊤ J + 2 * differentExponent ↥(IntermediateField.fixedField J) L ≤
      2 * differentExponent F L := by
  classical
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot F L
  have hcard : ∀ i : ℤ, Nat.card ↥(lowerRamificationGroup (↥(IntermediateField.fixedField J)) L i) =
      Nat.card ↥(lowerRamificationGroup F L i ⊓ J) := by
    intro i
    rw [← lowerRamificationGroup_map_fixedField J i,
      Subgroup.card_map_of_injective (AlgEquiv.restrictScalarsHom_injective F)]
  have hFbot : lowerRamificationGroup F L ((N + 1 : ℕ) : ℤ) = ⊥ := hN _ (by push_cast; omega)
  have hMbot : lowerRamificationGroup (↥(IntermediateField.fixedField J)) L ((N + 1 : ℕ) : ℤ) = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ (AlgEquiv.restrictScalarsHom_injective F),
      lowerRamificationGroup_map_fixedField, hFbot, bot_inf_eq]
  have hjs : jumpSum (wild F L) ⊤ J = ∑ t ∈ Finset.range N,
      (if lowerRamificationGroup F L ((t + 1 : ℕ) : ℤ) ≤ J then 0
        else Nat.card ↥(lowerRamificationGroup F L ((t + 1 : ℕ) : ℤ))) := by
    unfold jumpSum
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range N)]
    · refine Finset.sum_congr rfl fun t _ => ?_
      simp only [wild, top_inf_eq, Nat.cast_add, Nat.cast_one]
    · intro t ht
      rw [Function.mem_support] at ht
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h'
      apply ht
      simp only [wild, top_inf_eq]
      rw [hN _ (by omega)]
      simp
  rw [hjs, differentExponent_eq_sum_card_lowerRamificationGroup F L hFbot,
    differentExponent_eq_sum_card_lowerRamificationGroup _ L hMbot,
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [hcard]
  have hterm := Finset.sum_le_sum (s := Finset.range N) fun t _ =>
    ite_add_two_mul_card_inf_sub_one_le (lowerRamificationGroup F L ((t + 1 : ℕ) : ℤ)) J
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hterm
  have h0 : Nat.card ↥(lowerRamificationGroup F L ((0 : ℕ) : ℤ) ⊓ J) - 1 ≤
      Nat.card ↥(lowerRamificationGroup F L ((0 : ℕ) : ℤ)) - 1 :=
    Nat.sub_le_sub_right (Subgroup.card_le_of_le inf_le_left) 1
  rw [mul_add, mul_add]
  omega

end GlobalTheory.PMon.Ram
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationJumpSum_add_two_mul_differentExponent_le : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (J : Subgroup (L ≃ₐ[F] L)), jumpSum (wild F L) ⊤ J + 2 * differentExponent ↥(IntermediateField.fixedField J) L ≤ 2 * differentExponent F L := by
  atlas_forward_decl GlobalTheory.PMon.Ram.jumpSum_add_two_mul_differentExponent_fixedField_le
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

open IsDiscreteValuationRing in

theorem sq_mul_not_mem_maxIdeal_pow :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p e : ℕ) (c : ℤ),
      p.Prime → 0 < e → OrdIs F p e → ¬ (p : ℤ) ∣ c →
      ∀ w ∈ 𝓂[F] ^ (3 * e), ((w : 𝒪[F]) : F) ≠ (p : F) ^ 2 * (c : F) := by
  intro F _ _ _ _ p e c hp he hord hc w hw heq
  have hw' : w = (p : 𝒪[F]) ^ 2 * (c : 𝒪[F]) := by
    apply Subtype.ext
    simpa using heq

  have hcop : IsCoprime (p : ℤ) c :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).mpr hc
  obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom 𝒪[F])
  have h1 : IsUnit (a * (Int.castRingHom 𝒪[F]) p + b * (Int.castRingHom 𝒪[F]) c) := by
    rw [hab]; exact isUnit_one
  have hpnu : ¬ IsUnit (p : 𝒪[F]) := by
    rintro ⟨u, hu⟩
    have h0 := addVal_eq_zero_of_unit u
    rw [hu] at h0
    unfold OrdIs at hord
    rw [hord] at h0
    exact (Nat.pos_iff_ne_zero.mp he) (by exact_mod_cast h0)
  have hcu : IsUnit (c : 𝒪[F]) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h | h
    · exfalso; apply hpnu
      have := isUnit_of_mul_isUnit_right h
      simpa using this
    · have := isUnit_of_mul_isUnit_right h
      simpa using this

  have hval : addVal 𝒪[F] w = ((2 * e : ℕ) : ℕ∞) := by
    obtain ⟨u, hu⟩ := hcu
    rw [hw', addVal_mul, addVal_pow, ← hu, addVal_eq_zero_of_unit, add_zero]
    unfold OrdIs at hord
    rw [hord]
    push_cast
    rfl
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[F]
  rw [(irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hw
  have hle := (addVal_le_iff_dvd).mpr hw
  rw [addVal_pow, addVal_uniformizer hϖ, hval] at hle
  have : ((3 * e : ℕ) : ℕ∞) ≤ ((2 * e : ℕ) : ℕ∞) := by simpa using hle
  have := ENat.coe_le_coe.mp this
  omega

end GlobalTheory.PMon.Ram
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_mul_not_mem_maximalIdeal_pow_three_mul : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p e : ℕ) (c : ℤ), p.Prime → 0 < e → OrdIs F p e → ¬ (p : ℤ) ∣ c → ∀ w ∈ 𝓂[F] ^ (3 * e), ((w : 𝒪[F]) : F) ≠ (p : F) ^ 2 * (c : F) := by
  atlas_forward_decl GlobalTheory.PMon.Ram.sq_mul_not_mem_maxIdeal_pow
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent :
    ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (n : ℕ), ramificationIndex F M * n ≤ differentExponent F M → ∀ z : 𝒪[M], ∃ w ∈ 𝓂[F] ^ n, ((w : 𝒪[F]) : F) = Algebra.trace F M (z : M) := by
  intro F M _ _ _ _ _ _ _ _ _ _ _ _ n hn z
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hϖ0 : (ϖ : F) ≠ 0 := by
    have : ϖ ≠ 0 := hϖ.ne_zero
    exact_mod_cast this
  set I : Ideal 𝒪[M] := Ideal.span {algebraMap 𝒪[F] 𝒪[M] (ϖ ^ n)} with hI
  have hImap : I = (𝓂[F] ^ n).map (algebraMap 𝒪[F] 𝒪[M]) := by
    rw [hI, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton]
  have hIeq : I = 𝓂[M] ^ (ramificationIndex F M * n) := by
    rw [hImap, Ideal.map_pow, map_maximalIdeal, pow_mul]
  have hle : differentIdeal 𝒪[F] 𝒪[M] ≤ I := by
    rw [differentIdeal_eq_maximalIdeal_pow, hIeq]
    exact Ideal.pow_le_pow_right hn
  have hIne : I ≠ ⊥ := by
    rw [hI, ne_eq, Ideal.span_singleton_eq_bot]
    intro h
    have : ((algebraMap 𝒪[F] 𝒪[M] (ϖ ^ n) : 𝒪[M]) : M) = 0 := by rw [h]; rfl
    rw [coe_algebraMap_integer] at this
    rw [SubmonoidClass.coe_pow, map_pow] at this
    exact pow_ne_zero n ((_root_.map_ne_zero _).mpr hϖ0) this
  have key := (differentialIdeal_le_iff (K := F) (L := M) hIne).mp hle
  set x : M := algebraMap F M ((ϖ : F) ^ n) with hx
  have hx0 : x ≠ 0 := by
    rw [hx]; exact (_root_.map_ne_zero _).mpr (pow_ne_zero _ hϖ0)
  have hIfrac : ((I : FractionalIdeal (nonZeroDivisors 𝒪[M]) M)) = FractionalIdeal.spanSingleton (nonZeroDivisors 𝒪[M]) x := by
    rw [hI, FractionalIdeal.coeIdeal_span_singleton]
    congr 1
  have hmem : x⁻¹ * (z : M) ∈ (((I⁻¹ : FractionalIdeal (nonZeroDivisors 𝒪[M]) M) : Submodule 𝒪[M] M)) := by
    rw [hIfrac, FractionalIdeal.spanSingleton_inv, FractionalIdeal.mem_coe,
      FractionalIdeal.mem_spanSingleton]
    exact ⟨z, by rw [Algebra.smul_def, mul_comm]; rfl⟩
  have htr : Algebra.trace F M (x⁻¹ * (z : M)) ∈ (1 : Submodule 𝒪[F] F) :=
    key ⟨_, hmem, rfl⟩
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp htr
  refine ⟨ϖ ^ n * a, Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ) n), ?_⟩
  have hz : (z : M) = x * (x⁻¹ * (z : M)) := by rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
  rw [hz, hx, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow]
  rw [← ha]
  rfl

end GlobalTheory.PMon.Ram
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trace_mem_maximalIdeal_pow_of_differentExponent : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (n : ℕ), ramificationIndex F M * n ≤ differentExponent F M → ∀ z : 𝒪[M], ∃ w ∈ 𝓂[F] ^ n, ((w : 𝒪[F]) : F) = Algebra.trace F M (z : M) := by
  atlas_forward_decl GlobalTheory.PMon.Ram.exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem GlobalTheory.PMon.Ram.exists_integer_fixedField_trace_eq : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p r : ℕ) (x : L) (a : (L ≃ₐ[F] L) → ℤ) (J : Subgroup (L ≃ₐ[F] L)) [J.Normal] (σ₁ : L ≃ₐ[F] L) (c : ℤ), (p : L) ≠ 0 → AxIn F L p → (∀ σ : L ≃ₐ[F] L, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → (∀ σ ∈ J, (p : ℤ) ^ r ∣ a σ) → c * (p : ℤ) ^ r = (J.index : ℤ) * a σ₁ → ∃ z : 𝒪[↥(IntermediateField.fixedField J)], Algebra.trace F ↥(IntermediateField.fixedField J) (z : ↥(IntermediateField.fixedField J)) = (p : F) ^ 2 * (c : F) := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p r x a J _ σ₁ c hp hAx hx hJ hc
  set M := IntermediateField.fixedField J with hMdef
  have hpr : (p : L) ^ r ≠ 0 := pow_ne_zero _ hp
  have hint : ∀ n : ℤ, (n : L) ∈ 𝒪[L] := fun n => intCast_mem _ n
  have hσO : ∀ (σ : L ≃ₐ[F] L) (w : L), w ∈ 𝒪[L] → σ w ∈ 𝒪[L] := by
    intro σ w hw
    rw [Valuation.mem_integer_iff] at hw ⊢
    rwa [valuation_algEquiv_apply F L σ w]
  have hdiff : ∀ σ : L ≃ₐ[F] L, σ (x / (p : L) ^ r) - x / (p : L) ^ r = (σ x - x) / (p : L) ^ r := by
    intro σ
    rw [map_div₀, map_pow, map_natCast, sub_div]

  have hJint : ∀ σ ∈ J, σ (x / (p : L) ^ r) - x / (p : L) ^ r ∈ 𝒪[L] := by
    intro σ hσ
    obtain ⟨z, hz, e⟩ := hx σ
    obtain ⟨k, hk⟩ := hJ σ hσ
    rw [hdiff, e, hk]
    have : (((p : ℤ) ^ r * k : ℤ) : L) + (p : L) ^ r * z = (p : L) ^ r * ((k : L) + z) := by
      push_cast; ring
    rw [this, mul_div_cancel_left₀ _ hpr]
    exact add_mem (hint k) hz
  obtain ⟨y, hyJ, hw⟩ := hAx J (x / (p : L) ^ r) hJint
  obtain ⟨z₁, hz₁, e₁⟩ := hx σ₁
  have hyM : y ∈ M := (IntermediateField.mem_fixedField_iff J y).2 hyJ
  set yM : M := ⟨y, hyM⟩
  set sM : M := σ₁.restrictNormal M yM
  have hsM : (sM : L) = σ₁ y := AlgEquiv.restrictNormal_commutes σ₁ M yM
  have hpF : (p : F) ^ r ≠ 0 := by
    intro h; apply hpr
    have := congrArg (algebraMap F L) h
    simpa using this
  set kF : F := (a σ₁ : F) / (p : F) ^ r
  set zM : M := (p : M) ^ 2 * (algebraMap F M kF - (sM - yM))
  have hzL : (zM : L) = σ₁ ((p : L) ^ 2 * (x / (p : L) ^ r - y)) - (p : L) ^ 2 * (x / (p : L) ^ r - y)
      - (p : L) ^ 2 * z₁ := by
    have h1 : (algebraMap F L kF) = (a σ₁ : L) / (p : L) ^ r := by
      simp [kF]
    have h2 : σ₁ (x / (p : L) ^ r) = x / (p : L) ^ r + (a σ₁ : L) / (p : L) ^ r + z₁ := by
      have := hdiff σ₁
      rw [e₁, add_div, mul_div_cancel_left₀ _ hpr] at this
      linear_combination this
    have h3 : (zM : L) = (p : L) ^ 2 * (algebraMap F L kF - (σ₁ y - y)) := by
      simp only [zM, MulMemClass.coe_mul, SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub,
        IntermediateField.coe_algebraMap_apply, hsM]
      simp [yM]
    rw [h3, map_mul, map_sub, map_pow, map_natCast, h2, h1]
    ring
  have hzO : (zM : L) ∈ 𝒪[L] := by
    rw [hzL]
    exact sub_mem (sub_mem (hσO σ₁ _ hw) hw) (mul_mem (pow_mem (natCast_mem _ p) 2) hz₁)
  have hfin : Module.finrank F M = J.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index, hMdef, IntermediateField.fixingSubgroup_fixedField]
  refine ⟨⟨zM, ?_⟩, ?_⟩
  · rw [Valuation.mem_integer_iff] at hzO ⊢
    have hmono := ValuativeExtension.mapValueGroupWithZero_strictMono (A := M) (B := L)
    rw [IntermediateField.valuation_coe, ← map_one (ValuativeExtension.mapValueGroupWithZero M L)] at hzO
    exact hmono.le_iff_le.mp hzO
  · have hz : zM = algebraMap F M ((p : F) ^ 2 * kF) - algebraMap F M ((p : F) ^ 2) * (sM - yM) := by
      simp only [zM, map_mul, map_pow, map_natCast]; ring
    have htr : Algebra.trace F M sM = Algebra.trace F M yM := Algebra.trace_eq_of_algEquiv (σ₁.restrictNormal M) yM
    show Algebra.trace F M zM = _
    rw [hz, map_sub, Algebra.trace_algebraMap, ← Algebra.smul_def, LinearMap.map_smul, map_sub, htr, sub_self,
      smul_zero, sub_zero, hfin, nsmul_eq_mul]
    have hcF : (c : F) * (p : F) ^ r = (J.index : F) * (a σ₁ : F) := by exact_mod_cast congrArg (fun t : ℤ => (t : F)) hc
    have hk : (J.index : F) * kF = c := by
      simp only [kF]
      rw [mul_div_assoc', div_eq_iff hpF]
      linear_combination -hcF
    linear_combination (p : F) ^ 2 * hk
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_fixedField_trace_eq_sq_mul_of_ax : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p r : ℕ) (x : L) (a : (L ≃ₐ[F] L) → ℤ) (J : Subgroup (L ≃ₐ[F] L)) [J.Normal] (σ₁ : L ≃ₐ[F] L) (c : ℤ), (p : L) ≠ 0 → AxIn F L p → (∀ σ : L ≃ₐ[F] L, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → (∀ σ ∈ J, (p : ℤ) ^ r ∣ a σ) → c * (p : ℤ) ^ r = (J.index : ℤ) * a σ₁ → ∃ z : 𝒪[↥(IntermediateField.fixedField J)], Algebra.trace F ↥(IntermediateField.fixedField J) (z : ↥(IntermediateField.fixedField J)) = (p : F) ^ 2 * (c : F) := by
  atlas_forward_decl GlobalTheory.PMon.Ram.exists_integer_fixedField_trace_eq
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_kernel_le_six_mul :
    ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E r : ℕ) (x : L) (a : (L ≃ₐ[F] L) → ℤ), p.Prime → 0 < E → OrdIs L p E → AxIn F L p → (∀ σ : L ≃ₐ[F] L, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → (∃ σ, ¬ (p : ℤ) ^ r ∣ a σ) → ∃ J : Subgroup (L ≃ₐ[F] L), (∀ σ, σ ∈ J ↔ (p : ℤ) ^ r ∣ a σ) ∧ jumpSum (wild F L) ⊤ J ≤ 6 * E := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E r x a hp hE hord hax hx hne
  have hadd : ∀ σ τ : L ≃ₐ[F] L, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ := fun σ τ =>
    GlobalTheory.T.integer_coboundary_additive_mod_prime_pow F L p E r ⊤ x a hp hE hord (fun σ _ => hx σ) σ (Subgroup.mem_top _) τ (Subgroup.mem_top _)
  obtain ⟨J, hJn, σ₁, c, hJ, hc, hpc⟩ := GlobalTheory.T.character_mod_prime_pow_kernel_generator (L ≃ₐ[F] L) p r a hp hadd hne
  refine ⟨J, hJ, ?_⟩

  have hp0 : (p : L) ≠ 0 := by
    intro h0
    have h1 : ((p : 𝒪[L]) : L) = 0 := by simpa using h0
    have h2 : (p : 𝒪[L]) = 0 := Subtype.ext (by simpa using h1)
    unfold OrdIs at hord
    rw [h2, AddValuation.map_zero] at hord
    exact ENat.top_ne_coe E hord
  set M := IntermediateField.fixedField J with hM
  haveI : IsGalois F M := IsGalois.of_fixedField_normal_subgroup J
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_integer_fixedField_trace_eq_sq_mul_of_ax F L p r x a J σ₁ c hp0 hax hx (fun σ hσ => (hJ σ).1 hσ) hc
  obtain ⟨e, hordF, hEe, -⟩ := GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension F L p E hord
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at hEe; omega
    · exact h

  have hdM : differentExponent F M < ramificationIndex F M * (3 * e) := by
    by_contra hle
    push_neg at hle
    obtain ⟨w, hw, hwt⟩ := GlobalTheory.T.exists_trace_mem_maximalIdeal_pow_of_differentExponent F M (3 * e) hle z
    exact GlobalTheory.T.sq_mul_not_mem_maximalIdeal_pow_three_mul F p e c hp he hordF hpc w hw (hwt.trans hz)
  have htow := differentExponent_tower F M L
  have hram := ramificationIndex_tower F M L
  have hjs : jumpSum (wild F L) ⊤ J + 2 * differentExponent M L ≤ 2 * differentExponent F L := GlobalTheory.T.ramificationJumpSum_add_two_mul_differentExponent_le F L J
  have key : jumpSum (wild F L) ⊤ J ≤ 2 * (ramificationIndex M L * differentExponent F M) := by omega
  have hML : ramificationIndex M L * differentExponent F M ≤ ramificationIndex M L * (ramificationIndex F M * (3 * e)) :=
    Nat.mul_le_mul_left _ hdM.le
  have : ramificationIndex M L * (ramificationIndex F M * (3 * e)) * 2 = 6 * E := by
    rw [hEe, hram]; ring
  nlinarith

end GlobalTheory.PMon.Ram
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jumpSum_kernel_coboundaryChar_le_six_mul : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E r : ℕ) (x : L) (a : (L ≃ₐ[F] L) → ℤ), p.Prime → 0 < E → OrdIs L p E → AxIn F L p → (∀ σ : L ≃ₐ[F] L, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → (∃ σ, ¬ (p : ℤ) ^ r ∣ a σ) → ∃ J : Subgroup (L ≃ₐ[F] L), (∀ σ, σ ∈ J ↔ (p : ℤ) ^ r ∣ a σ) ∧ jumpSum (wild F L) ⊤ J ≤ 6 * E := by
  atlas_forward_decl GlobalTheory.PMon.Ram.jumpSum_kernel_le_six_mul
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

open Classical in

theorem jumpSum_mono_of_le :
    ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R → (∃ m, R m = ⊥) →
      (∀ t, A ⊓ R t ≤ C → A ⊓ R t ≤ B) → jumpSum R A B ≤ jumpSum R A C := by
  intro G _ R A B C hR ⟨m, hm⟩ hBC
  have hbot : ∀ t, m ≤ t → ∀ D : Subgroup G, A ⊓ R t ≤ D := by
    intro t ht D
    have : R t ≤ ⊥ := hm ▸ hR ht
    exact le_trans inf_le_right (le_trans this bot_le)
  have hfin : ∀ D : Subgroup G,
      (Function.support fun t : ℕ => if A ⊓ R t ≤ D then 0 else Nat.card ↥(A ⊓ R t)) ⊆ ↑(Finset.range m) := by
    intro D
    intro t ht
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply ht
    simp [hbot t (not_lt.mp h) D]
  unfold jumpSum
  rw [finsum_eq_sum_of_support_subset _ (hfin B), finsum_eq_sum_of_support_subset _ (hfin C)]
  apply Finset.sum_le_sum
  intro t _
  by_cases hC : A ⊓ R t ≤ C
  · simp [hBC t hC]
  · rw [if_neg hC]
    split_ifs <;> simp

end GlobalTheory.PMon.Ram
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationJumpSum_mono_of_le : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R → (∃ m, R m = ⊥) → (∀ t, A ⊓ R t ≤ C → A ⊓ R t ≤ B) → jumpSum R A B ≤ jumpSum R A C := by
  atlas_forward_decl GlobalTheory.PMon.Ram.jumpSum_mono_of_le
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_wild_top_le_of_detects : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E r : ℕ) (B : Subgroup (L ≃ₐ[F] L)), p.Prime → 0 < E → OrdIs L p E → AxIn F L p → Detects p r ⊤ B → jumpSum (wild F L) ⊤ B ≤ 6 * E := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E r B hp hE hord hax hdet
  obtain ⟨hanti, hbot⟩ := GlobalTheory.T.wildLowerRamificationGroup_antitone_eventually_bot F L
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_initialSegment_not_inf_le_filtration _ (wild F L) ⊤ B hanti hbot
  rcases n with _ | k
  · rw [GlobalTheory.T.ramificationJumpSum_eq_sum_range _ (wild F L) ⊤ B 0 hanti hn]
    simp
  · have hk : ¬ (⊤ : Subgroup (L ≃ₐ[F] L)) ⊓ wild F L k ≤ B := (hn k).1 (Nat.lt_succ_self k)
    obtain ⟨σ₀, hσ₀, hσ₀B⟩ := SetLike.not_le_iff_exists.1 hk
    have hσ₀k : σ₀ ∈ wild F L k := (Subgroup.mem_inf.1 hσ₀).2
    obtain ⟨x, a, hxa, hnd⟩ := hdet σ₀ (Subgroup.mem_top σ₀) hσ₀B
    obtain ⟨J, hJ, hJsum⟩ := GlobalTheory.T.jumpSum_kernel_coboundaryChar_le_six_mul F L p E r x a hp hE hord hax
      (fun σ => hxa σ (Subgroup.mem_top σ)) ⟨σ₀, hnd⟩
    have hσ₀J : σ₀ ∉ J := fun h => hnd ((hJ σ₀).1 h)
    have hmono : ∀ t, (⊤ : Subgroup (L ≃ₐ[F] L)) ⊓ wild F L t ≤ J → (⊤ : Subgroup (L ≃ₐ[F] L)) ⊓ wild F L t ≤ B := by
      intro t ht
      by_contra hB
      have htk : t ≤ k := Nat.lt_succ_iff.1 ((hn t).2 hB)
      have hσ₀t : σ₀ ∈ wild F L t := hanti htk hσ₀k
      exact hσ₀J (ht (Subgroup.mem_inf.2 ⟨Subgroup.mem_top σ₀, hσ₀t⟩))
    exact le_trans (GlobalTheory.T.ramificationJumpSum_mono_of_le _ (wild F L) ⊤ B J hanti hbot hmono) hJsum

end GlobalTheory.PMon.Ram
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wild_jumpSum_le_of_coboundary_detects : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E r : ℕ) (B : Subgroup (L ≃ₐ[F] L)), p.Prime → 0 < E → OrdIs L p E → AxIn F L p → Detects p r ⊤ B → jumpSum (wild F L) ⊤ B ≤ 6 * E := by
  atlas_forward_decl GlobalTheory.PMon.Ram.jumpSum_wild_top_le_of_detects
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_le_of_detects : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → AxIn K L p → Detects p r A B → jumpSum (wild K L) A B ≤ 6 * E := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E r A B hp hE hord hax hdet
  obtain ⟨j, hinj, hrange, happ, hram⟩ := GlobalTheory.T.galoisGroup_fixedField_baseChange_localField K L A

  have haxF : AxIn (IntermediateField.fixedField A) L p := by
    intro J x hx
    obtain ⟨y, hy, hxy⟩ := hax (J.map j) x (by
      rintro σ ⟨τ, hτ, rfl⟩
      rw [happ]
      exact hx τ hτ)
    refine ⟨y, fun τ hτ => ?_, hxy⟩
    rw [← happ]
    exact hy (j τ) ⟨τ, hτ, rfl⟩
  have hdetF : Detects p r ⊤ (B.comap j) := by
    intro τ₀ _ hτ₀
    have hA : j τ₀ ∈ A := hrange.le (MonoidHom.mem_range.mpr ⟨τ₀, rfl⟩)
    obtain ⟨x, a, hxa, hnd⟩ := hdet (j τ₀) hA hτ₀
    refine ⟨x, fun τ => a (j τ), fun τ _ => ?_, hnd⟩
    obtain ⟨z, hz, hzx⟩ := hxa (j τ) (hrange.le (MonoidHom.mem_range.mpr ⟨τ, rfl⟩))
    refine ⟨z, hz, ?_⟩
    rw [← happ]
    exact hzx
  have key := GlobalTheory.T.wild_jumpSum_le_of_coboundary_detects (IntermediateField.fixedField A) L p E r (B.comap j) hp hE hord haxF hdetF
  have hwild : wild (IntermediateField.fixedField A) L = fun t => (wild K L t).comap j := by
    funext t
    exact hram _
  rw [hwild, jumpSum_comap_injective _ _ j _ B hinj, hrange] at key
  exact key

end GlobalTheory.PMon.Ram
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wildJumpSum_le_of_detecting_coboundary_characters : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → AxIn K L p → Detects p r A B → jumpSum (wild K L) A B ≤ 6 * E := by
  atlas_forward_decl GlobalTheory.PMon.Ram.jumpSum_le_of_detects
end
