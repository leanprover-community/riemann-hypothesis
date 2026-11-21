import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DividedPowersValuations
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClearsIdempotentOfExponentBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDifferentExponentDenominator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFifth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodDenominatorBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodConjugateIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodProductIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledRestrictionEndomorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodTraceIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodNormIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodGaloisIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowersPrimeUnique

section
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.CondAway

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isUnit_absNorm_of_not_mem (q : HeightOneSpectrum (OF E)) (l : ℕ) (hl : l.Prime)
    (hq : (l : OF E) ∉ q.asIdeal) (O : Type) [CommRing O] [IsLocalRing O]
    (hlO : (l : O) ∈ IsLocalRing.maximalIdeal O) : IsUnit ((Ideal.absNorm q.asIdeal : ℕ) : O) := by
  haveI : Finite (OF E ⧸ q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ q.ne_bot
  haveI := q.isMaximal
  letI : Field (OF E ⧸ q.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (OF E ⧸ q.asIdeal) := Fintype.ofFinite _
  obtain ⟨n, hp, hcard⟩ := FiniteField.card (OF E ⧸ q.asIdeal) (ringChar (OF E ⧸ q.asIdeal))
  set p := ringChar (OF E ⧸ q.asIdeal)
  have hN : Ideal.absNorm q.asIdeal = p ^ (n : ℕ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]
  have hpl : p ≠ l := by
    intro h
    apply hq
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h]
    exact ringChar.Nat.cast_ringChar
  by_contra hu
  have hmem : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
    have : ((p : ℕ) : O) ^ (n : ℕ) ∈ IsLocalRing.maximalIdeal O := by
      rw [← Nat.cast_pow, ← hN]; exact (IsLocalRing.mem_maximalIdeal _).2 hu
    exact (IsLocalRing.maximalIdeal.isMaximal O).isPrime.mem_of_pow_mem _ this
  have hcop : IsCoprime (p : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hpl)
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    have := congrArg (Int.cast : ℤ → O) huv
    push_cast at this
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hlO)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem coordAt_rTensor (O : Type) [CommRing O] {K : Type} [Field K] [Algebra O K] {c c' : Ideal (OF E)} (s : E)
    (g : orderC c →ₗ[ℤ] orderC c') (hg : ∀ x, (g x : E) = s * x) (σ : E →+* K) (t : orderC c ⊗[ℤ] O) :
    coordAt O c' σ (g.rTensor O t) = σ s * coordAt O c σ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [LinearMap.rTensor_tmul]
    show σ (g a) * algebraMap O K x = σ s * (σ a * algebraMap O K x)
    rw [hg, map_mul, mul_assoc]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]

theorem clearsIdem_condQ_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E))
    (Q : Finset (HeightOneSpectrum (OF E))) (l : ℕ), l.Prime → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ D : O,
    ClearsIdem K (condQ 𝔣 Q) D ↔ ClearsIdem K 𝔣 D := by
  intro E _ _ _ 𝔣 Q l hl hQ O _ _ _ _ K _ _ _ hlO D
  have hle : condQ 𝔣 Q ≤ 𝔣 := Ideal.mul_le_inf.trans inf_le_left
  constructor
  · intro h σ
    obtain ⟨t, ht⟩ := h σ
    let g : orderC (condQ 𝔣 Q) →ₗ[ℤ] orderC 𝔣 := AddMonoidHom.toIntLinearMap
      { toFun := fun x => ⟨(1 : E) * x, by rw [one_mul]; exact orderC_mono hle x.2⟩,
        map_zero' := Subtype.ext (by simp), map_add' := fun x y => Subtype.ext (by simp [mul_add]) }
    refine ⟨g.rTensor O t, fun σ' => ?_⟩
    rw [coordAt_rTensor O (1 : E) g (fun x => rfl), map_one, one_mul, ht]
  · intro h σ
    obtain ⟨t, ht⟩ := h σ
    set m : ℕ := ∏ q ∈ Q, Ideal.absNorm q.asIdeal with hm
    have hmI : (m : OF E) ∈ ∏ q ∈ Q, q.asIdeal := by
      rw [hm, Nat.cast_prod]
      exact Ideal.prod_mem_prod fun q _ => Ideal.absNorm_mem q.asIdeal
    have hmul : ∀ x ∈ orderC 𝔣, (m : E) * x ∈ orderC (condQ 𝔣 Q) := by
      intro x hx
      obtain ⟨a, b, hb, rfl⟩ := mem_orderC.1 hx
      refine mem_orderC.2 ⟨m * a, b * algebraMap (OF E) (𝓞 E) m, ?_, ?_⟩
      · rw [condQ, Ideal.map_mul]
        exact Ideal.mul_mem_mul hb (Ideal.mem_map_of_mem _ hmI)
      · simp only [map_mul, map_natCast]
        ring
    let g : orderC 𝔣 →ₗ[ℤ] orderC (condQ 𝔣 Q) := AddMonoidHom.toIntLinearMap
      { toFun := fun x => ⟨(m : E) * x, hmul x x.2⟩,
        map_zero' := Subtype.ext (by simp), map_add' := fun x y => Subtype.ext (by simp [mul_add]) }
    have hu : IsUnit (m : O) := by
      rw [hm, Nat.cast_prod]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
        (fun q hq => isUnit_absNorm_of_not_mem q l hl (hQ q hq) O hlO)
    obtain ⟨u, hu'⟩ := hu.exists_left_inv
    refine ⟨g.rTensor O t * (1 ⊗ₜ u), fun σ' => ?_⟩
    rw [map_mul, coordAt_rTensor O (m : E) g (fun x => rfl), ht]
    have h1 : coordAt O (condQ 𝔣 Q) σ' (1 ⊗ₜ u) = algebraMap O K u := by
      show σ' ((1 : orderC (condQ 𝔣 Q)) : E) * algebraMap O K u = _
      simp
    have h2 : algebraMap O K u * (m : K) = 1 := by
      rw [← map_natCast (algebraMap O K), ← map_mul, hu', map_one]
    rw [h1, map_natCast]
    split_ifs
    · linear_combination (algebraMap O K D) * h2
    · simp

end GlobalTheory.CondAway
end
end

open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clears_idempotent_conductor_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (l : ℕ), l.Prime → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ D : O, ClearsIdem K (condQ 𝔣 Q) D ↔ ClearsIdem K 𝔣 D := by
  atlas_forward_decl GlobalTheory.CondAway.clearsIdem_condQ_iff
end

section
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.DualCrit

theorem trace_eq_sum_ringHom {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K]
    [Fintype (E →+* K)] (hcard : Fintype.card (E →+* K) = Module.finrank ℚ E) (x : E) :
    algebraMap ℚ K (Algebra.trace ℚ E x) = ∑ σ : E →+* K, σ x := by
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  apply ι.injective
  rw [map_sum]
  have hq : ι.comp (algebraMap ℚ K) = algebraMap ℚ (AlgebraicClosure K) := RingHom.ext_rat _ _
  rw [← RingHom.comp_apply, hq, trace_eq_sum_embeddings (AlgebraicClosure K)]
  let f : (E →+* K) → (E →ₐ[ℚ] AlgebraicClosure K) := fun σ => (ι.comp σ).toRatAlgHom
  have hinj : Function.Injective f := by
    intro σ σ' h
    ext y
    apply ι.injective
    exact congrArg (fun g : E →ₐ[ℚ] AlgebraicClosure K => g y) h
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [hcard, AlgHom.card]
  exact (Fintype.sum_bijective f hbij (fun σ => ι (σ x)) (fun τ => τ x) (fun σ => rfl)).symm

theorem sum_basis_mul_dual {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K]
    [Fintype (E →+* K)] (hcard : Fintype.card (E →+* K) = Module.finrank ℚ E)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (σ σ' : E →+* K) :
    ∑ j, σ' (b j) * σ ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b j) =
      if σ' = σ then 1 else 0 := by
  set bd := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b
  let A : Matrix ι (E →+* K) K := fun j τ => τ (b j)
  let B : Matrix (E →+* K) ι K := fun τ k => τ (bd k)
  have hAB : A * B = 1 := by
    ext j k
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [A, B]
    rw [show (∑ τ : E →+* K, τ (b j) * τ (bd k)) = ∑ τ : E →+* K, τ (bd k * b j) from
      Finset.sum_congr rfl fun τ _ => by rw [map_mul, mul_comm]]
    rw [← trace_eq_sum_ringHom hcard, ← Algebra.traceForm_apply,
      LinearMap.BilinForm.apply_dualBasis_left]
    split_ifs <;> simp
  have e : ι ≃ (E →+* K) := Fintype.equivOfCardEq (by rw [hcard, Module.finrank_eq_card_basis b])
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hAB
  have h := congrFun (congrFun hBA σ) σ'
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simp only [A, B] at h
  calc _ = ∑ k, σ (bd k) * σ' (b k) := Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ = _ := by rw [h]; exact if_congr eq_comm rfl rfl

theorem clearsIdem_top_of_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], Nat.card (E →+* K) = Module.finrank ℚ E → ∀ D : O, (∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = algebraMap O K D * σ y) → ClearsIdem K (⊤ : Ideal (OF E)) D := by
  intro E _ _ _ O _ _ _ _ K _ _ _ hcard D hD σ
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective O K)
  haveI : Finite (E →+* K) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')
  letI : Fintype (E →+* K) := Fintype.ofFinite _
  have hcard' : Fintype.card (E →+* K) = Module.finrank ℚ E := by
    rw [← Nat.card_eq_fintype_card, hcard]
  set b := RingOfIntegers.basis E
  set bQ := integralBasis E
  set bd := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) bQ
  have hint : ∀ j (x : 𝓞 E), ∃ n : ℤ, Algebra.trace ℚ E (bd j * x) = n := by
    intro j x
    refine ⟨b.repr x j, ?_⟩
    have h1 : Algebra.trace ℚ E (bd j * x) = bQ.repr (x : E) j := by
      rw [← Algebra.traceForm_apply]
      conv_lhs => rw [← bQ.sum_repr (x : E)]
      rw [map_sum]
      simp only [bd, map_smul, LinearMap.BilinForm.apply_dualBasis_left, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h1]
    exact (integralBasis_repr_apply E x j).trans (eq_intCast _ _)
  choose z hz using fun j => hD σ (bd j) (hint j)
  have hmem : ∀ j, ((b j : 𝓞 E) : E) ∈ orderC (⊤ : Ideal (OF E)) := fun j =>
    mem_orderC.2 ⟨0, b j, by rw [Ideal.map_top]; exact Submodule.mem_top, by simp⟩
  refine ⟨∑ j, (⟨((b j : 𝓞 E) : E), hmem j⟩ : orderC (⊤ : Ideal (OF E))) ⊗ₜ[ℤ] z j, fun σ' => ?_⟩
  have hc : ∀ j, coordAt O (⊤ : Ideal (OF E)) σ'
      ((⟨((b j : 𝓞 E) : E), hmem j⟩ : orderC (⊤ : Ideal (OF E))) ⊗ₜ[ℤ] z j) =
        algebraMap O K D * (σ' (bQ j) * σ (bd j)) := by
    intro j
    show σ' ((b j : 𝓞 E) : E) * algebraMap O K (z j) = _
    rw [hz j, integralBasis_apply]
    simp only [b]
    rw [← RingOfIntegers.coe_eq_algebraMap]
    ring
  rw [map_sum, Finset.sum_congr rfl fun j _ => hc j, ← Finset.mul_sum, sum_basis_mul_dual hcard' bQ σ σ']
  split_ifs <;> simp

end GlobalTheory.DualCrit
end
end

open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clears_idempotent_of_trace_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], Nat.card (E →+* K) = Module.finrank ℚ E → ∀ D : O, (∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = algebraMap O K D * σ y) → ClearsIdem K (⊤ : Ideal (OF E)) D := by
  atlas_forward_decl GlobalTheory.DualCrit.clearsIdem_top_of_dual
end

section
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory

theorem traceDual_integral_of_not_dvd_discr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime → ¬ (l : ℤ) ∣ discr E → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = σ y := by
  intro E _ _ _ l hl hd O _ _ _ _ K _ _ _ hlm σ y hy

  have hmem : y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨x, rfl⟩ := Submodule.mem_one.mp ha
    obtain ⟨k, hk⟩ := hy x
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, hk]
    simp
  have hb : ∀ i, IsIntegral ℤ (integralBasis E i) := fun i => by
    rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
  have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hint0 := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) hb h1 hmem
  rw [← coe_discr, Algebra.smul_def, mul_one] at hint0
  have hint : IsIntegral ℤ ((NumberField.discr E : E) * y) := by simpa using hint0

  have hσ : IsIntegral ℤ (σ ((NumberField.discr E : E) * y)) := hint.map σ.toIntAlgHom
  have hO : IsIntegral O (σ ((NumberField.discr E : E) * y)) := hσ.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hO

  have hcop : IsCoprime (l : ℤ) (NumberField.discr E) :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hl).irreducible).mpr hd
  obtain ⟨a, b, hab⟩ := hcop
  have hu : IsUnit ((NumberField.discr E : ℤ) : O) := by
    by_contra hn
    have hdm : ((NumberField.discr E : ℤ) : O) ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr hn
    have hlm' : ((l : ℤ) : O) ∈ IsLocalRing.maximalIdeal O := by simpa using hlm
    have h1m : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have : ((a : O) * ((l : ℤ) : O) + (b : O) * ((NumberField.discr E : ℤ) : O)) = 1 := by
        exact_mod_cast congrArg (Int.cast (R := O)) hab
      rw [← this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlm') (Ideal.mul_mem_left _ _ hdm)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1m)
  obtain ⟨u, hu'⟩ := hu
  refine ⟨(u⁻¹ : Oˣ) * z, ?_⟩
  rw [map_mul, hz, map_mul, map_intCast, ← map_intCast (algebraMap O K), ← hu', ← mul_assoc,
    ← map_mul, Units.inv_mul, map_one, one_mul]

end GlobalTheory
end

open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_of_trace_dual_element : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime → ¬ (l : ℤ) ∣ discr E → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = σ y := by
  atlas_forward_decl GlobalTheory.traceDual_integral_of_not_dvd_discr
end

section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_different_exponent_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∃ D : O, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → val_vp O l (algebraMap O K D) = ((diffExp_vp l P : ℚ) : WithTop ℚ)) ∧ ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = algebraMap O K D * σ y := by
  first | exact @GlobalTheory.DifferentElement.diff_element | exact GlobalTheory.DifferentElement.diff_element | (intros; apply GlobalTheory.DifferentElement.diff_element <;> assumption)
end

section
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory

theorem val_vp_natCast_pow (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K]
    [Algebra O K] [IsFractionRing O K] (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) (k : ℕ) :
    val_vp O l (algebraMap O K ((l : O) ^ k)) = ((k : ℚ) : WithTop ℚ) := by
  have h0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap O K)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (Nat.cast_ne_zero.2 hl)
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) < 1 := by
    rw [← map_natCast (algebraMap O K), HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact h
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) ≠ 0 := by simpa using h0
  have h3 : ord_vw O (l : K) ≠ 0 := by
    unfold ord_vw
    intro h4
    have := WithZero.exp_log h2
    rw [neg_eq_zero.1 h4, WithZero.exp_zero] at this
    exact h1.ne this.symm
  have hpow : algebraMap O K ((l : O) ^ k) = (l : K) ^ k := by simp
  have hk : ord_vw O ((l : K) ^ k) = k * ord_vw O (l : K) := by
    unfold ord_vw
    rw [map_pow, WithZero.log_pow, nsmul_eq_mul]
    ring
  rw [hpow, val_vp, if_neg (pow_ne_zero k h0), hk]
  congr 1
  push_cast
  field_simp

end GlobalTheory
end

open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_pow_eq_alt : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], ∀ (l : ℕ), l ≠ 0 → (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ k : ℕ, val_vp O l (algebraMap O K ((l : O) ^ k)) = ((k : ℚ) : WithTop ℚ) := by
  atlas_forward_decl GlobalTheory.val_vp_natCast_pow
end

section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_period_integral_first : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ) := by
  first | exact @GlobalTheory.EigLineSum.eigK_isInternal | exact GlobalTheory.EigLineSum.eigK_isInternal | (intros; apply GlobalTheory.EigLineSum.eigK_isInternal <;> assumption)
end

section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_period_integral_second : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ σ : E →+* K, IsSat (eigLat ρ σ) ∧ (∃ g : H, g ≠ 0 ∧ eigLat ρ σ = O ∙ g) ∧ Module.Free O (eigLat ρ σ) ∧ Module.finrank O (eigLat ρ σ) = 1 ∧ ∃ C : Submodule O H, IsCompl (eigLat ρ σ) C := by
  first | exact @GlobalTheory.EigenLattice.main | exact GlobalTheory.EigenLattice.main | (intros; apply GlobalTheory.EigenLattice.main <;> assumption)
end

section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_period_integral_third : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ) → iSupIndep (fun σ : E →+* K => eigLat ρ σ) ∧ ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ := by
  first | exact @GlobalTheory.EigenLattice.iSupIndep_and_smul_mem_iSup | exact GlobalTheory.EigenLattice.iSupIndep_and_smul_mem_iSup | (intros; apply GlobalTheory.EigenLattice.iSupIndep_and_smul_mem_iSup <;> assumption)
end

section
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.Div.cm_type_period_integral_fourth

theorem exists_smul_mem_of_tmul_mem_baseChange {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K]
    [IsFractionRing O K] {H : Type} [AddCommGroup H] [Module O H] (Fil : Submodule O H) (h : H)
    (hh : (1 : K) ⊗ₜ[O] h ∈ Fil.baseChange K) : ∃ d : O, d ≠ 0 ∧ d • h ∈ Fil := by
  have key : ∀ x ∈ Fil.baseChange K, ∃ s : O, s ≠ 0 ∧ ∃ f ∈ Fil, algebraMap O K s • x = (1 : K) ⊗ₜ[O] f := by
    intro x hx
    rw [Submodule.baseChange_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      exact ⟨1, one_ne_zero, f, hf, by simp⟩
    | zero => exact ⟨1, one_ne_zero, 0, Fil.zero_mem, by simp⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨s, hs, f, hf, e⟩ := ihx
      obtain ⟨t, ht, g, hg, e'⟩ := ihy
      refine ⟨s * t, mul_ne_zero hs ht, t • f + s • g, Fil.add_mem (Fil.smul_mem _ hf) (Fil.smul_mem _ hg), ?_⟩
      simp only [map_mul, smul_add, mul_smul]
      rw [smul_comm (algebraMap O K s) (algebraMap O K t) x, e, e', TensorProduct.tmul_add,
        TensorProduct.tmul_smul, TensorProduct.tmul_smul, algebraMap_smul, algebraMap_smul]
    | smul k x _ ihx =>
      obtain ⟨s, hs, f, hf, e⟩ := ihx
      obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) k
      have hb : (b : O) ≠ 0 := nonZeroDivisors.ne_zero b.2
      refine ⟨b * s, mul_ne_zero hb hs, a • f, Fil.smul_mem _ hf, ?_⟩
      rw [← mul_smul, map_mul, mul_assoc, mul_comm (algebraMap O K s), ← mul_assoc,
        mul_comm (algebraMap O K (b : O)), IsLocalization.mk'_spec, mul_smul, e, TensorProduct.tmul_smul,
        algebraMap_smul]
  obtain ⟨s, hs, f, hf, e⟩ := key _ hh
  have hloc : IsLocalizedModule (nonZeroDivisors O) (TensorProduct.mk O K H 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K _).2 (TensorProduct.isBaseChange O H K)
  have h0 : TensorProduct.mk O K H 1 (s • h - f) = 0 := by
    rw [map_sub, map_smul, TensorProduct.mk_apply, TensorProduct.mk_apply, ← algebraMap_smul K, e, sub_self]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors O) _).1 h0
  refine ⟨(t : O) * s, mul_ne_zero (nonZeroDivisors.ne_zero t.2) hs, ?_⟩
  have : (t : O) • (s • h) = (t : O) • f := by
    rw [Submonoid.smul_def, smul_sub, sub_eq_zero] at ht
    exact ht
  rw [mul_smul, this]
  exact Fil.smul_mem _ hf

theorem fil_inf_eigLat_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ i, Fil ⊓ eigLat ρ (φ i) = eigLat ρ (φ i) := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hL i
  refine inf_eq_right.2 fun h hh => ?_
  obtain ⟨-, -, -, -, hsat, hbc, -⟩ := hL
  have h1 : inK K H h ∈ Fil.baseChange K := by
    rw [hbc]
    exact le_iSup (fun j => eigK ρ (φ j)) i hh
  obtain ⟨d, hd, hdh⟩ := exists_smul_mem_of_tmul_mem_baseChange Fil h h1
  exact hsat d h hd hdh

end GlobalTheory.Div.cm_type_period_integral_fourth
end

open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_period_integral_fourth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ i, Fil ⊓ eigLat ρ (φ i) = eigLat ρ (φ i) := by
  atlas_forward_decl GlobalTheory.Div.cm_type_period_integral_fourth.fil_inf_eigLat_cmType
end

section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_period_integral_fifth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ σ σ' : E →+* K, σ' ≠ bar σ → ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', B.baseChange K x y = 0 := by
  first | exact @GlobalTheory.EigenPair.pairing_eig_eq_zero | exact GlobalTheory.EigenPair.pairing_eig_eq_zero | (intros; apply GlobalTheory.EigenPair.pairing_eig_eq_zero <;> assumption)
end

section
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory

theorem inK_injective_of_free {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K] (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] :
    Function.Injective (inK K H : H →ₗ[O] K ⊗[O] H) := by
  have h1 : Function.Injective ((Algebra.linearMap O K).rTensor H) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective O K)
  intro x y hxy
  apply (TensorProduct.lid O H).symm.injective
  apply h1
  simpa [inK] using hxy

theorem existsUnique_endo_line {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    (W : ι → Submodule K V) (hW : DirectSum.IsInternal W) (τ : ι) (v w : V) (hv : v ∈ W τ) (hv0 : v ≠ 0)
    (h1 : Module.finrank K (W τ) = 1) :
    ∃! N : Module.End K V, N v = w ∧ ∀ σ, σ ≠ τ → ∀ x ∈ W σ, N x = 0 := by
  have hspan : ∀ x ∈ W τ, ∃ c : K, c • v = x := by
    intro x hx
    have hu : (⟨v, hv⟩ : W τ) ≠ 0 := by simpa using hv0
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : W τ) hu).1 h1 ⟨x, hx⟩
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩
  have hind := hW.submodule_iSupIndep
  have htop := hW.submodule_iSup_eq_top
  set C : Submodule K V := ⨆ j, ⨆ (_ : j ≠ τ), W j with hC
  have hmemC : ∀ σ, σ ≠ τ → ∀ x ∈ W σ, x ∈ C := fun σ hσ x hx =>
    (le_iSup₂_of_le σ hσ le_rfl : W σ ≤ C) hx
  have hc : IsCompl (W τ) C := by
    refine ⟨hind τ, codisjoint_iff.2 (eq_top_iff.2 ?_)⟩
    rw [← htop]
    refine iSup_le fun j => ?_
    by_cases hj : j = τ
    · subst hj; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le j hj le_rfl)
  have huniq : ∀ N₁ N₂ : Module.End K V, (N₁ v = w ∧ ∀ σ, σ ≠ τ → ∀ x ∈ W σ, N₁ x = 0) →
      (N₂ v = w ∧ ∀ σ, σ ≠ τ → ∀ x ∈ W σ, N₂ x = 0) → N₁ = N₂ := by
    intro N₁ N₂ h₁ h₂
    have hle : ∀ σ, W σ ≤ LinearMap.eqLocus N₁ N₂ := by
      intro σ x hx
      show N₁ x = N₂ x
      by_cases hσ : σ = τ
      · subst hσ
        obtain ⟨c, rfl⟩ := hspan x hx
        rw [map_smul, map_smul, h₁.1, h₂.1]
      · rw [h₁.2 σ hσ x hx, h₂.2 σ hσ x hx]
    have : (⊤ : Submodule K V) ≤ LinearMap.eqLocus N₁ N₂ := htop ▸ iSup_le hle
    exact LinearMap.ext fun x => this (Submodule.mem_top)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.toSpanSingleton K V v)
    (LinearMap.ker_toSpanSingleton K hv0)
  let p := Submodule.linearProjOfIsCompl (W τ) C hc
  have hN0 : ((LinearMap.toSpanSingleton K V w) ∘ₗ g ∘ₗ (W τ).subtype ∘ₗ p) v = w ∧
      ∀ σ, σ ≠ τ → ∀ x ∈ W σ, ((LinearMap.toSpanSingleton K V w) ∘ₗ g ∘ₗ (W τ).subtype ∘ₗ p) x = 0 := by
    constructor
    · have hpv : p v = ⟨v, hv⟩ := Submodule.linearProjOfIsCompl_apply_left hc ⟨v, hv⟩
      have hgv : g v = 1 := by simpa using LinearMap.congr_fun hg 1
      simp [hpv, hgv]
    · intro σ hσ x hx
      have : p x = 0 := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).2 (hmemC σ hσ x hx)
      simp [this]
  exact ⟨_, hN0, fun N hN => huniq _ _ hN hN0⟩
end GlobalTheory

namespace GlobalTheory

theorem lowerOp_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ i, ∃! N, IsLower ρ (φ i) (e i) (f i) N := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hLat hEig e f hGen i
  haveI : Module.Free O H := hLat.1
  have hmem : e i ∈ eigLat ρ (φ i) := by rw [(hGen i).1]; exact Submodule.mem_span_singleton_self _
  have hv : inK (O := O) K H (e i) ∈ eigK ρ (φ i) := hmem
  have he0 : e i ≠ 0 := by
    obtain ⟨g, hg0, hgs⟩ := (hEig.2.1 (φ i)).2.1
    intro h
    apply hg0
    have : g ∈ eigLat ρ (φ i) := hgs ▸ Submodule.mem_span_singleton_self g
    rw [(hGen i).1, h] at this
    simpa using this
  have hv0 : inK (O := O) K H (e i) ≠ 0 := fun h => he0 (inK_injective_of_free (O := O) K H (h.trans (map_zero (inK (O := O) K H)).symm))
  have key := existsUnique_endo_line (eigK ρ) hEig.1 (φ i) (inK K H (e i)) (inK K H (f i)) hv hv0 (hLat.2.2.2.1 (φ i))
  unfold IsLower
  exact key

end GlobalTheory
end

open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_period_valuation_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ i, ∃! N, IsLower ρ (φ i) (e i) (f i) N := by
  atlas_forward_decl GlobalTheory.lowerOp_existsUnique
end

section
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.ScaledRestr

theorem inK_injective {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] : Function.Injective (inK K H : H →ₗ[O] K ⊗[O] H) := by
  have : IsLocalizedModule (nonZeroDivisors O) (TensorProduct.mk O K H 1) := inferInstance
  unfold inK
  rw [IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors O)]
  intro c
  intro x y hxy
  exact smul_right_injective H (nonZeroDivisors.coe_ne_zero c) hxy

theorem exists_scaled_image {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
    {H : Type} [AddCommGroup H] [Module O H] {I : Type}
    (φ : I → E →+* K) (ρ : orderC c →+* Module.End O H) (D : O) (e f : I → H)
    (hD : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ) (hG : IsGens φ ρ e f)
    (N : Module.End K (K ⊗[O] H)) (i : I) (hN : IsLower ρ (φ i) (e i) (f i) N) (h : H) :
    ∃ m : H, inK K H m = algebraMap O K D • N (inK K H h) := by
  have key : ∀ x ∈ ⨆ σ : E →+* K, eigLat ρ σ, ∃ m : H, inK K H m = N (inK K H x) := by
    intro x hx
    refine Submodule.iSup_induction (fun σ : E →+* K => eigLat ρ σ)
      (motive := fun x => ∃ m : H, inK K H m = N (inK K H x)) hx ?_ ?_ ?_
    · intro σ x hx
      by_cases hσ : σ = φ i
      · subst hσ
        rw [(hG i).1, Submodule.mem_span_singleton] at hx
        obtain ⟨u, rfl⟩ := hx
        refine ⟨u • f i, ?_⟩
        rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul_of_tower, hN.1]
      · refine ⟨0, ?_⟩
        have hx' : inK K H x ∈ eigK ρ σ := hx
        rw [hN.2 σ hσ _ hx', LinearMap.map_zero]
    · exact ⟨0, by simp⟩
    · intro x y hx hy
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, ha, hb]⟩
  obtain ⟨m, hm⟩ := key _ (hD h)
  refine ⟨m, ?_⟩
  rw [hm, LinearMap.map_smul, LinearMap.map_smul_of_tower, algebraMap_smul]

end GlobalTheory.ScaledRestr

namespace GlobalTheory.ScaledRestr

theorem scaledRestr_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → ∀ i, ∃! M : Module.End O H, IsScaledRestr D (N i) M := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hlat hEig e f hG N hN i
  haveI : Module.Free O H := hlat.1
  have hinj := inK_injective (O := O) K H
  have hD : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ := hEig.2.2.1.2
  let g : H →ₗ[O] K ⊗[O] H := (algebraMap O K D) • ((N i).restrictScalars O ∘ₗ inK K H)
  have hg : ∀ h, g h ∈ LinearMap.range (inK K H) := by
    intro h
    obtain ⟨m, hm⟩ := exists_scaled_image φ ρ D e f hD hG (N i) i (hN i) h
    exact ⟨m, hm⟩
  refine ⟨(LinearEquiv.ofInjective (inK K H) hinj).symm.toLinearMap ∘ₗ (g.codRestrict _ hg), ?_, ?_⟩
  · intro h
    have := (LinearEquiv.ofInjective (inK K H) hinj).apply_symm_apply (g.codRestrict _ hg h)
    rw [Subtype.ext_iff, LinearEquiv.ofInjective_apply] at this
    simpa [g] using this
  · intro M hM
    ext h
    apply hinj
    rw [hM h]
    have := (LinearEquiv.ofInjective (inK K H) hinj).apply_symm_apply (g.codRestrict _ hg h)
    rw [Subtype.ext_iff, LinearEquiv.ofInjective_apply] at this
    simpa [g] using this.symm

end GlobalTheory.ScaledRestr
end

open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_period_integrality : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → ∀ i, ∃! M : Module.End O H, IsScaledRestr D (N i) M := by
  atlas_forward_decl GlobalTheory.ScaledRestr.scaledRestr_existsUnique
end

section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_period_conjugate_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → (∀ i (a : OF E), Commute (N i) ((ρ (ofF c a)).baseChange K)) ∧ ∀ i j, N i * N j = 0 := by
  first | exact @GlobalTheory.LowerOps.lower_commute_and_mul_eq_zero | exact GlobalTheory.LowerOps.lower_commute_and_mul_eq_zero | (intros; apply GlobalTheory.LowerOps.lower_commute_and_mul_eq_zero <;> assumption)
end

section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_line_bilinear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → (∀ i x y, B.baseChange K (N i x) y + B.baseChange K x (N i y) = 0) ∧ ∀ i j x y, B.baseChange K (N i x) (N j y) = 0 := by
  first | exact @GlobalTheory.Div.eigen_line_bilinear.lower_skew_orth | exact GlobalTheory.Div.eigen_line_bilinear.lower_skew_orth | (intros; apply GlobalTheory.Div.eigen_line_bilinear.lower_skew_orth <;> assumption)
end

section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_period_norm_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → (∃! ρE : E →+* Module.End K (K ⊗[O] H), ∀ a : orderC c, ρE a = (ρ a).baseChange K) := by
  first | exact @GlobalTheory.CMExtend.exists_unique_extend | exact GlobalTheory.CMExtend.exists_unique_extend | (intros; apply GlobalTheory.CMExtend.exists_unique_extend <;> assumption)
end

section
section
noncomputable section

open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.CMLatticeRow

theorem qt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (l : ℕ), l.Prime → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ D : O, ClearsIdem K (condQ 𝔣 Q) D ↔ ClearsIdem K 𝔣 D :=
  GlobalTheory.T.clears_idempotent_conductor_iff

theorem condT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E)), 𝔣 ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ k : ℕ, (∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → expIn 𝔣 v ≤ k) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ D : O, ClearsIdem K (⊤ : Ideal (OF E)) D → ClearsIdem K 𝔣 ((l : O) ^ k * D) :=
  GlobalTheory.T.clears_idempotent_of_exponent_bound

theorem dualCrit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], Nat.card (E →+* K) = Module.finrank ℚ E → ∀ D : O, (∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = algebraMap O K D * σ y) → ClearsIdem K (⊤ : Ideal (OF E)) D :=
  GlobalTheory.T.clears_idempotent_of_trace_dual

theorem unram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime → ¬ (l : ℤ) ∣ discr E → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = σ y :=
  GlobalTheory.T.exists_lift_of_trace_dual_element

theorem diffEx : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∃ D : O, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → val_vp O l (algebraMap O K D) = ((diffExp_vp l P : ℚ) : WithTop ℚ)) ∧ ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = algebraMap O K D * σ y :=
  GlobalTheory.T.exists_different_exponent_denominator

theorem valPow : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], ∀ (l : ℕ), l ≠ 0 → (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ k : ℕ, val_vp O l (algebraMap O K ((l : O) ^ k)) = ((k : ℚ) : WithTop ℚ) :=
  GlobalTheory.T.valuation_pow_eq_alt

theorem a1 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ) :=
  GlobalTheory.T.cm_type_period_integral_first

theorem a2 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ σ : E →+* K, IsSat (eigLat ρ σ) ∧ (∃ g : H, g ≠ 0 ∧ eigLat ρ σ = O ∙ g) ∧ Module.Free O (eigLat ρ σ) ∧ Module.finrank O (eigLat ρ σ) = 1 ∧ ∃ C : Submodule O H, IsCompl (eigLat ρ σ) C :=
  GlobalTheory.T.cm_type_period_integral_second

theorem a3 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ) → iSupIndep (fun σ : E →+* K => eigLat ρ σ) ∧ ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ :=
  GlobalTheory.T.cm_type_period_integral_third

theorem a4 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ i, Fil ⊓ eigLat ρ (φ i) = eigLat ρ (φ i) :=
  GlobalTheory.T.cm_type_period_integral_fourth

theorem a5 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ σ σ' : E →+* K, σ' ≠ bar σ → ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', B.baseChange K x y = 0 :=
  GlobalTheory.T.cm_type_period_integral_fifth

theorem pb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ i, 0 ≤ val_vp O l (algebraMap O K (B (e i) (f i))) ∧ val_vp O l (algebraMap O K (B (e i) (f i))) ≤ val_vp O l (algebraMap O K D) :=
  GlobalTheory.T.cm_type_period_denominator_bound

theorem la : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ i, ∃! N, IsLower ρ (φ i) (e i) (f i) N :=
  GlobalTheory.T.cm_type_period_valuation_bound

theorem lb1 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → ∀ i, ∃! M : Module.End O H, IsScaledRestr D (N i) M :=
  GlobalTheory.T.cm_type_period_integrality

theorem lb2 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → (∀ i (a : OF E), Commute (N i) ((ρ (ofF c a)).baseChange K)) ∧ ∀ i j, N i * N j = 0 :=
  GlobalTheory.T.cm_type_period_conjugate_integral

theorem lb3 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → (∀ i x y, B.baseChange K (N i x) y + B.baseChange K x (N i y) = 0) ∧ ∀ i j x y, B.baseChange K (N i x) (N j y) = 0 :=
  GlobalTheory.T.eigen_line_bilinear

theorem lc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (O : Type) [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] (H : Type) [AddCommGroup H] [Module O H], Module.Free O H → ∀ (ρ : orderC c →+* Module.End O H) (B : LinearMap.BilinForm O H) (I : Type) [Fintype I] (N : I → Module.End K (K ⊗[O] H)) (D : O) (M : I → Module.End O H), (∀ i, IsScaledRestr D (N i) (M i)) → (∀ i (a : OF E), Commute (N i) ((ρ (ofF c a)).baseChange K)) → (∀ i j, N i * N j = 0) → (∀ i x y, B.baseChange K (N i x) y + B.baseChange K x (N i y) = 0) → (∀ i j x y, B.baseChange K (N i x) (N j y) = 0) → ∀ (l : ℕ) (R : Type) [CommRing R] [Algebra O R] (t : I → R), (∀ x : R ⊗[O] H, ∃ y : R ⊗[O] H, (1 + nilPart l M R t) x = x + (lPrime l : R) • y) ∧ ((1 + nilPart l M R t) * (1 - nilPart l M R t) = 1 ∧ (1 - nilPart l M R t) * (1 + nilPart l M R t) = 1) ∧ (∀ a : OF E, Commute (1 + nilPart l M R t) ((ρ (ofF c a)).baseChange R)) ∧ ∀ x y : R ⊗[O] H, B.baseChange R ((1 + nilPart l M R t) x) ((1 + nilPart l M R t) y) = B.baseChange R x y :=
  GlobalTheory.T.scaled_restriction_endomorphisms

theorem det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → DetClaims K l Fil D e :=
  GlobalTheory.T.cm_type_period_trace_integral

theorem fa : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → (∃! ρE : E →+* Module.End K (K ⊗[O] H), ∀ a : orderC c, ρE a = (ρ a).baseChange K) :=
  GlobalTheory.T.cm_type_period_norm_integral

theorem fb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → (∀ i, 0 ≤ val_vp O l (algebraMap O K (B (e i) (f i))) ∧ val_vp O l (algebraMap O K (B (e i) (f i))) ≤ val_vp O l (algebraMap O K D)) → (∃! ρE : E →+* Module.End K (K ⊗[O] H), ∀ a : orderC c, ρE a = (ρ a).baseChange K) → FormClaims l φ ρ B D e f :=
  GlobalTheory.T.cm_type_period_galois_integral

theorem dp0 : ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (R : Type) [CommRing R] [Algebra O R], (∀ (k : ℕ) (x : R), k ≠ 0 → (k : R) * x = 0 → x = 0) → ∃ γ₀ : DividedPowers (Ideal.span {(l : R)}), ∀ (m : ℕ), ∀ y ∈ Ideal.span {(l : R)}, (m.factorial : R) * γ₀.dpow m y = y ^ m :=
  GlobalTheory.T.exists_divided_powers_prime

theorem dp1 : ∀ (l : ℕ), l.Prime → (∀ m : ℕ, (1 ≤ m → lPrimeExp l + padicValNat l m.factorial ≤ lPrimeExp l * m) ∧ m + 2 * padicValNat l m.factorial ≤ 2 * (lPrimeExp l * m)) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (R : Type) [CommRing R] [Algebra O R], (∀ (k : ℕ) (x : R), k ≠ 0 → (k : R) * x = 0 → x = 0) → ∀ γ₀ : DividedPowers (Ideal.span {(l : R)}), (∀ (m : ℕ), ∀ y ∈ Ideal.span {(l : R)}, (m.factorial : R) * γ₀.dpow m y = y ^ m) → ∃ γ : DividedPowers (Ideal.span {(lPrime l : R)}), (∀ m : ℕ, ∃ q : O, (m.factorial : O) * q = (lPrime l : O) ^ m ∧ ∀ x : R, γ.dpow m ((lPrime l : R) * x) = algebraMap O R q * x ^ m) ∧ (∀ (m : ℕ), ∀ y ∈ Ideal.span {(lPrime l : R)}, γ.dpow m y = γ₀.dpow m y) ∧ ∀ n : ℕ, 1 ≤ n → γ.IsSubDPIdeal (Ideal.span {(lPrime l : R) ^ n}) ∧ ∀ (r : ℕ) (m : Fin r → ℕ) (x : Fin r → R), (∀ i, x i ∈ Ideal.span {(lPrime l : R)}) → 2 * n * lPrimeExp l ≤ ∑ i, m i → ∏ i, γ.dpow (m i) (x i) ∈ Ideal.span {(lPrime l : R) ^ n} :=
  GlobalTheory.T.divided_powers_prime_unique

theorem statement : Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro E _ _ _ _ 𝔣 h𝔣 l hl O _ _ _ _ K _ _ _ hlO hcard
    refine ⟨?_, fun Q _ hQl D => qt E 𝔣 Q l hl hQl O K hlO D⟩
    by_cases hdiv : ∃ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 ∧ (l : OF E) ∈ v.asIdeal
    · obtain ⟨v, hv𝔣, hvl⟩ := hdiv
      have hl' : ¬ (l : ℤ) ∣ discr E := by
        obtain ⟨_, _, l', hl'p, _, hl'v, hdisc, _⟩ := h𝔣.2.2 v hv𝔣
        have hll : l' = l := by
          by_contra hne
          have hcop : IsCoprime ((l' : ℤ) : OF E) ((l : ℤ) : OF E) :=
            (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hl'p hl).2 hne)).intCast
          obtain ⟨a, b, hab⟩ := hcop
          have h1 : (1 : OF E) ∈ v.asIdeal := by
            rw [← hab]
            push_cast
            exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hl'v) (v.asIdeal.mul_mem_left _ hvl)
          exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
        exact hll ▸ hdisc
      refine ⟨(l : O) ^ condExp 𝔣 l, fun P _ => ?_, ?_⟩
      · rw [cNum_vp, if_pos ⟨v, hv𝔣, hvl⟩]
        exact valPow O K l hl.ne_zero hlO _
      · have h1 : ClearsIdem K (⊤ : Ideal (OF E)) (1 : O) := dualCrit E O K hcard 1 (fun σ y hy => by
          obtain ⟨z, hz⟩ := unram E l hl hl' O K hlO σ y hy
          exact ⟨z, by rw [hz, map_one, one_mul]⟩)
        have := condT E 𝔣 h𝔣.1 l hl (condExp 𝔣 l)
          (fun w hw => le_csSup (condExp_bdd 𝔣 hl.ne_zero) ⟨w, hw, rfl⟩) O K hlO 1 h1
        rwa [mul_one] at this
    · obtain ⟨D, hv, hD⟩ := diffEx E l hl O K hlO hcard
      refine ⟨D, fun P hP => ?_, ?_⟩
      · rw [cNum_vp, if_neg hdiv]
        exact hv P hP
      · have hz : ∀ w : HeightOneSpectrum (OF E), (l : OF E) ∈ w.asIdeal → expIn 𝔣 w ≤ 0 := by
          intro w hw
          have : ¬ w.asIdeal ∣ 𝔣 := fun h => hdiv ⟨w, h, hw⟩
          exact le_of_eq (multiplicity_eq_zero.2 this)
        have := condT E 𝔣 h𝔣.1 l hl 0 hz O K hlO D (dualCrit E O K hcard D hD)
        rwa [pow_zero, one_mul] at this
  · intro E _ _ _ 𝔣 h𝔣 l hl Q _ hQl O _ _ _ _ K _ _ _ hlO hcard D hD0 hD I _ φ hφ H _ _ ρ Fil B hL
    have hc : condQ 𝔣 Q ≠ ⊥ := by
      unfold condQ
      rw [Ne, Ideal.mul_eq_bot, not_or]
      refine ⟨h𝔣.1, ?_⟩
      rw [← Ne, ← Ideal.zero_eq_bot]
      exact Finset.prod_ne_zero_iff.2 fun q _ => by rw [Ideal.zero_eq_bot]; exact q.ne_bot
    have hDc : ClearsIdem K (condQ 𝔣 Q) D := (qt E 𝔣 Q l hl hQl O K hlO D).2 hD
    have hE : EigenClaims φ ρ Fil B D := by
      have hI := a1 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL
      exact ⟨hI, a2 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL,
        a3 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hI,
        a4 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL,
        a5 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL⟩
    refine ⟨hE, fun e f hg => ?_⟩
    have hP := pb E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg
    refine ⟨hP, ⟨la E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg, fun N hN => ?_⟩,
      det E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg,
      fb E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg hP
        (fa E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE)⟩
    obtain ⟨h1, h2⟩ := lb2 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg N hN
    obtain ⟨h3, h4⟩ := lb3 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg N hN
    exact ⟨lb1 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg N hN, h1, h2, h3, h4,
      fun M hM R _ _ t => lc E _ O K H hL.1 ρ B I N D M hM h1 h2 h3 h4 l R t⟩
  · intro l hl
    have hnum : ∀ m : ℕ, (1 ≤ m → lPrimeExp l + padicValNat l m.factorial ≤ lPrimeExp l * m) ∧
        m + 2 * padicValNat l m.factorial ≤ 2 * (lPrimeExp l * m) := by
      obtain ⟨h1, h2, _⟩ := GlobalTheory.T.divided_powers_valuations
      intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      by_cases h2l : l = 2
      · subst h2l
        have := h2 m hm
        rw [show lPrimeExp 2 = 2 from rfl]
        omega
      · have := h1 l m hl h2l hm
        rw [show lPrimeExp l = 1 from if_neg h2l]
        omega
    refine ⟨hnum, fun O _ _ _ _ hlO R _ _ htf => ?_⟩
    obtain ⟨γ₀, hγ₀⟩ := dp0 l hl O hlO R htf
    obtain ⟨γ, hγ⟩ := dp1 l hl hnum O hlO R htf γ₀ hγ₀
    exact ⟨γ, γ₀, hγ.1, hγ₀, hγ.2⟩

end GlobalTheory.CMLatticeRow
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_dual_statement : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.Statement := by
  atlas_forward_decl GlobalTheory.CMLatticeRow.statement
end
