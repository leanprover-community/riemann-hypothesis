import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmExtensionAdelesStandardModelDictionary
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AdeleIdemPrimeCriterion
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RayCharacterExtendsToIdeals
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RayInvariantContinuousEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryCharPiComplexUnitsEqProdZpow
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdeleCongruenceUnitCriterion

section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

theorem exists_primeInvolution_of_ringInvolution {R : Type} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] (s : R ≃+* R) (hs : ∀ x, s (s x) = x) :
    ∃ c : HeightOneSpectrum R ≃ HeightOneSpectrum R, (∀ P, c (c P) = P) ∧
      (∀ P, Ideal.absNorm (c P).asIdeal = Ideal.absNorm P.asIdeal) ∧
      (∀ P x, s x ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧
      (∀ P x, s x ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2) := by
  have hm : ∀ (I : Ideal R) (x : R), s x ∈ I.map s ↔ x ∈ I := by
    intro I x
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨y, hy, h⟩
      rwa [← s.injective h]
    · intro h
      exact ⟨x, h, rfl⟩
  let f : HeightOneSpectrum R → HeightOneSpectrum R := fun P =>
    { asIdeal := P.asIdeal.map s
      isPrime := by
        have := P.isPrime
        exact Ideal.map_isPrime_of_equiv s
      ne_bot := by
        intro h
        apply P.ne_bot
        rw [eq_bot_iff]
        intro x hx
        have h1 := (hm _ x).2 hx
        rw [h, Ideal.mem_bot] at h1
        rw [Ideal.mem_bot]
        exact s.injective (by simpa using h1) }
  have hf : Function.Involutive f := by
    intro P
    ext x
    show x ∈ (P.asIdeal.map s).map s ↔ _
    rw [← hm P.asIdeal x, ← hm _ (s x), hs]
  refine ⟨hf.toPerm f, hf, ?_, ?_, ?_⟩
  · intro P
    show Ideal.absNorm (P.asIdeal.map s) = _
    simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal (P.asIdeal.map s) s rfl).toEquiv).symm
  · intro P x
    exact hm _ x
  · intro P x
    show s x ∈ (P.asIdeal.map s) ^ 2 ↔ _
    rw [← Ideal.map_pow, hm]

theorem cmConjugation_on_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → (∀ x, σ (σ x) = x) ∧ ∃ c : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E), (∀ P, c (c P) = P) ∧ (∀ P, Ideal.absNorm (c P).asIdeal = Ideal.absNorm P.asIdeal) ∧ (∀ x : 𝓞 E, ∃ y : 𝓞 E, (y : E) = σ x) ∧ (∀ P (x y : 𝓞 E), (y : E) = σ x → (y ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧ (y ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2)) ∧ ∀ P Q : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = Q.under (𝓞 F) ↔ Q = P ∨ Q = c P := by
  intro F E _ _ _ _ _ σ _ hE h2 hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hσ, hσ, star_star]
  have hfix : ∀ x, σ x = x → ∃ a : F, algebraMap F E a = x := by
    intro x hx
    have := Subalgebra.isSimpleOrder_of_finrank h2
    rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
    · have hx' : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
      rw [h] at hx'
      exact hx'
    · exfalso
      apply IsTotallyComplex.complexEmbedding_not_isReal τ
      rw [ComplexEmbedding.isReal_iff]
      ext y
      have hy : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
      have hy' : σ y = y := hy
      rw [ComplexEmbedding.conjugate_coe_eq]
      have := hσ τ y
      rw [hy'] at this
      exact this.symm
  let e : E ≃+* E :=
    { toFun := σ, invFun := σ, left_inv := hinv, right_inv := hinv,
      map_mul' := map_mul σ, map_add' := map_add σ }
  let s : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv e
  have hs : ∀ x : 𝓞 E, ((s x : 𝓞 E) : E) = σ x := fun x => rfl
  have hss : ∀ x, s (s x) = x := by
    intro x
    apply RingOfIntegers.ext
    rw [hs, hs, hinv]
  have hsF : ∀ a : 𝓞 F, s (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
    intro a
    apply RingOfIntegers.ext
    rw [hs]
    exact σ.commutes (a : F)
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := exists_primeInvolution_of_ringInvolution s hss
  refine ⟨hinv, c, hc1, hc2, fun x => ⟨s x, hs x⟩, ?_, ?_⟩
  · intro P x y hy
    have : y = s x := RingOfIntegers.ext (by rw [hy, hs])
    subst this
    exact ⟨hc3 P x, hc4 P x⟩
  · intro P Q
    have hu : ∀ (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 F),
        a ∈ (P.under (𝓞 F)).asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) a ∈ P.asIdeal := fun P a => Iff.rfl
    constructor
    · intro h
      by_contra hne
      push Not at hne
      have hnot : ¬ ((Q.asIdeal : Set (𝓞 E)) ⊆ P.asIdeal ∪ (c P).asIdeal) := by
        rw [Ideal.subset_union]
        rintro (h' | h')
        · exact hne.1 (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h'))
        · exact hne.2 (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (c P).isPrime.ne_top h'))
      rw [Set.not_subset] at hnot
      obtain ⟨x, hxQ, hx⟩ := hnot
      simp only [Set.mem_union, SetLike.mem_coe, not_or] at hx hxQ
      obtain ⟨a, ha⟩ := hfix ((x * s x : 𝓞 E) : E) (by
        rw [← hs, map_mul, hss, mul_comm])
      have hai : IsIntegral ℤ a := by
        have h1 : IsIntegral ℤ (algebraMap F E a) := by
          rw [ha]; exact RingOfIntegers.isIntegral_coe _
        exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 h1
      obtain ⟨b, hb⟩ : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = x * s x :=
        ⟨⟨a, hai⟩, RingOfIntegers.ext ha⟩
      have h1 : b ∈ (Q.under (𝓞 F)).asIdeal := by
        rw [hu, hb]; exact Ideal.mul_mem_right _ _ hxQ
      rw [← h, hu, hb] at h1
      rcases P.isPrime.mem_or_mem h1 with h3 | h3
      · exact hx.1 h3
      · apply hx.2
        have := (hc3 P _).2 h3
        rwa [hss] at this
    · rintro (rfl | rfl)
      · rfl
      · ext a
        rw [hu, hu, ← hc3 P, hsF]

end GlobalTheory
end

section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

section ConjIdem

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem conjIdem_sigR_tmul (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (a : R) (x : E) :
    sigR R σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := rfl

theorem conjIdem_sigR_sigR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (h : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) : sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [conjIdem_sigR_tmul, conjIdem_sigR_tmul, h]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem conjIdem_sigR_algebraMap (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (a : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) a) = algebraMap R (R ⊗[F] E) a := by
  show sigR R σ (a ⊗ₜ[F] 1) = a ⊗ₜ[F] 1
  rw [conjIdem_sigR_tmul, map_one]

theorem conjIdem_sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (x : E) :
    sigR R σ (inclR (F := F) R x) = inclR (F := F) R (σ x) := rfl

variable [NumberField F] [NumberField E]

omit [NumberField E] in
theorem conjIdem_finPart_cA (σ : E →ₐ[F] E) (y : AE F E) :
    finPart F E (cA σ y) = sigR (Af F) σ (finPart F E y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

omit [NumberField E] in
theorem conjIdem_sigR_mem_intAE (σ : E →ₐ[F] E) (h : ∀ x : 𝓞 E, ∃ y : 𝓞 E, (y : E) = σ x)
    (y : Af F ⊗[F] E) (hy : y ∈ intAE F E) : sigR (Af F) σ y ∈ intAE F E := by
  unfold intAE at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    obtain ⟨z, hz⟩ := h x
    exact AddSubgroup.subset_closure ⟨a, ha, z, by rw [conjIdem_sigR_tmul, hz]⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end ConjIdem

theorem cmConjugation_on_primes_adeles_idempotents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ c : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E), (∀ P, c (c P) = P) ∧ (∀ P, normP (c P) = normP P) ∧ (∀ P (x y : 𝓞 E), (y : E) = σ x → (y ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧ (y ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2)) ∧ (∀ P Q : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = Q.under (𝓞 F) ↔ Q = P ∨ Q = c P) ∧ (∀ y, cA σ (cA σ y) = y) ∧ (∀ y : AE F E, finPart F E (cA σ y) ∈ intAE F E ↔ finPart F E y ∈ intAE F E) ∧ ∀ P e f, IsPrimeIdem σ P e f → IsPrimeIdem σ (c P) (cA σ e) f := by
  intro F E _ _ _ _ _ σ hCM
  obtain ⟨h1, h2, h3, h4⟩ := hCM
  obtain ⟨hinv, c, hc1, hc2, hint, hc3, hc4⟩ := cmConjugation_on_primes F E σ h1 h2 h3 h4
  have hcc : ∀ y : AE F E, cA σ (cA σ y) = y := conjIdem_sigR_sigR (AF F) σ hinv
  have hfin : ∀ y : AE F E, finPart F E (cA σ y) ∈ intAE F E ↔ finPart F E y ∈ intAE F E := by
    have key : ∀ y : AE F E, finPart F E y ∈ intAE F E → finPart F E (cA σ y) ∈ intAE F E := by
      intro y hy
      rw [conjIdem_finPart_cA]
      exact conjIdem_sigR_mem_intAE σ hint _ hy
    intro y
    exact ⟨fun h => by have := key _ h; rwa [hcc] at this, key y⟩
  have hcrit : ∀ (P : HeightOneSpectrum (𝓞 E)) (e : AE F E),
      (∀ x : 𝓞 E, x ≠ 0 →
        (x ∈ P.asIdeal ↔ finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E)) →
      ∀ x : 𝓞 E, x ≠ 0 →
        (x ∈ (c P).asIdeal ↔ finPart F E (cA σ e * incA F E ((x : E)⁻¹)) ∉ intAE F E) := by
    intro P e h x hx
    obtain ⟨z, hz⟩ := hint x
    have hxz : (x : E) = σ z := by rw [hz, hinv]
    have hz0 : z ≠ 0 := by
      rintro rfl
      apply hx
      apply RingOfIntegers.ext
      rw [hxz]
      simp
    have hm : cA σ e * incA F E ((x : E)⁻¹) = cA σ (e * incA F E ((z : E)⁻¹)) := by
      rw [map_mul, conjIdem_sigR_inclR, map_inv₀ σ, hxz]
    rw [(hc3 P z x hxz).1, h z hz0, hm, hfin]
  refine ⟨c, hc1, hc2, hc3, hc4, hcc, hfin, ?_⟩
  intro P e f h
  rcases h with ⟨⟨⟨he1, he2, v, ε, hv, he3⟩, hP⟩, hf⟩ | ⟨hf, ⟨v, ε, hv, he⟩, hP⟩
  · left
    refine ⟨⟨⟨?_, ?_, v, ε, hv, ?_⟩, hcrit P e hP⟩, ?_⟩
    · rw [← map_mul, he1]
    · rw [hcc, mul_comm, he2]
    · rw [hcc, add_comm, he3]
    · rw [hcc, add_comm, hf]
  · right
    have hce : cA σ e = e := by rw [he]; exact conjIdem_sigR_algebraMap _ σ ε
    exact ⟨by rw [hce, hf], ⟨v, ε, hv, by rw [hce, he]⟩, hcrit P e hP⟩

end GlobalTheory
end

section
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.PrimeIdemExists

theorem exists_indicator (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    ∃ a : FiniteAdeleRing (𝓞 K) K, a v = 1 ∧ ∀ w, w ≠ v → a w = 0 := by
  refine ⟨(⟨fun w => if w = v then 1 else 0, ?_⟩ :
    RestrictedProduct (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) Filter.cofinite), ?_, ?_⟩
  · refine Filter.Eventually.of_forall fun w => ?_
    beta_reduce
    by_cases h : w = v
    · rw [if_pos h]; exact one_mem (w.adicCompletionIntegers K)
    · rw [if_neg h]; exact zero_mem (w.adicCompletionIntegers K)
  · exact if_pos rfl
  · intro w hw; exact if_neg hw

theorem cA_algebraMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (ε : AF F) :
    cA σ (algebraMap (AF F) (AE F E) ε) = algebraMap (AF F) (AE F E) ε := by
  change Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ (ε ⊗ₜ[F] (1 : E)) = ε ⊗ₜ[F] (1 : E)
  simp

theorem cA_incA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (x : E) :
    cA σ (incA F E x) = incA F E (σ x) := by
  change Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] (σ x)
  simp

theorem prod_ext {K : Type} [Field K] [NumberField K] {M : Type} {a b : M × FiniteAdeleRing (𝓞 K) K}
    (h1 : a.1 = b.1) (h2 : ∀ P, a.2 P = b.2 P) : a = b :=
  Prod.ext h1 (DFunLike.ext _ _ h2)

theorem exists_isPrimeIdem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ P : HeightOneSpectrum (𝓞 E), ∃ e f, IsPrimeIdem σ P e f := by
  intro F E _ _ _ _ _ σ hσ P
  obtain ⟨c, hcc, -, hcmem, hcund, -, hcint, -⟩ := GlobalTheory.cmConjugation_on_primes_adeles_idempotents F E σ hσ
  obtain ⟨Φ, hΦ1, hΦ2, hΦ3, -, -⟩ := GlobalTheory.T.cmExtension_adeles_standardModel_dictionary F E σ hσ
  have crit := GlobalTheory.adele_idem_prime_criterion F E Φ hΦ1 hΦ2 hΦ3
  obtain ⟨α, hα1, hα0⟩ := exists_indicator F (P.under (𝓞 F))
  have hε : IsPlaceIdem F (P.under (𝓞 F)) (pairA F 0 α) := ⟨α, rfl, hα1, hα0⟩
  set ε := pairA F 0 α with hεdef
  set η := algebraMap (AF F) (AE F E) ε with hη
  obtain ⟨hη1, hη2⟩ := hΦ3 _ _ hε
  rw [← hη] at hη1 hη2
  have hη3 : ∀ Q, (Φ η).2 Q = if Q = P ∨ Q = c P then 1 else 0 := by
    intro Q
    rw [hη2 Q]
    exact if_congr (eq_comm.trans (hcund P Q)) rfl rfl
  have mulap : ∀ (a b : mixedSpace E × FiniteAdeleRing (𝓞 E) E) Q, (a * b).2 Q = a.2 Q * b.2 Q :=
    fun _ _ _ => rfl
  have addap : ∀ (a b : mixedSpace E × FiniteAdeleRing (𝓞 E) E) Q, (a + b).2 Q = a.2 Q + b.2 Q :=
    fun _ _ _ => rfl
  by_cases hP : c P = P
  · have hηη : η * η = η := by
      apply Φ.injective
      rw [map_mul]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_mul, hη1, mul_zero]
      · rw [mulap, hη3]; split_ifs <;> simp
    refine ⟨η, η, Or.inr ⟨rfl, ⟨_, ε, hε, rfl⟩, ?_⟩⟩
    refine (crit η P _ ε hε hηη hηη).2 ⟨hη1, ?_, fun Q hQ => ?_⟩
    · rw [hη3, if_pos (Or.inl rfl)]
    · rw [hη3, if_neg]
      rw [hP]; simpa using hQ
  · obtain ⟨β, hβ1, hβ0⟩ := exists_indicator E P
    set e : AE F E := Φ.symm (0, β) with he
    have hΦe : Φ e = (0, β) := Φ.apply_symm_apply _
    have he1 : (Φ e).1 = 0 := by rw [hΦe]
    have heP : (Φ e).2 P = 1 := by rw [hΦe]; exact hβ1
    have he0 : ∀ Q, Q ≠ P → (Φ e).2 Q = 0 := by rw [hΦe]; exact hβ0
    have hee : e * e = e := by
      apply Φ.injective
      rw [map_mul]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_mul, he1, mul_zero]
      · rw [mulap]
        by_cases hQ : Q = P
        · subst hQ; rw [heP, mul_one]
        · rw [he0 Q hQ, mul_zero]
    have heη : e * η = e := by
      apply Φ.injective
      rw [map_mul]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_mul, he1, zero_mul]
      · rw [mulap]
        by_cases hQ : Q = P
        · rw [hη3, if_pos (Or.inl hQ), mul_one]
        · rw [he0 Q hQ, zero_mul]
    have hcr := (crit e P _ ε hε hee heη).2 ⟨he1, heP, he0⟩
    have hσσ : ∀ x : E, σ (σ x) = x := by
      intro x
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      apply τ.injective
      rw [hσ.2.2.2, hσ.2.2.2, star_star]
    have hcr' : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ (c P).asIdeal ↔
        finPart F E (cA σ e * incA F E ((x : E)⁻¹)) ∉ intAE F E) := by
      intro x hx
      have hint : IsIntegral ℤ (σ (x : E)) :=
        (RingOfIntegers.isIntegral_coe x).map (σ.toRingHom.toIntAlgHom)
      let y : 𝓞 E := ⟨σ (x : E), hint⟩
      have hy : (y : E) = σ (x : E) := rfl
      have hxy : (x : E) = σ (y : E) := by rw [hy, hσσ]
      have hy0 : y ≠ 0 := by
        intro h0
        apply hx
        apply RingOfIntegers.ext
        rw [hxy, h0]; simp
      rw [(hcmem P y x hxy).1, hcr y hy0, ← hcint, map_mul (cA σ), cA_incA, map_inv₀, ← hxy]
    have hee' : cA σ e * cA σ e = cA σ e := by rw [← map_mul, hee]
    have heη' : cA σ e * η = cA σ e := by
      have := congrArg (cA σ) heη
      rwa [map_mul, hη, cA_algebraMap] at this
    obtain ⟨hc1, hcP, hc0⟩ := (crit (cA σ e) (c P) _ ε hε hee' heη').1 hcr'
    refine ⟨e, e + cA σ e, Or.inl ⟨⟨⟨hee, ?_, _, ε, hε, ?_⟩, hcr⟩, rfl⟩⟩
    · apply Φ.injective
      rw [map_mul, map_zero]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_mul, he1, zero_mul]; rfl
      · rw [mulap]
        by_cases hQ : Q = P
        · rw [hc0 Q (by rw [hQ]; exact fun h => hP h.symm), mul_zero]; rfl
        · rw [he0 Q hQ, zero_mul]; rfl
    · apply Φ.injective
      rw [map_add, ← hη]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_add, he1, hc1, hη1, add_zero]
      · rw [addap, hη3]
        by_cases hQ : Q = P
        · subst hQ
          rw [heP, hc0 _ (fun h => hP h.symm), add_zero, if_pos (Or.inl rfl)]
        · by_cases hQ' : Q = c P
          · subst hQ'
            rw [he0 _ hQ, hcP, zero_add, if_pos (Or.inr rfl)]
          · rw [he0 _ hQ, hc0 _ hQ', add_zero, if_neg (by tauto)]

end GlobalTheory.PrimeIdemExists
end

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeIdempotent_CMField : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ P : HeightOneSpectrum (𝓞 E), ∃ e f, IsPrimeIdem σ P e f := by
  atlas_forward_decl GlobalTheory.PrimeIdemExists.exists_isPrimeIdem
end

section
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical in
open scoped TensorProduct ContDiff nonZeroDivisors in

theorem _root_.GlobalTheory.isPrimeIdem_eq_indicator :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ Φ : _root_.HeckeCharacterZeroLocus.ThmBIn.AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (_root_.HeckeCharacterZeroLocus.ThmBIn.incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) → (∀ y, _root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E y ∈ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) → (∀ v ε, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPlaceIdem F v ε → (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) → ∀ P e f, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPrimeIdem σ P e f → ((Φ e).1 = 0 ∧ (Φ e).2 P = 1 ∧ ∀ Q, Q ≠ P → (Φ e).2 Q = 0) := by
  intro F E _ _ _ _ _ σ Φ hΦ hint hplace P e f hprime
  unfold _root_.HeckeCharacterZeroLocus.ThmBIn.IsPrimeIdem at hprime
  rcases hprime with ⟨hat, -⟩ | ⟨-, ⟨v, ε, hε, rfl⟩, hcrit⟩
  · unfold _root_.HeckeCharacterZeroLocus.ThmBIn.IsIdemAt _root_.HeckeCharacterZeroLocus.ThmBIn.IsSplitIdem at hat
    obtain ⟨⟨he, hce, v, ε, hε, hsum⟩, hcrit⟩ := hat
    have heε : e * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε = e := by
      rw [← hsum, mul_add, he, hce, add_zero]
    exact (_root_.GlobalTheory.adele_idem_prime_criterion F E Φ hΦ hint hplace e P v ε hε he heε).mp hcrit
  · obtain ⟨h0, hind⟩ := hplace v ε hε
    have he : algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε =
        algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε := by
      apply Φ.injective
      rw [map_mul]
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_mul, h0, mul_zero]
      · ext Q : 1
        change (Φ _).2 Q * (Φ _).2 Q = (Φ _).2 Q
        rw [hind Q]
        split_ifs <;> simp
    exact (_root_.GlobalTheory.adele_idem_prime_criterion F E Φ hΦ hint hplace _ P v ε hε he he).mp hcrit

end GlobalTheory
end

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeIdempotent_eq_indicator_prime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ Φ : AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) → (∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) → (∀ v ε, IsPlaceIdem F v ε → (Φ (algebraMap (AF F) (AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (AF F) (AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) → ∀ P e f, IsPrimeIdem σ P e f → ((Φ e).1 = 0 ∧ (Φ e).2 P = 1 ∧ ∀ Q, Q ≠ P → (Φ e).2 Q = 0) := by
  atlas_forward_decl GlobalTheory.isPrimeIdem_eq_indicator
end

section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.HeckeUnif

theorem idem_glue_mul {R : Type*} [CommRing R] {e : R} (he : e * e = e) (a b : R) :
    (e * a + (1 - e)) * (e * b + (1 - e)) = e * (a * b) + (1 - e) := by
  linear_combination (a * b - a - b + 1) * he

theorem intValuation_of_mem_notMem_sq {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : HeightOneSpectrum R) {a : R} (h1 : a ∈ P.asIdeal) (h2 : a ∉ P.asIdeal ^ 2) :
    P.intValuation a = WithZero.exp (-1 : ℤ) := by
  have ha : a ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have k1 : P.intValuation a ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; simpa using h1
  have k2 : ¬ P.intValuation a ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; exact h2
  have h0 : P.intValuation a ≠ 0 := HeightOneSpectrum.intValuation_ne_zero P a ha
  rw [← WithZero.exp_log h0] at k1 k2 ⊢
  rw [WithZero.exp_le_exp] at k1 k2
  congr 1
  omega

theorem unifIdele_exists_chiAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)), (∃ x, IsUnifIdele σ P x) ∧ (IsUnramAt σ χ P → ∀ x, IsUnifIdele σ P x → chiAt σ χ P = (χ x : ℂ)) ∧ ‖chiAt σ χ P‖ ≤ 1 := by
  intro F E _ _ _ _ _ σ hσ χ P
  obtain ⟨Φ, h1, h2, h3, -, -⟩ := GlobalTheory.T.cmExtension_adeles_standardModel_dictionary F E σ hσ
  have hu := GlobalTheory.T.primeIdempotent_eq_indicator_prime F E σ Φ h1 h2 h3 P
  obtain ⟨e, f, hef⟩ := GlobalTheory.T.exists_primeIdempotent_CMField F E σ hσ P
  obtain ⟨ea, eb, ec⟩ := hu e f hef
  have huniq : ∀ e' f', IsPrimeIdem σ P e' f' → e' = e := by
    intro e' f' h'
    obtain ⟨ea', eb', ec'⟩ := hu e' f' h'
    apply Φ.injective
    refine Prod.ext (by rw [ea, ea']) ?_
    ext Q
    by_cases hQ : Q = P
    · subst hQ; rw [eb, eb']
    · rw [ec Q hQ, ec' Q hQ]
  let ψ : ∀ Q : HeightOneSpectrum (𝓞 E), AE F E →+* Q.adicCompletion E := fun Q =>
    ((evalV E Q).toRingHom.comp (RingHom.snd _ _)).comp Φ.toRingHom
  have hψ : ∀ Q y, (Φ y).2 Q = ψ Q y := fun _ _ => rfl
  have he : e * e = e := by
    apply Φ.injective
    refine Prod.ext (by rw [map_mul, Prod.fst_mul, ea, mul_zero]) ?_
    ext Q
    rw [hψ, hψ, map_mul, ← hψ]
    by_cases hQ : Q = P
    · subst hQ; rw [eb, mul_one]
    · rw [ec Q hQ, mul_zero]
  have hint : ∀ c : E, P.valuation E c ≤ 1 →
      finPart F E (e * incA F E c + (1 - e)) ∈ intAE F E := by
    intro c hc
    rw [h2]
    intro Q
    rw [hψ, map_add, map_sub, map_mul, map_one, ← hψ, ← hψ]
    by_cases hQ : Q = P
    · subst hQ
      rw [eb, h1, one_mul, sub_self, add_zero]
      have : Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) c) Q) = Q.valuation E c :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q c
      exact this.le.trans hc
    · rw [ec Q hQ]; simp
  have hex : ∃ x, IsUnifIdele σ P x := by
    obtain ⟨ϖ, m1, m2⟩ := Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1
    have hϖ : (ϖ : E) ≠ 0 := by
      intro h
      have : ϖ = 0 := by exact_mod_cast h
      exact m2 (this ▸ zero_mem _)
    have hm : (e * incA F E (ϖ : E) + (1 - e)) * (e * incA F E (ϖ : E)⁻¹ + (1 - e)) = 1 := by
      rw [idem_glue_mul he, ← map_mul, mul_inv_cancel₀ hϖ, map_one]; ring
    exact ⟨⟨_, _, hm, by rw [mul_comm, hm]⟩, e, f, ϖ, hef, by simpa using m1, m2, rfl⟩
  have hq : ∀ x y : (AE F E)ˣ, IsUnifIdele σ P x → IsUnifIdele σ P y →
      ∃ c : E, P.valuation E c ≤ 1 ∧
        ((x * y⁻¹ : (AE F E)ˣ) : AE F E) = e * incA F E c + (1 - e) := by
    rintro x y ⟨e1, f1, a, p1, a1, a2, hx⟩ ⟨e2, f2, b, p2, b1, b2, hy⟩
    rw [huniq _ _ p1] at hx
    rw [huniq _ _ p2] at hy
    have hb : (b : E) ≠ 0 := by
      intro h
      have : b = 0 := by exact_mod_cast h
      exact b2 (this ▸ zero_mem _)
    refine ⟨(a : E) / (b : E), ?_, ?_⟩
    · have va : P.valuation E (a : E) = WithZero.exp (-1 : ℤ) := by
        rw [← intValuation_of_mem_notMem_sq P a1 a2]
        exact HeightOneSpectrum.valuation_of_algebraMap P a
      have vb : P.valuation E (b : E) = WithZero.exp (-1 : ℤ) := by
        rw [← intValuation_of_mem_notMem_sq P b1 b2]
        exact HeightOneSpectrum.valuation_of_algebraMap P b
      rw [map_div₀, va, vb, div_self WithZero.exp_ne_zero]
    · rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul, hx, hy, idem_glue_mul he, ← map_mul,
        div_mul_cancel₀ _ hb]
  refine ⟨hex, ?_, ?_⟩
  · intro hun x hx
    have hc : IsUnramAt σ χ P ∧ ∃ x, IsUnifIdele σ P x := ⟨hun, hex⟩
    rw [chiAt, dif_pos hc]
    have hy := hc.2.choose_spec
    set y := hc.2.choose
    obtain ⟨e', f', p', hχ⟩ := hun
    rw [huniq _ _ p'] at hχ
    obtain ⟨c, c1, c2⟩ := hq y x hy hx
    obtain ⟨d, d1, d2⟩ := hq x y hx hy
    have := hχ (y * x⁻¹) (by rw [c2]; linear_combination (1 - incA F E c) * he)
      (by rw [c2]; exact hint c c1)
      (by rw [mul_inv_rev, inv_inv, d2]; exact hint d d1)
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    rw [this]
  · rw [chiAt]
    split_ifs
    · exact (Circle.norm_coe _).le
    · simp

end GlobalTheory.HeckeUnif
end

section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

theorem mem_range_algebraMap_of_conj_fixed (F E : Type) [Field F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hE : IsTotallyComplex E) (h2 : Module.finrank F E = 2)
    (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (e : E) (he : σ e = e) :
    ∃ c : F, algebraMap F E c = e := by
  have := Subalgebra.isSimpleOrder_of_finrank h2
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
  · have hm : e ∈ AlgHom.equalizer σ (AlgHom.id F E) := by
      rw [AlgHom.mem_equalizer]; simpa using he
    rw [h] at hm
    exact Algebra.mem_bot.mp hm
  · exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hm : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
    rw [AlgHom.mem_equalizer] at hm
    have h1 := hσ τ x
    rw [hm] at h1
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact h1.symm

theorem exists_mul_conj_eq_algebraMap (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hE : IsTotallyComplex E) (h2 : Module.finrank F E = 2)
    (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (R : Type) [CommRing R] [Algebra F R]
    (y : R ⊗[F] E) :
    ∃ n : R, y * Algebra.TensorProduct.map (AlgHom.id F R) σ y = algebraMap R (R ⊗[F] E) n := by
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hσ, hσ, star_star]
  set φ := Algebra.TensorProduct.map (AlgHom.id F R) σ with hφ
  have key : ∀ y z : R ⊗[F] E, ∃ n : R, y * φ z + z * φ y = algebraMap R (R ⊗[F] E) n := by
    intro y z
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨n₁, h₁⟩ := h₁
      obtain ⟨n₂, h₂⟩ := h₂
      exact ⟨n₁ + n₂, by rw [map_add, map_add, ← h₁, ← h₂]; ring⟩
    | tmul a e =>
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | add z₁ z₂ h₁ h₂ =>
        obtain ⟨n₁, h₁⟩ := h₁
        obtain ⟨n₂, h₂⟩ := h₂
        exact ⟨n₁ + n₂, by rw [map_add, map_add, ← h₁, ← h₂]; ring⟩
      | tmul b f =>
        obtain ⟨c, hc⟩ := mem_range_algebraMap_of_conj_fixed F E σ hE h2 hσ
          (e * σ f + f * σ e) (by rw [map_add, map_mul, map_mul, hinv, hinv]; ring)
        refine ⟨c • (a * b), ?_⟩
        rw [hφ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          AlgHom.id_apply, AlgHom.id_apply, mul_comm b a, ← TensorProduct.tmul_add, ← hc,
          Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  obtain ⟨n, hn⟩ := key y y
  refine ⟨algebraMap F R (1 / 2) * n, ?_⟩
  have h : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul]; norm_num
  have h' : algebraMap R (R ⊗[F] E) (algebraMap F R (1 / 2)) * 2 = 1 := by
    rw [← map_ofNat (algebraMap R (R ⊗[F] E)) 2, ← map_mul, h, map_one]
  rw [map_mul, ← hn, ← two_mul, ← mul_assoc, h', one_mul]

theorem exists_unit_mul_conj_eq_algebraMap :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → ∀ (R : Type) [CommRing R] [Algebra F R] (x : (R ⊗[F] E)ˣ), ∃ n : Rˣ, (x : R ⊗[F] E) * Algebra.TensorProduct.map (AlgHom.id F R) σ (x : R ⊗[F] E) = algebraMap R (R ⊗[F] E) n := by
  intro F E _ _ _ _ _ σ _ hE h2 hσ R _ _ x
  obtain ⟨n, hn⟩ := exists_mul_conj_eq_algebraMap F E σ hE h2 hσ R (x : R ⊗[F] E)
  obtain ⟨m, hm⟩ := exists_mul_conj_eq_algebraMap F E σ hE h2 hσ R ((x⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)
  have hinj : Function.Injective (algebraMap R (R ⊗[F] E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := R) (algebraMap F E).injective
  have hnm : n * m = 1 := by
    apply hinj
    rw [map_mul, map_one, ← hn, ← hm, mul_mul_mul_comm, ← map_mul, Units.mul_inv, map_one, mul_one]
  exact ⟨⟨n, m, hnm, by rw [mul_comm, hnm]⟩, hn⟩

end GlobalTheory
end

section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

theorem ideleChar_conj_eq_inv_of_trivial_on_base :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ χ : (AE F E)ˣ →* Circle, (∀ a : (AF F)ˣ, χ (idF F E a) = 1) → ∀ x y : (AE F E)ˣ, (y : AE F E) = cA σ x → χ y = (χ x)⁻¹ := by
  intro F E _ _ _ _ _ σ h χ hχ x y hy
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨n, hn⟩ := exists_unit_mul_conj_eq_algebraMap F E σ h1 h2 h3 h4 (AF F) x
  have hxy : x * y = idF F E n := by
    apply Units.ext
    rw [Units.val_mul, hy]
    exact hn
  have h5 : χ x * χ y = 1 := by rw [← map_mul, hxy, hχ]
  exact eq_inv_of_mul_eq_one_right h5

end GlobalTheory
end

section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical in
open scoped TensorProduct ContDiff nonZeroDivisors in

theorem _root_.GlobalTheory.cA_incA_apply {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (x : E) :
    _root_.HeckeCharacterZeroLocus.ThmBIn.cA σ (_root_.HeckeCharacterZeroLocus.ThmBIn.incA F E x) = _root_.HeckeCharacterZeroLocus.ThmBIn.incA F E (σ x) := by
  unfold _root_.HeckeCharacterZeroLocus.ThmBIn.cA _root_.HeckeCharacterZeroLocus.ThmBIn.incA _root_.HeckeCharacterZeroLocus.ThmBIn.AE
  exact rfl

end GlobalTheory
end

section
open Filter Topology

namespace GlobalTheory

theorem real_pos_at_one_of_right (L : ℂ → ℂ) (hc : ContinuousAt L 1) (h1 : L 1 ≠ 0)
    (h : ∀ s : ℂ, 1 < s.re → s.im = 0 → (L s).im = 0 ∧ 0 < (L s).re) :
    (L 1).im = 0 ∧ 0 < (L 1).re := by
  have ht : Tendsto (fun t : ℝ => L (t : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (L 1)) := by
    have h0 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (1 : ℂ)) := by
      simpa using Complex.continuous_ofReal.tendsto 1
    exact (hc.tendsto.comp h0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), (L (t : ℂ)).im = 0 ∧ 0 < (L (t : ℂ)).re := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact h t (by simpa using ht) (by simp)
  have him : (L 1).im = 0 := by
    have h2 := (Complex.continuous_im.tendsto _).comp ht
    have h3 : Tendsto (Complex.im ∘ fun t : ℝ => L (t : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun t ht => ht.1.symm)
    exact tendsto_nhds_unique h2 h3
  have hre : 0 ≤ (L 1).re :=
    ge_of_tendsto ((Complex.continuous_re.tendsto _).comp ht) (hev.mono fun t ht => ht.2.le)
  refine ⟨him, lt_of_le_of_ne hre fun h0 => h1 ?_⟩
  exact Complex.ext h0.symm him

end GlobalTheory
end
