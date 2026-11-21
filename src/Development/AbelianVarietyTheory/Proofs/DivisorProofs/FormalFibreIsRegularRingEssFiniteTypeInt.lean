import Mathlib
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendAdicCompletionLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingQuotientOfDetDerivationUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataOfPrime

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_surj_localization_mvPolynomial_of_essFiniteType :
    ∀ (Λ R : Type) [CommRing Λ] [CommRing R] [IsLocalRing R] [Algebra Λ R]
      [Algebra.EssFiniteType Λ R], ∃ (n : ℕ) (P : Ideal (MvPolynomial (Fin n) Λ)) (_ : P.IsPrime)
      (φ : Localization.AtPrime P →ₐ[Λ] R), Function.Surjective φ := by
  intro Λ R _ _ _ _ h
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff Λ R).mp h
  let y : Fin σ.card → R := fun i => (σ.equivFin.symm i : R)
  let φ₀ : MvPolynomial (Fin σ.card) Λ →ₐ[Λ] R := MvPolynomial.aeval y
  have hrange : Algebra.adjoin Λ (σ : Set R) = φ₀.range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    congr 1
    ext x
    constructor
    · intro hx
      exact ⟨σ.equivFin ⟨x, hx⟩, by simp [y]⟩
    · rintro ⟨i, rfl⟩
      exact (σ.equivFin.symm i).2
  let P : Ideal (MvPolynomial (Fin σ.card) Λ) := (maximalIdeal R).comap φ₀
  have hunit : ∀ b : P.primeCompl, IsUnit (φ₀ b) := by
    intro b
    by_contra hb
    exact b.2 ((mem_maximalIdeal _).mpr hb)
  refine ⟨σ.card, P, inferInstance, IsLocalization.liftAlgHom (M := P.primeCompl) (f := φ₀) hunit, ?_⟩
  intro r
  obtain ⟨t, ht, htu, hrt⟩ := hσ r
  rw [hrange] at ht hrt
  obtain ⟨b, rfl⟩ := ht
  obtain ⟨a, ha⟩ := hrt
  have hb : b ∈ P.primeCompl := fun hbP => (mem_maximalIdeal _).mp hbP htu
  refine ⟨IsLocalization.mk' (Localization.AtPrime P) a ⟨b, hb⟩, ?_⟩
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_mk'_spec]
  change φ₀ a = φ₀ b * r
  exact ha.trans (mul_comm _ _)

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_surj_localization_mvPolynomial_of_essFiniteType_local : ∀ (Λ R : Type) [CommRing Λ] [CommRing R] [IsLocalRing R] [Algebra Λ R] [Algebra.EssFiniteType Λ R], ∃ (n : ℕ) (P : Ideal (MvPolynomial (Fin n) Λ)) (_ : P.IsPrime) (φ : Localization.AtPrime P →ₐ[Λ] R), Function.Surjective φ := by
  atlas_forward_decl GlobalTheory.exists_surj_localization_mvPolynomial_of_essFiniteType
end

section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_extend_adicCompletion_localization : ∀ (S : Type) [CommRing S] (P : Ideal S) [P.IsPrime] (d : Derivation ℤ S S), ∃ D : Derivation ℤ (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)) (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)), ∀ x, D (algebraMap S _ x) = algebraMap S _ (d x) := by
  first | exact @GlobalTheory.derivation_extend_completion_localization_atPrime | exact GlobalTheory.derivation_extend_completion_localization_atPrime | (intros; apply GlobalTheory.derivation_extend_completion_localization_atPrime <;> assumption)
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

open MvPolynomial in

noncomputable def coeffDerivFun {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p : MvPolynomial τ B) : MvPolynomial τ B :=
  ∑ s ∈ p.support, monomial s (D (coeff s p))

open MvPolynomial in
theorem coeff_coeffDerivFun {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p : MvPolynomial τ B) (m : τ →₀ ℕ) :
    coeff m (coeffDerivFun D p) = D (coeff m p) := by
  classical
  rw [coeffDerivFun, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

noncomputable def coeffDerivAddHom {B τ : Type} [CommRing B] (D : Derivation ℤ B B) :
    MvPolynomial τ B →+ MvPolynomial τ B where
  toFun := coeffDerivFun D
  map_zero' := by ext m; simp [coeff_coeffDerivFun]
  map_add' p q := by ext m; simp [coeff_coeffDerivFun]

theorem coeffDerivAddHom_monomial {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (s : τ →₀ ℕ) (a : B) :
    coeffDerivAddHom D (MvPolynomial.monomial s a) = MvPolynomial.monomial s (D a) := by
  classical
  ext m
  change MvPolynomial.coeff m (coeffDerivFun D _) = _
  rw [coeff_coeffDerivFun, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  split_ifs <;> simp

theorem coeffDerivAddHom_mul {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p q : MvPolynomial τ B) :
    coeffDerivAddHom D (p * q) = p * coeffDerivAddHom D q + q * coeffDerivAddHom D p := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    induction q using MvPolynomial.induction_on' with
    | monomial v b =>
      simp only [MvPolynomial.monomial_mul, coeffDerivAddHom_monomial, Derivation.leibniz,
        smul_eq_mul, map_add, add_comm v u]
    | add q₁ q₂ h₁ h₂ =>
      rw [mul_add, map_add, h₁, h₂, map_add]; ring
  | add p₁ p₂ h₁ h₂ =>
    rw [add_mul, map_add, h₁, h₂, map_add]; ring

theorem derivation_extend_mvPolynomial :
    ∀ (B τ : Type) [CommRing B] (D : Derivation ℤ B B),
      ∃ D' : Derivation ℤ (MvPolynomial τ B) (MvPolynomial τ B),
        (∀ x, D' (MvPolynomial.C x) = MvPolynomial.C (D x)) ∧ ∀ t, D' (MvPolynomial.X t) = 0 := by
  intro B τ _ D
  refine ⟨Derivation.mk' (coeffDerivAddHom D).toIntLinearMap
    (fun a b => by simpa [smul_eq_mul] using coeffDerivAddHom_mul D a b), ?_, ?_⟩
  · intro x
    show coeffDerivAddHom D (MvPolynomial.monomial 0 x) = MvPolynomial.monomial 0 (D x)
    exact coeffDerivAddHom_monomial D 0 x
  · intro t
    show coeffDerivAddHom D (MvPolynomial.monomial (Finsupp.single t 1) 1) = 0
    rw [coeffDerivAddHom_monomial, Derivation.map_one_eq_zero, map_zero]

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_extend_mvPolynomial : ∀ (B τ : Type) [CommRing B] (D : Derivation ℤ B B), ∃ D' : Derivation ℤ (MvPolynomial τ B) (MvPolynomial τ B), (∀ x, D' (MvPolynomial.C x) = MvPolynomial.C (D x)) ∧ ∀ t, D' (MvPolynomial.X t) = 0 := by
  atlas_forward_decl GlobalTheory.derivation_extend_mvPolynomial
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isRegularRing_tensor_of_fibre_localRings :
    ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsNoetherianRing T] [Field K]
      [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q →
      (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) →
      (∀ (n : Ideal T) [n.IsPrime], n.comap (algebraMap S T) = Q →
        IsRegularLocalRing (Localization.AtPrime n ⧸
          (Q.map (algebraMap S T)).map (algebraMap T (Localization.AtPrime n)))) →
      IsRegularRing (T ⊗[S] K) := by
  intro S T K _ _ _ _ _ _ Q hQ hfrac hreg
  haveI : Q.IsPrime := hQ ▸ RingHom.ker_isPrime (algebraMap S K)
  let φ : Q.ResidueField →ₐ[S] K := Ideal.ResidueField.liftₐ Q (Algebra.ofId S K) hQ.ge (by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hx (hQ ▸ h0))
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, b, hb, hy⟩ := hfrac y
    have hb0 : algebraMap S K b ≠ 0 := fun h0 => hb (hQ ▸ h0)
    refine ⟨algebraMap S Q.ResidueField a * (algebraMap S Q.ResidueField b)⁻¹, ?_⟩
    rw [map_mul, map_inv₀, AlgHom.commutes, AlgHom.commutes]
    rw [← hy, mul_assoc, mul_inv_cancel₀ hb0, mul_one]
  let e : Q.ResidueField ≃ₐ[S] K := AlgEquiv.ofBijective φ ⟨φ.toRingHom.injective, hsurj⟩
  let E : Q.Fiber T ≃ₐ[S] T ⊗[S] K :=
    (Algebra.TensorProduct.congr e AlgEquiv.refl).trans (Algebra.TensorProduct.comm S K T)
  haveI : IsNoetherianRing (Q.Fiber T) := by
    letI : Algebra T (Q.Fiber T) := Algebra.TensorProduct.rightAlgebra
    let Sp := Localization (Algebra.algebraMapSubmonoid T Q.primeCompl)
    haveI : IsNoetherianRing Sp :=
      IsLocalization.isNoetherianRing (Algebra.algebraMapSubmonoid T Q.primeCompl) Sp inferInstance
    exact isNoetherianRing_of_ringEquiv _ (Ideal.Fiber.algEquivAux₁ Q (S := T)).toRingEquiv.symm
  haveI : IsRegularRing (Q.Fiber T) := by
    rw [isRegularRing_iff]
    intro q hq
    let n : Ideal T := q.comap (Algebra.TensorProduct.includeRight : T →ₐ[S] Q.Fiber T)
    haveI : n.IsPrime := Ideal.comap_isPrime _ _
    have hn : n.comap (algebraMap S T) = Q := by
      change Ideal.comap (algebraMap S T) (Ideal.comap
        ((Algebra.TensorProduct.includeRight : T →ₐ[S] Q.Fiber T) : T →+* Q.Fiber T) q) = Q
      rw [Ideal.comap_comap, AlgHom.comp_algebraMap]
      exact (Ideal.over_def q Q).symm
    haveI := hreg n hn
    exact IsRegularLocalRing.of_ringEquiv (Ideal.Fiber.algEquivAux₂ Q q).toRingEquiv.symm
  exact IsRegularRing.of_ringEquiv E.toRingEquiv

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularRing_tensor_of_regular_fibre_localizations : ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsNoetherianRing T] [Field K] [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q → (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) → (∀ (n : Ideal T) [n.IsPrime], n.comap (algebraMap S T) = Q → IsRegularLocalRing (Localization.AtPrime n ⧸ (Q.map (algebraMap S T)).map (algebraMap T (Localization.AtPrime n)))) → IsRegularRing (T ⊗[S] K) := by
  atlas_forward_decl GlobalTheory.isRegularRing_tensor_of_fibre_localRings
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem regular_fibre_of_jacobian : ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsRegularRing T] [Field K] [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q → (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) → ∀ (h : ℕ) (f : Fin h → S) (g : S) (d : Fin h → Derivation ℤ S S) (D : Fin h → Derivation ℤ T T), (∀ i x, D i (algebraMap S T x) = algebraMap S T (d i x)) → g ∉ Q → (∀ j, f j ∈ Q) → (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) → (Matrix.of fun i j => d i (f j)).det ∉ Q → IsRegularRing (T ⊗[S] K) := by
  intro S T K _ _ _ _ _ _ Q hker hfrac h f g d D hD hg hf hgQ hdet
  refine GlobalTheory.T.isRegularRing_tensor_of_regular_fibre_localizations S T K Q hker hfrac ?_
  intro n _ hn
  set F : Fin h → T := fun j => algebraMap S T (f j) with hFdef
  have hFn : ∀ j, F j ∈ n := by
    intro j
    have : f j ∈ n.comap (algebraMap S T) := by rw [hn]; exact hf j
    exact this
  have hdetn : (Matrix.of fun i j => D i (F j)).det ∉ n := by
    intro hmem
    have hm : (Matrix.of fun i j => D i (F j)) = (Matrix.of fun i j => d i (f j)).map (algebraMap S T) := by
      ext i j; simp [hFdef, hD]
    rw [hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hmem
    have : (Matrix.of fun i j => d i (f j)).det ∈ n.comap (algebraMap S T) := hmem
    rw [hn] at this
    exact hdet this
  have hreg := GlobalTheory.T.isRegularLocalRing_quotient_of_det_derivation_unit T h F D n hFn hdetn
  have heq : (Ideal.span (Set.range F)).map (algebraMap T (Localization.AtPrime n)) =
      (Q.map (algebraMap S T)).map (algebraMap T (Localization.AtPrime n)) := by
    have hspan : Ideal.span (Set.range F) = (Ideal.span (Set.range f)).map (algebraMap S T) := by
      rw [Ideal.map_span, ← Set.range_comp]; rfl
    rw [hspan, Ideal.map_map, Ideal.map_map]
    apply le_antisymm
    · apply Ideal.map_mono
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hf j
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap]
      have hu : IsUnit ((algebraMap T (Localization.AtPrime n)).comp (algebraMap S T) g) := by
        rw [RingHom.comp_apply]
        apply IsLocalization.map_units (M := n.primeCompl) (Localization.AtPrime n) (⟨algebraMap S T g, ?_⟩ : n.primeCompl)
        intro hgn
        have : g ∈ n.comap (algebraMap S T) := hgn
        rw [hn] at this
        exact hg this
      have hm : (algebraMap T (Localization.AtPrime n)).comp (algebraMap S T) (g * x) ∈
          (Ideal.span (Set.range f)).map ((algebraMap T (Localization.AtPrime n)).comp (algebraMap S T)) :=
        Ideal.mem_map_of_mem _ (hgQ x hx)
      rw [map_mul] at hm
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hm
  rw [← heq]
  exact hreg

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegular_fibre_of_jacobian_derivations : ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsRegularRing T] [Field K] [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q → (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) → ∀ (h : ℕ) (f : Fin h → S) (g : S) (d : Fin h → Derivation ℤ S S) (D : Fin h → Derivation ℤ T T), (∀ i x, D i (algebraMap S T x) = algebraMap S T (d i x)) → g ∉ Q → (∀ j, f j ∈ Q) → (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) → (Matrix.of fun i j => d i (f j)).det ∉ Q → IsRegularRing (T ⊗[S] K) := by
  atlas_forward_decl GlobalTheory.regular_fibre_of_jacobian
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

open MvPolynomial in

theorem derivation_sumAlgEquiv_eq_pderiv {Λ : Type} [CommRing Λ] {σ τ : Type}
    (d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ))
      (MvPolynomial τ (MvPolynomial σ Λ)))
    (h1 : ∀ t x, d (Sum.inl t) x = pderiv t x)
    (h2 : ∀ s x, d (Sum.inr s) (C x) = C (pderiv s x))
    (h3 : ∀ s t, d (Sum.inr s) (X t) = 0) (u : τ ⊕ σ) (y : MvPolynomial (τ ⊕ σ) Λ) :
    d u (sumAlgEquiv Λ τ σ y) = sumAlgEquiv Λ τ σ (pderiv u y) := by
  classical
  have eC : ∀ a : Λ, sumAlgEquiv Λ τ σ (C a) = C (C a) := fun a => by
    simp [sumAlgEquiv_C_inl]
  have eL : ∀ t : τ, sumAlgEquiv Λ τ σ (X (Sum.inl t)) = X t := fun t => by
    simp [sumAlgEquiv_X_inl]
  have eR : ∀ s : σ, sumAlgEquiv Λ τ σ (X (Sum.inr s)) = C (X s) := fun s => by
    simp [sumAlgEquiv_X_inr]
  have hX : ∀ v : τ ⊕ σ,
      d u (sumAlgEquiv Λ τ σ (X v)) = sumAlgEquiv Λ τ σ (pderiv u (X v)) := by
    intro v
    rcases u with t | s <;> rcases v with t' | s'
    · rw [eL, h1]
      by_cases h : t = t'
      · subst h; simp
      · rw [pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne (by simpa using Ne.symm h), map_zero]
    · rw [eR, h1, pderiv_C, pderiv_X_of_ne (by simp), map_zero]
    · rw [eL, h3, pderiv_X_of_ne (by simp), map_zero]
    · rw [eR, h2]
      by_cases h : s = s'
      · subst h; simp
      · rw [pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne (by simpa using Ne.symm h), map_zero,
          map_zero]
  induction y using MvPolynomial.induction_on with
  | C a =>
    rw [eC, pderiv_C, map_zero]
    rcases u with t | s
    · rw [h1, pderiv_C]
    · rw [h2, pderiv_C, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, hp, hX, map_add, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, map_mul]

theorem exists_generic_jacobian_data_iterated : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ τ : Type) [Finite σ] [Finite τ] (Q : Ideal (MvPolynomial τ (MvPolynomial σ Λ))) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C (MvPolynomial.C a) ∈ Q → a = 0) → ∀ d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ)) (MvPolynomial τ (MvPolynomial σ Λ)), (∀ t x, d (Sum.inl t) x = MvPolynomial.pderiv t x) → (∀ s x, d (Sum.inr s) (MvPolynomial.C x) = MvPolynomial.C (MvPolynomial.pderiv s x)) → (∀ s t, d (Sum.inr s) (MvPolynomial.X t) = 0) → ∃ (h : ℕ) (f : Fin h → MvPolynomial τ (MvPolynomial σ Λ)) (s : Fin h → τ ⊕ σ) (g : MvPolynomial τ (MvPolynomial σ Λ)), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ (Matrix.of fun i j => d (s i) (f j)).det ∉ Q := by
  intro Λ _ _ _ _ σ τ _ _ Q _ hQ d h1 h2 h3
  let e := MvPolynomial.sumAlgEquiv Λ τ σ
  have eC : ∀ a : Λ, e (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a) := fun a => by
    simp [e, MvPolynomial.sumAlgEquiv_C_inl]
  obtain ⟨h, f, s, g, hg, hf, hx, hdet⟩ := GlobalTheory.T.exists_local_generators_jacobian_det_not_mem Λ (τ ⊕ σ) (Q.comap e)
    (fun a ha => hQ a (by rw [← eC]; exact ha))
  refine ⟨h, fun j => e (f j), s, e g, hg, hf, fun x hxQ => ?_, ?_⟩
  · have h4 := hx (e.symm x) (by simpa [Ideal.mem_comap] using hxQ)
    have h5 := Ideal.mem_map_of_mem e h4
    rw [Ideal.map_span, ← Set.range_comp, map_mul, AlgEquiv.apply_symm_apply] at h5
    exact h5
  · intro hmem
    apply hdet
    rw [Ideal.mem_comap, AlgEquiv.map_det]
    convert hmem using 2
    ext i j : 1
    exact (derivation_sumAlgEquiv_eq_pderiv d h1 h2 h3 _ _).symm

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_jacobian_data_iterated_alt : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ τ : Type) [Finite σ] [Finite τ] (Q : Ideal (MvPolynomial τ (MvPolynomial σ Λ))) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C (MvPolynomial.C a) ∈ Q → a = 0) → ∀ d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ)) (MvPolynomial τ (MvPolynomial σ Λ)), (∀ t x, d (Sum.inl t) x = MvPolynomial.pderiv t x) → (∀ s x, d (Sum.inr s) (MvPolynomial.C x) = MvPolynomial.C (MvPolynomial.pderiv s x)) → (∀ s t, d (Sum.inr s) (MvPolynomial.X t) = 0) → ∃ (h : ℕ) (f : Fin h → MvPolynomial τ (MvPolynomial σ Λ)) (s : Fin h → τ ⊕ σ) (g : MvPolynomial τ (MvPolynomial σ Λ)), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ (Matrix.of fun i j => d (s i) (f j)).det ∉ Q := by
  atlas_forward_decl GlobalTheory.exists_generic_jacobian_data_iterated
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem mvPolynomial_tensor_baseChange_ringEquiv :
    ∀ (S B K τ : Type) [CommRing S] [CommRing B] [CommRing K] [Algebra S B] [Algebra S K]
      [Algebra (MvPolynomial τ S) K] [IsScalarTower S (MvPolynomial τ S) K],
      letI : Algebra (MvPolynomial τ S) (MvPolynomial τ B) :=
        (MvPolynomial.map (algebraMap S B)).toAlgebra
      Nonempty (MvPolynomial τ B ⊗[MvPolynomial τ S] K ≃+* B ⊗[S] K) := by
  intro S B K τ _ _ _ _ _ _ _
  letI : Algebra (MvPolynomial τ S) (MvPolynomial τ B) := MvPolynomial.algebraMvPolynomial
  let e : MvPolynomial τ S ⊗[S] B ≃ₐ[MvPolynomial τ S] MvPolynomial τ B :=
    Algebra.IsPushout.equiv S (MvPolynomial τ S) B (MvPolynomial τ B)
  exact ⟨(Algebra.TensorProduct.comm (MvPolynomial τ S) (MvPolynomial τ B) K).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[MvPolynomial τ S] K) e.symm).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange S (MvPolynomial τ S) (MvPolynomial τ S) K B).toRingEquiv.trans
        (Algebra.TensorProduct.comm S K B).toRingEquiv))⟩

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPolynomial_tensor_baseChange_ringEquiv' : ∀ (S B K τ : Type) [CommRing S] [CommRing B] [CommRing K] [Algebra S B] [Algebra S K] [Algebra (MvPolynomial τ S) K] [IsScalarTower S (MvPolynomial τ S) K], letI : Algebra (MvPolynomial τ S) (MvPolynomial τ B) := (MvPolynomial.map (algebraMap S B)).toAlgebra; Nonempty (MvPolynomial τ B ⊗[MvPolynomial τ S] K ≃+* B ⊗[S] K) := by
  atlas_forward_decl GlobalTheory.mvPolynomial_tensor_baseChange_ringEquiv
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem regularFibre_of_liftedPartialDerivations :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (B K : Type) [CommRing B] [IsRegularRing B] [Algebra (MvPolynomial σ Λ) B] [Field K] [Algebra (MvPolynomial σ Λ) K] [Algebra.EssFiniteType (MvPolynomial σ Λ) K], (∀ a : Λ, algebraMap (MvPolynomial σ Λ) K (MvPolynomial.C a) = 0 → a = 0) → (∀ s : σ, ∃ D : Derivation ℤ B B, ∀ x, D (algebraMap (MvPolynomial σ Λ) B x) = algebraMap (MvPolynomial σ Λ) B (MvPolynomial.pderiv s x)) → IsRegularRing (B ⊗[MvPolynomial σ Λ] K) := by
  intro Λ _ _ _ _ σ _ B K _ _ _ _ _ _ hΛ hlift
  obtain ⟨F, hF⟩ := (Algebra.essFiniteType_iff (R := MvPolynomial σ Λ) (S := K)).1 inferInstance
  let φ : MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ) →ₐ[MvPolynomial σ Λ] K :=
    MvPolynomial.aeval (fun z : ↥(F : Set K) => (z : K))
  letI : Algebra (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) K := φ.toRingHom.toAlgebra
  haveI : IsScalarTower (MvPolynomial σ Λ) (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) K :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  letI : Algebra (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) (MvPolynomial (↥(F : Set K)) B) :=
    (MvPolynomial.map (algebraMap (MvPolynomial σ Λ) B)).toAlgebra
  have hC : ∀ x, algebraMap (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) K (MvPolynomial.C x) =
      algebraMap (MvPolynomial σ Λ) K x := fun x => MvPolynomial.aeval_C _ _
  set Q := RingHom.ker (algebraMap (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) K) with hQdef
  haveI : Q.IsPrime := RingHom.ker_isPrime _
  have hfrac : ∀ y : K, ∃ a b : MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ), b ∉ Q ∧
      y * algebraMap _ K b = algebraMap _ K a := by
    intro y
    obtain ⟨t, ht, htu, hyt⟩ := hF y
    rw [Algebra.adjoin_eq_range] at ht hyt
    obtain ⟨b, hb⟩ := ht
    obtain ⟨a, ha⟩ := hyt
    refine ⟨a, b, ?_, ?_⟩
    · rw [hQdef, RingHom.mem_ker]
      change φ b ≠ 0
      rw [show φ b = t from hb]
      exact htu.ne_zero
    · change y * φ b = φ a
      rw [show φ b = t from hb, show φ a = y * t from ha]
  have hΛQ : ∀ a : Λ, MvPolynomial.C (MvPolynomial.C a) ∈ Q → a = 0 := by
    intro a ha
    rw [hQdef, RingHom.mem_ker, hC] at ha
    exact hΛ a ha
  choose Dσ hDσ using hlift
  choose dσ hdσC hdσX using fun s : σ => GlobalTheory.T.exists_derivation_extend_mvPolynomial (MvPolynomial σ Λ) (↥(F : Set K))
    ((MvPolynomial.pderiv s : Derivation Λ (MvPolynomial σ Λ) (MvPolynomial σ Λ)).restrictScalars ℤ)
  choose Eσ hEσC hEσX using fun s : σ => GlobalTheory.T.exists_derivation_extend_mvPolynomial B (↥(F : Set K)) (Dσ s)
  let d : (↥(F : Set K)) ⊕ σ → Derivation ℤ (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ))
      (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) :=
    Sum.elim (fun t => (MvPolynomial.pderiv t).restrictScalars ℤ) dσ
  let D : (↥(F : Set K)) ⊕ σ → Derivation ℤ (MvPolynomial (↥(F : Set K)) B) (MvPolynomial (↥(F : Set K)) B) :=
    Sum.elim (fun t => (MvPolynomial.pderiv t).restrictScalars ℤ) Eσ
  have hcompat : ∀ u x, D u (algebraMap _ (MvPolynomial (↥(F : Set K)) B) x) =
      algebraMap _ (MvPolynomial (↥(F : Set K)) B) (d u x) := by
    intro u x
    change D u (MvPolynomial.map (algebraMap (MvPolynomial σ Λ) B) x) =
      MvPolynomial.map (algebraMap (MvPolynomial σ Λ) B) (d u x)
    rcases u with t | s
    · exact MvPolynomial.pderiv_map
    · change Eσ s _ = MvPolynomial.map _ (dσ s x)
      induction x using MvPolynomial.induction_on with
      | C a =>
        rw [MvPolynomial.map_C, hEσC, hDσ, hdσC, MvPolynomial.map_C]
        rfl
      | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
      | mul_X p t ih =>
        rw [map_mul, Derivation.leibniz, Derivation.leibniz, MvPolynomial.map_X, hEσX, hdσX, ih]
        simp [smul_eq_mul]
  obtain ⟨h, f, s, g, hg, hfQ, hQspan, hdet⟩ :=
    GlobalTheory.T.exists_generic_jacobian_data_iterated_alt Λ σ (↥(F : Set K)) Q hΛQ d (fun t x => rfl) (fun s x => hdσC s x) (fun s t => hdσX s t)
  have hreg : IsRegularRing (MvPolynomial (↥(F : Set K)) B ⊗[MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)] K) :=
    GlobalTheory.T.isRegular_fibre_of_jacobian_derivations _ _ K Q rfl hfrac h f g (fun i => d (s i)) (fun i => D (s i))
      (fun i x => hcompat (s i) x) hg hfQ hQspan hdet
  obtain ⟨e⟩ := GlobalTheory.T.mvPolynomial_tensor_baseChange_ringEquiv' (MvPolynomial σ Λ) B K (↥(F : Set K))
  exact IsRegularRing.of_ringEquiv e

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_fibre_of_lifted_partialDerivations : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (B K : Type) [CommRing B] [IsRegularRing B] [Algebra (MvPolynomial σ Λ) B] [Field K] [Algebra (MvPolynomial σ Λ) K] [Algebra.EssFiniteType (MvPolynomial σ Λ) K], (∀ a : Λ, algebraMap (MvPolynomial σ Λ) K (MvPolynomial.C a) = 0 → a = 0) → (∀ s : σ, ∃ D : Derivation ℤ B B, ∀ x, D (algebraMap (MvPolynomial σ Λ) B x) = algebraMap (MvPolynomial σ Λ) B (MvPolynomial.pderiv s x)) → IsRegularRing (B ⊗[MvPolynomial σ Λ] K) := by
  atlas_forward_decl GlobalTheory.regularFibre_of_liftedPartialDerivations
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isRegularRing_adicCompletion_tensor_of_mvPolynomial :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (n : ℕ)
      (P : Ideal (MvPolynomial (Fin n) Λ)) [P.IsPrime] (K : Type) [Field K]
      [Algebra (Localization.AtPrime P) K] [Algebra.EssFiniteType (Localization.AtPrime P) K],
      (∀ a : Λ, algebraMap (Localization.AtPrime P) K
        (algebraMap Λ (Localization.AtPrime P) a) = 0 → a = 0) →
      IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime P))
        (Localization.AtPrime P) ⊗[Localization.AtPrime P] K) := by
  intro Λ _ _ _ _ n P _ K _ _ _ hinj
  let S₀ := MvPolynomial (Fin n) Λ
  let R := Localization.AtPrime P
  let B := AdicCompletion (maximalIdeal R) R
  haveI : IsRegularLocalRing R := inferInstance
  haveI : IsRegularLocalRing B := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion R
  haveI : IsRegularRing B := GlobalTheory.isRegularRing_of_isRegularLocalRing B
  letI : Algebra S₀ K := ((algebraMap R K).comp (algebraMap S₀ R)).toAlgebra
  haveI : IsScalarTower S₀ R K := .of_algebraMap_eq fun _ => rfl
  haveI : Algebra.EssFiniteType S₀ R := Algebra.EssFiniteType.of_isLocalization R P.primeCompl
  haveI : Algebra.EssFiniteType S₀ K := Algebra.EssFiniteType.comp S₀ R K
  have hC : ∀ a : Λ, algebraMap S₀ K (MvPolynomial.C a) = 0 → a = 0 := by
    intro a ha
    apply hinj a
    rw [IsScalarTower.algebraMap_apply Λ S₀ R a]
    exact ha
  have hD : ∀ s : Fin n, ∃ D : Derivation ℤ B B, ∀ x,
      D (algebraMap S₀ B x) = algebraMap S₀ B (MvPolynomial.pderiv s x) := fun s =>
    GlobalTheory.T.exists_derivation_extend_adicCompletion_localization S₀ P ((MvPolynomial.pderiv s).restrictScalars ℤ)
  have hD' : ∀ s : Fin n, ∃ D : @Derivation ℤ B B _ _ _ (Ring.toIntAlgebra B) _ _, ∀ x,
      D (algebraMap S₀ B x) = algebraMap S₀ B (MvPolynomial.pderiv s x) := by
    intro s
    obtain ⟨D, hD⟩ := hD s
    exact ⟨@Derivation.mk ℤ B B _ _ _ (Ring.toIntAlgebra B) _ _ D.toLinearMap
      D.map_one_eq_zero' D.leibniz', hD⟩
  have h := GlobalTheory.T.regular_fibre_of_lifted_partialDerivations Λ (Fin n) B K hC hD'
  let e : B ⊗[R] K ≃ₐ[R] B ⊗[S₀] K := IsLocalization.algebraTensorEquiv P.primeCompl R B K
  exact IsRegularRing.of_ringEquiv e.symm.toRingEquiv

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularRing_formal_fibre_mvPolynomial_perfect : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (n : ℕ) (P : Ideal (MvPolynomial (Fin n) Λ)) [P.IsPrime] (K : Type) [Field K] [Algebra (Localization.AtPrime P) K] [Algebra.EssFiniteType (Localization.AtPrime P) K], (∀ a : Λ, algebraMap (Localization.AtPrime P) K (algebraMap Λ (Localization.AtPrime P) a) = 0 → a = 0) → IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P) ⊗[Localization.AtPrime P] K) := by
  atlas_forward_decl GlobalTheory.isRegularRing_adicCompletion_tensor_of_mvPolynomial
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory.AdicSurj

open AdicCompletion

variable (B : Type) {A : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)

theorem mem_smul_top_iff (n : ℕ) (b : B) :
    b ∈ (J ^ n • ⊤ : Submodule A B) ↔ b ∈ (J.map (algebraMap A B)) ^ n := by
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]

theorem pow_le_comap (n : ℕ) :
    J ^ n ≤ ((J.map (algebraMap A B)) ^ n).comap (algebraMap A B) := by
  rw [← Ideal.map_pow]; exact Ideal.le_comap_map

noncomputable def lev (n : ℕ) :
    AdicCompletion J A →+* B ⧸ (J.map (algebraMap A B)) ^ n :=
  (Ideal.quotientMap _ (algebraMap A B) (pow_le_comap B J n)).comp (evalₐ J n).toRingHom

theorem lev_mk (n : ℕ) (s : AdicCauchySequence J A) :
    lev B J n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ (algebraMap A B (s n)) := by
  simp [lev, evalₐ_mk, Ideal.quotientMap_mk]

theorem lev_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow _ hle).comp (lev B J n) = lev B J m := by
  ext x
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  have h1 := s.property hle
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  simp only [RingHom.comp_apply, lev_mk]
  rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq, ← map_sub]
  have h3 : s n - s m ∈ J ^ m := by rw [← neg_sub]; exact neg_mem h1
  exact Ideal.mem_comap.mp (pow_le_comap B J m h3)

noncomputable def psi : AdicCompletion J A →+* AdicCompletion (J.map (algebraMap A B)) B :=
  AdicCompletion.liftRingHom _ (lev B J) (fun hle ↦ lev_compat B J hle)

theorem evalₐ_psi (n : ℕ) (x : AdicCompletion J A) :
    evalₐ _ n (psi B J x) = lev B J n x := by
  simp [psi]

theorem psi_algebraMap (a : A) :
    psi B J (algebraMap A (AdicCompletion J A) a) =
      algebraMap A (AdicCompletion (J.map (algebraMap A B)) B) a := by
  refine ext_evalₐ fun n ↦ ?_
  rw [evalₐ_psi, lev, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
    Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk, AdicCompletion.algebraMap_apply, evalₐ_of]

theorem map_val_mk_eq_iff (s : AdicCauchySequence J A) (n : ℕ) (c : B) :
    (map J (Algebra.linearMap A B) (AdicCompletion.mk J A s)).val n = Submodule.Quotient.mk c ↔
      lev B J n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ c := by
  rw [map_val_apply, mk_apply_coe, lev_mk, Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply,
    Submodule.Quotient.eq, Ideal.Quotient.eq, mem_smul_top_iff]
  rfl

theorem psi_surjective [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B)) :
    Function.Surjective (psi B J) := by
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.mk_surjective _ _ y
  let t' : AdicCauchySequence J B := ⟨t.val, fun {m n} hmn ↦ by
    have h := t.property hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
    rw [SModEq.sub_mem, mem_smul_top_iff]; exact h⟩
  obtain ⟨x, hx⟩ := map_surjective J (f := Algebra.linearMap A B) hs (AdicCompletion.mk J _ t')
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  refine ⟨AdicCompletion.mk J A s, ext_evalₐ fun n ↦ ?_⟩
  rw [evalₐ_psi, evalₐ_mk]
  refine (map_val_mk_eq_iff B J s n (t n)).mp ?_
  rw [hx]; rfl

theorem ker_psi [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B)) :
    RingHom.ker (psi B J) =
      Ideal.map (algebraMap A (AdicCompletion J A)) (LinearMap.ker (Algebra.linearMap A B)) := by
  set q := LinearMap.ker (Algebra.linearMap A B)
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have hz : map J (Algebra.linearMap A B) x = 0 := by
      obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
      ext n
      have := (map_val_mk_eq_iff B J s n 0).mpr
        (by rw [← evalₐ_psi, hx, _root_.map_zero, _root_.map_zero])
      simpa using this
    obtain ⟨y, rfl⟩ := ((AdicCompletion.map_exact (I := J) (f := q.subtype) (g := Algebra.linearMap A B)
      Subtype.val_injective (LinearMap.exact_subtype_ker_map _) hs) x).mp hz
    obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite J q y
    clear hx hz
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [ofTensorProduct_tmul, map_smul, map_of, smul_eq_mul]
      have hm : (of J A) (q.subtype m) = algebraMap A (AdicCompletion J A) (m : A) := by
        rw [AdicCompletion.algebraMap_apply]; rfl
      rw [hm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ m.2)
    | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, psi_algebraMap, AdicCompletion.algebraMap_apply]
    have : algebraMap A B a = 0 := LinearMap.mem_ker.mp ha
    rw [this, _root_.map_zero]

end GlobalTheory.AdicSurj

namespace GlobalTheory.AdicSurj

open AdicCompletion

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)

instance isScalarTower_adic :
    IsScalarTower A B (AdicCompletion (J.map (algebraMap A B)) B) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

noncomputable def psiₐ :
    AdicCompletion J A →ₐ[A] AdicCompletion (J.map (algebraMap A B)) B :=
  { psi B J with commutes' := psi_algebraMap B J }

noncomputable def theta :
    B ⊗[A] AdicCompletion J A →ₐ[B] AdicCompletion (J.map (algebraMap A B)) B :=
  Algebra.TensorProduct.lift (Algebra.ofId B _) (psiₐ J) fun _ _ ↦ Commute.all _ _

theorem theta_bijective [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B)) :
    Function.Bijective (theta (B := B) J) := by
  let e := RingHom.quotientKerEquivOfSurjective (psi_surjective B J hs)
  have hker : RingHom.ker (psi B J) ≤
      RingHom.ker (Algebra.TensorProduct.includeRight (R := A) (A := B)
        (B := AdicCompletion J A)).toRingHom := by
    rw [ker_psi B J hs, Ideal.map_le_iff_le_comap]
    intro a ha
    have h0 : algebraMap A B a = 0 := LinearMap.mem_ker.mp ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change (1 : B) ⊗ₜ[A] algebraMap A (AdicCompletion J A) a = 0
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, h0, zero_mul,
      TensorProduct.zero_tmul]
  let σ : AdicCompletion (J.map (algebraMap A B)) B →+* B ⊗[A] AdicCompletion J A :=
    (Ideal.Quotient.lift _ _ hker).comp e.symm.toRingHom
  have hσ : ∀ x, σ (psi B J x) = 1 ⊗ₜ[A] x := by
    intro x
    have : e.symm (psi B J x) = Ideal.Quotient.mk _ x := e.symm_apply_eq.mpr rfl
    simp only [σ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this,
      Ideal.Quotient.lift_mk]
    rfl
  have hleft : ∀ t, σ (theta J t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul b x =>
      obtain ⟨a, rfl⟩ := hs b
      rw [theta, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
        ← IsScalarTower.algebraMap_apply, ← psi_algebraMap B J a]
      change σ (psi B J _ * psi B J x) = _
      rw [← map_mul, hσ, ← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  refine ⟨Function.LeftInverse.injective hleft, fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := psi_surjective B J hs y
  refine ⟨1 ⊗ₜ[A] x, ?_⟩
  rw [theta, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

theorem tensor_ringEquiv [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B))
    (I : Ideal B) (hI : I = J.map (algebraMap A B)) (K : Type) [CommRing K] [Algebra B K] [Algebra A K]
    [IsScalarTower A B K] :
    Nonempty (AdicCompletion I B ⊗[B] K ≃+* AdicCompletion J A ⊗[A] K) := by
  subst hI
  let θ := AlgEquiv.ofBijective (theta (B := B) J) (theta_bijective J hs)
  exact ⟨(Algebra.TensorProduct.comm B _ K).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[B] K) θ.symm).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange A B B K (AdicCompletion J A)).toRingEquiv.trans
    (Algebra.TensorProduct.comm A K (AdicCompletion J A)).toRingEquiv))⟩

end GlobalTheory.AdicSurj

theorem GlobalTheory.adicCompletion_tensor_quotient_ringEquiv :
    ∀ (R₀ R K : Type) [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀] [CommRing R] [IsLocalRing R]
      [Algebra R₀ R] [CommRing K] [Algebra R K] [Algebra R₀ K] [IsScalarTower R₀ R K],
      Function.Surjective (algebraMap R₀ R) →
        Nonempty (AdicCompletion (maximalIdeal R) R ⊗[R] K ≃+*
          AdicCompletion (maximalIdeal R₀) R₀ ⊗[R₀] K) := by
  intro R₀ R K _ _ _ _ _ _ _ _ _ _ hs
  have hk : RingHom.ker (algebraMap R₀ R) ≤ maximalIdeal R₀ :=
    le_maximalIdeal (RingHom.ker_ne_top _)
  have hmax : ((maximalIdeal R₀).map (algebraMap R₀ R)).IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (hf := hs) (H := maximalIdeal.isMaximal R₀) with h | h
    · exfalso
      have h1 : (1 : R) ∈ (maximalIdeal R₀).map (algebraMap R₀ R) := h ▸ Submodule.mem_top
      obtain ⟨a, ha, hfa⟩ := (Ideal.mem_map_iff_of_surjective _ hs).mp h1
      have h2 : 1 - a ∈ maximalIdeal R₀ := hk (by rw [RingHom.mem_ker, map_sub, hfa, map_one, sub_self])
      have h3 : (1 : R₀) ∈ maximalIdeal R₀ := by simpa using add_mem h2 ha
      exact (maximalIdeal.isMaximal R₀).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
    · exact h
  exact GlobalTheory.AdicSurj.tensor_ringEquiv (maximalIdeal R₀) hs _ (eq_maximalIdeal hmax).symm K
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_adicCompletion_tensor_ringEquiv_of_surjective : ∀ (R₀ R K : Type) [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀] [CommRing R] [IsLocalRing R] [Algebra R₀ R] [CommRing K] [Algebra R K] [Algebra R₀ K] [IsScalarTower R₀ R K], Function.Surjective (algebraMap R₀ R) → Nonempty (AdicCompletion (maximalIdeal R) R ⊗[R] K ≃+* AdicCompletion (maximalIdeal R₀) R₀ ⊗[R₀] K) := by
  atlas_forward_decl GlobalTheory.adicCompletion_tensor_quotient_ringEquiv
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem formalFibre_isRegularRing_of_essFiniteType :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)]
      (R K : Type) [CommRing R] [IsLocalRing R] [Algebra Λ R] [Algebra.EssFiniteType Λ R]
      [Field K] [Algebra R K] [Algebra.EssFiniteType R K],
      (∀ a : Λ, algebraMap R K (algebraMap Λ R a) = 0 → a = 0) →
      IsRegularRing (AdicCompletion (maximalIdeal R) R ⊗[R] K) := by
  intro Λ _ _ _ _ R K _ _ _ _ _ _ _ hK
  obtain ⟨n, P, hP, φ, hφ⟩ := GlobalTheory.T.exists_surj_localization_mvPolynomial_of_essFiniteType_local Λ R
  let R₀ := Localization.AtPrime P
  letI : Algebra R₀ R := φ.toRingHom.toAlgebra
  letI : Algebra R₀ K := ((algebraMap R K).comp φ.toRingHom).toAlgebra
  haveI : IsScalarTower R₀ R K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsNoetherianRing R₀ := IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hsurj : Function.Surjective (algebraMap R₀ R) := hφ
  haveI : Algebra.FiniteType R₀ R := Algebra.FiniteType.of_surjective (Algebra.ofId R₀ R) hsurj
  haveI : Algebra.EssFiniteType R₀ R := inferInstance
  haveI : Algebra.EssFiniteType R₀ K := Algebra.EssFiniteType.comp R₀ R K
  have hK₀ : ∀ a : Λ, algebraMap R₀ K (algebraMap Λ R₀ a) = 0 → a = 0 := by
    intro a ha
    apply hK a
    have h1 : algebraMap R₀ K (algebraMap Λ R₀ a) = algebraMap R K (φ (algebraMap Λ R₀ a)) := rfl
    rw [h1, φ.commutes] at ha
    exact ha
  have hreg := GlobalTheory.T.isRegularRing_formal_fibre_mvPolynomial_perfect Λ n P K hK₀
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_adicCompletion_tensor_ringEquiv_of_surjective R₀ R K hsurj
  exact IsRegularRing.of_ringEquiv e.symm

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularRing_formalFibre_of_essFiniteType : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (R K : Type) [CommRing R] [IsLocalRing R] [Algebra Λ R] [Algebra.EssFiniteType Λ R] [Field K] [Algebra R K] [Algebra.EssFiniteType R K], (∀ a : Λ, algebraMap R K (algebraMap Λ R a) = 0 → a = 0) → IsRegularRing (AdicCompletion (maximalIdeal R) R ⊗[R] K) := by
  atlas_forward_decl GlobalTheory.formalFibre_isRegularRing_of_essFiniteType
end

section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem perfectField_fractionRing_zmod (p : ℕ) [Fact p.Prime] :
    PerfectField (FractionRing (ZMod p)) :=
  PerfectField.of_ringEquiv (FractionRing.algEquiv (ZMod p) (ZMod p)).symm.toRingEquiv

theorem formalFibre_isRegularRing_of_essFiniteType_int :
    ∀ (R K : Type) [CommRing R] [IsLocalRing R] [Algebra.EssFiniteType ℤ R] [Field K] [Algebra R K]
      [Algebra.EssFiniteType R K], IsRegularRing (AdicCompletion (maximalIdeal R) R ⊗[R] K) := by
  intro R K _ _ _ _ _ _
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
  ·
    set p := ringChar K with hpdef
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℤ R
    have hpK : algebraMap R K (p : R) = 0 := by
      rw [map_natCast]; exact CharP.cast_eq_zero K p
    have hnu : ((p : ℕ) : R) ∈ nonunits R := fun hu => by
      have := hu.map (algebraMap R K); rw [hpK] at this; exact not_isUnit_zero this
    let I : Ideal R := Ideal.span {((p : ℕ) : R)}
    haveI : CharP (R ⧸ I) p := CharP.quotient R p hnu
    have hI : I ≠ ⊤ := by
      exact fun h => hnu (Ideal.span_singleton_eq_top.mp h)
    haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
    haveI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hker : I ≤ RingHom.ker (algebraMap R K) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact hpK
    letI : Algebra (R ⧸ I) K := (Ideal.Quotient.lift I (algebraMap R K) hker).toAlgebra
    haveI : IsScalarTower R (R ⧸ I) K := IsScalarTower.of_algebraMap_eq fun x => rfl
    haveI : Algebra.EssFiniteType R (R ⧸ I) :=
      Algebra.EssFiniteType.of_surjective (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective
    haveI : Algebra.EssFiniteType ℤ (R ⧸ I) := Algebra.EssFiniteType.comp ℤ R (R ⧸ I)
    letI : Algebra (ZMod p) (R ⧸ I) := ZMod.algebra (R ⧸ I) p
    haveI : Algebra.EssFiniteType (ZMod p) (R ⧸ I) := Algebra.EssFiniteType.of_comp ℤ (ZMod p) (R ⧸ I)
    haveI : Algebra.EssFiniteType (R ⧸ I) K := Algebra.EssFiniteType.of_comp R (R ⧸ I) K
    haveI := perfectField_fractionRing_zmod p
    have hinj : ∀ a : ZMod p, algebraMap (R ⧸ I) K (algebraMap (ZMod p) (R ⧸ I) a) = 0 → a = 0 :=
      fun a ha => ((algebraMap (R ⧸ I) K).comp (algebraMap (ZMod p) (R ⧸ I))).injective
        (by simpa using ha)
    have hreg := GlobalTheory.T.isRegularRing_formalFibre_of_essFiniteType (ZMod p) (R ⧸ I) K hinj
    obtain ⟨e⟩ := GlobalTheory.T.nonempty_adicCompletion_tensor_ringEquiv_of_surjective R (R ⧸ I) K Ideal.Quotient.mk_surjective
    exact IsRegularRing.of_ringEquiv e
  ·
    haveI : CharP K 0 := by rw [← h0]; exact ringChar.charP K
    haveI : CharZero K := CharP.charP_to_charZero K
    refine GlobalTheory.T.isRegularRing_formalFibre_of_essFiniteType ℤ R K ?_
    intro a ha
    rw [eq_intCast (algebraMap ℤ R), map_intCast] at ha
    exact_mod_cast ha

end GlobalTheory
end
