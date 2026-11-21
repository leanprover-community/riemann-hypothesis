import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEtaleOfIsEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedEquationPullbackEtaleOverAffineSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeomRegFibAdicCompletionOfEssFiniteTypeInt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinTypeQE
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsRegularRingEssFiniteTypeInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingQuotientOfDetDerivationUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataOfPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingOfRegularQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalLocalGeneratorsStatement

section
section
open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem geomRegFib_of_isRegularRing_essFiniteType :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B],
      (∀ (K : Type) [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (B ⊗[R] K)) →
        FinalTheorems.GeomRegFib R B := by
  intro R B _ _ _ h P _ K _ _ _ _ hfg
  haveI : Algebra.EssFiniteType P.ResidueField K := IntermediateField.fg_top_iff.mp hfg
  haveI : Algebra.EssFiniteType R K := Algebra.EssFiniteType.comp R P.ResidueField K
  haveI hr : IsRegularRing (B ⊗[R] K) := h K
  exact ⟨inferInstance, fun Q _ => hr.isRegularLocalRing_localization Q⟩

end GlobalTheory
end

open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geomRegFib_of_isRegularRing_tensor_essFiniteType : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B], (∀ (K : Type) [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (B ⊗[R] K)) → FinalTheorems.GeomRegFib R B := by
  atlas_forward_decl GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType
end

section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalFibre_isRegularRing_essFiniteType_int : ∀ (R K : Type) [CommRing R] [IsLocalRing R] [Algebra.EssFiniteType ℤ R] [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (AdicCompletion (maximalIdeal R) R ⊗[R] K) := by
  first | exact @GlobalTheory.formalFibre_isRegularRing_of_essFiniteType_int | exact GlobalTheory.formalFibre_isRegularRing_of_essFiniteType_int | (intros; apply GlobalTheory.formalFibre_isRegularRing_of_essFiniteType_int <;> assumption)
end

section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem localization_quotient_comap_equiv :
    ∀ (S B : Type) [CommRing S] [CommRing B] (φ : S →+* B), Function.Surjective φ →
      ∀ (p q : Ideal B) [q.IsPrime],
        Nonempty ((Localization.AtPrime (q.comap φ) ⧸
            (p.comap φ).map (algebraMap S (Localization.AtPrime (q.comap φ)))) ≃+*
          (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q)))) := by
  intro S B _ _ φ hφ p q _
  let ψ := Localization.localRingHom (q.comap φ) q φ rfl
  let f := (Ideal.Quotient.mk (p.map (algebraMap B (Localization.AtPrime q)))).comp ψ
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    obtain ⟨a, rfl⟩ := hφ b
    obtain ⟨t₀, ht₀⟩ := hφ (t : B)
    have ht₀' : t₀ ∈ (q.comap φ).primeCompl := by
      show t₀ ∉ q.comap φ
      rw [Ideal.mem_comap, ht₀]
      exact t.2
    refine ⟨IsLocalization.mk' (Localization.AtPrime (q.comap φ)) a ⟨t₀, ht₀'⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext ht₀
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hψ
  have hker : RingHom.ker f = (p.comap φ).map (algebraMap S (Localization.AtPrime (q.comap φ))) := by
    ext x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (q.comap φ).primeCompl x
    simp only [RingHom.mem_ker, f, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ψ,
      Localization.localRingHom_mk']
    rw [IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_mem_map_algebraMap_iff]
    constructor
    · rintro ⟨t, ht, hta⟩
      obtain ⟨t₀, rfl⟩ := hφ t
      refine ⟨t₀, ?_, ?_⟩
      · show t₀ ∉ q.comap φ
        simpa [Ideal.mem_comap] using ht
      · simpa [Ideal.mem_comap, map_mul] using hta
    · rintro ⟨t₀, ht, hta⟩
      refine ⟨φ t₀, ?_, ?_⟩
      · show φ t₀ ∉ q
        simpa [Ideal.mem_comap] using ht
      · simpa [Ideal.mem_comap, map_mul] using hta
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hf)⟩

end GlobalTheory
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem prime_generically_regular_quotient :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)]
      (B : Type) [CommRing B] [Algebra Λ B] [Algebra.FiniteType Λ B] (p : Ideal B) [p.IsPrime],
      (∀ a : Λ, algebraMap Λ B a ∈ p → a = 0) → ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q →
        g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸
          p.map (algebraMap B (Localization.AtPrime q))) := by
  intro Λ _ _ _ _ B _ _ _ p _ hp
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType Λ B)
  set Q : Ideal (MvPolynomial (Fin n) Λ) := p.comap φ with hQdef
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQ : ∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0 := by
    intro a ha
    apply hp a
    have : φ (MvPolynomial.C a) ∈ p := ha
    rwa [MvPolynomial.algHom_C] at this
  obtain ⟨h, f, s, g₀, hg₀, hfQ, hgQ, hdet⟩ := GlobalTheory.T.exists_local_generators_jacobian_det_not_mem Λ (Fin n) Q hQ
  set δ := (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)).det with hδ
  refine ⟨φ (g₀ * δ), ?_, ?_⟩
  · intro hmem
    have : g₀ * δ ∈ Q := hmem
    rcases Ideal.IsPrime.mem_or_mem inferInstance this with h1 | h1
    · exact hg₀ h1
    · exact hdet h1
  · intro q _ hpq hgq
    set N : Ideal (MvPolynomial (Fin n) Λ) := q.comap φ with hN
    haveI : N.IsPrime := Ideal.comap_isPrime _ _
    have hQN : Q ≤ N := Ideal.comap_mono hpq
    have hgN : g₀ * δ ∉ N := hgq
    have hg₀N : g₀ ∉ N := fun h1 => hgN (N.mul_mem_right _ h1)
    have hδN : δ ∉ N := fun h1 => hgN (N.mul_mem_left _ h1)
    let D : Fin h → Derivation ℤ (MvPolynomial (Fin n) Λ) (MvPolynomial (Fin n) Λ) :=
      fun i => (MvPolynomial.pderiv (s i)).restrictScalars ℤ
    have hdetD : (Matrix.of fun i j => D i (f j)).det ∉ N := by
      simpa [D] using hδN
    have hreg := GlobalTheory.T.isRegularLocalRing_quotient_of_det_derivation_unit (MvPolynomial (Fin n) Λ) h f D N (fun j => hQN (hfQ j)) hdetD
    have heq : (Ideal.span (Set.range f)).map
          (algebraMap (MvPolynomial (Fin n) Λ) (Localization.AtPrime N)) =
        Q.map (algebraMap (MvPolynomial (Fin n) Λ) (Localization.AtPrime N)) := by
      apply le_antisymm
      · apply Ideal.map_mono
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        exact hfQ j
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap]
        have hu : IsUnit (algebraMap (MvPolynomial (Fin n) Λ) (Localization.AtPrime N) g₀) :=
          IsLocalization.map_units (Localization.AtPrime N) (⟨g₀, hg₀N⟩ : N.primeCompl)
        rw [← Ideal.unit_mul_mem_iff_mem _ hu, ← map_mul]
        exact Ideal.mem_map_of_mem _ (hgQ x hx)
    rw [heq] at hreg
    obtain ⟨e⟩ := GlobalTheory.localization_quotient_comap_equiv (MvPolynomial (Fin n) Λ) B
      φ.toRingHom hφ p q
    haveI : IsRegularLocalRing (Localization.AtPrime (q.comap φ.toRingHom) ⧸
        (p.comap φ.toRingHom).map (algebraMap _ (Localization.AtPrime (q.comap φ.toRingHom)))) := hreg
    exact IsRegularLocalRing.of_ringEquiv e

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericallyRegular_quotient_dominating_prime : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (B : Type) [CommRing B] [Algebra Λ B] [Algebra.FiniteType Λ B] (p : Ideal B) [p.IsPrime], (∀ a : Λ, algebraMap Λ B a ∈ p → a = 0) → ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) := by
  atlas_forward_decl GlobalTheory.prime_generically_regular_quotient
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem generically_regular_quotient_of_finiteType_int :
    ∀ (B : Type) [CommRing B] [Algebra.FiniteType ℤ B] (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧
      ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q →
        IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) := by
  intro B _ _ p hp
  by_cases h : ∀ a : ℤ, algebraMap ℤ B a ∈ p → a = 0
  · exact GlobalTheory.T.exists_genericallyRegular_quotient_dominating_prime ℤ B p h
  push_neg at h
  obtain ⟨a, ha, ha0⟩ := h
  have hP : (p.comap (algebraMap ℤ B)) ≠ ⊥ := by
    intro hb
    apply ha0
    have : a ∈ p.comap (algebraMap ℤ B) := ha
    rw [hb] at this
    simpa using this
  obtain ⟨x, hx, hxp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (Ideal.IsPrime.comap _) hP
  set l := x.natAbs with hl
  have hlp : l.Prime := Int.prime_iff_natAbs_prime.mp hxp
  haveI : Fact l.Prime := ⟨hlp⟩
  have hlmem : (l : B) ∈ p := by
    have hx' : algebraMap ℤ B x ∈ p := hx
    rcases Int.natAbs_eq x with h1 | h1
    · rw [h1] at hx'
      simpa [hl] using hx'
    · rw [h1] at hx'
      simpa [hl] using hx'
  set I : Ideal B := Ideal.span {(l : B)} with hI
  let mk := Ideal.Quotient.mk I
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker mk = I := Ideal.mk_ker
  have hIp : I ≤ p := by
    rw [hI, Ideal.span_le]; simpa using hlmem
  have hl0 : ∀ a ∈ Ideal.span {((l : ℕ) : ℤ)}, (Int.castRingHom (B ⧸ I)) a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    have : ((l : ℕ) : B ⧸ I) = 0 := by
      have h0 : (Ideal.Quotient.mk I) (l : B) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span rfl)
      simpa using h0
    simp [this]
  let ψ : ZMod l →+* B ⧸ I :=
    (Ideal.Quotient.lift (Ideal.span {((l : ℕ) : ℤ)}) (Int.castRingHom (B ⧸ I)) hl0).comp
      (Int.quotientSpanNatEquivZMod l).symm.toRingHom
  letI : Algebra (ZMod l) (B ⧸ I) := ψ.toAlgebra
  haveI : IsScalarTower ℤ (ZMod l) (B ⧸ I) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : Algebra.FiniteType (ZMod l) (B ⧸ I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod l) (B ⧸ I)
  haveI : PerfectField (FractionRing (ZMod l)) := by
    have : Finite (FractionRing (ZMod l)) :=
      Finite.of_equiv _ (FractionRing.algEquiv (ZMod l) (ZMod l)).toEquiv.symm
    infer_instance

  have corr : ∀ (r : Ideal B), r.IsPrime → I ≤ r → (r.map mk).IsPrime ∧ (r.map mk).comap mk = r := by
    intro r hr hIr
    refine ⟨Ideal.map_isPrime_of_surjective hmk (by rw [hker]; exact hIr), ?_⟩
    rw [Ideal.comap_map_of_surjective' mk hmk, hker]
    exact sup_eq_left.mpr hIr
  obtain ⟨p', hp', rfl⟩ : ∃ p' : Ideal (B ⧸ I), p'.IsPrime ∧ p'.comap mk = p :=
    ⟨p.map mk, corr p hp hIp⟩
  have hdom : ∀ a : ZMod l, algebraMap (ZMod l) (B ⧸ I) a ∈ p' → a = 0 := by
    intro a ha
    by_contra ha0
    exact hp'.ne_top (Ideal.eq_top_of_isUnit_mem _ ha ((IsUnit.mk0 a ha0).map _))
  obtain ⟨g', hg'p, hg'⟩ := GlobalTheory.T.exists_genericallyRegular_quotient_dominating_prime (ZMod l) (B ⧸ I) p' hdom
  obtain ⟨g, rfl⟩ := hmk g'
  refine ⟨g, fun hg => hg'p hg, ?_⟩
  intro q hq hpq hgq
  have hIq : I ≤ q := hIp.trans hpq
  obtain ⟨q', hq', rfl⟩ : ∃ q' : Ideal (B ⧸ I), q'.IsPrime ∧ q'.comap mk = q :=
    ⟨q.map mk, corr q hq hIq⟩
  have hpq' : p' ≤ q' := by
    intro y hy
    obtain ⟨y, rfl⟩ := hmk y
    exact hpq hy
  have hreg := hg' q' hpq' (fun h => hgq h)
  obtain ⟨e⟩ := GlobalTheory.localization_quotient_comap_equiv B (B ⧸ I) mk hmk p' q'
  exact IsRegularLocalRing.of_ringEquiv e.symm

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_quotient_near_prime_finiteType_int : ∀ (B : Type) [CommRing B] [Algebra.FiniteType ℤ B] (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) := by
  atlas_forward_decl GlobalTheory.generically_regular_quotient_of_finiteType_int
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isOpen_of_stableUnderGeneralization_of_locally_open_in_closure :
    ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (U : Set (PrimeSpectrum B)),
      (∀ p q : PrimeSpectrum B, p ≤ q → q ∈ U → p ∈ U) →
      (∀ p ∈ U, ∃ g, g ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum B, p ≤ q → g ∉ q.asIdeal → q ∈ U) →
      IsOpen U := by
  intro B _ _ U hgen hloc
  classical
  set I := PrimeSpectrum.vanishingIdeal (Uᶜ) with hI
  have hIle : ∀ q : PrimeSpectrum B, q ∈ Uᶜ → I ≤ q.asIdeal := by
    intro q hq f hf
    exact (PrimeSpectrum.mem_vanishingIdeal _ f).1 hf q hq
  have key : ∀ x : PrimeSpectrum B, x.asIdeal ∈ I.minimalPrimes → x ∉ U := by
    intro x hx hxU
    obtain ⟨g, hg, hgU⟩ := hloc x hxU
    have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B I
    set S := hfin.toFinset.erase x.asIdeal with hS
    have hJ : ¬ S.inf id ≤ x.asIdeal := by
      intro h
      obtain ⟨P, hPS, hPx⟩ := (Ideal.IsPrime.inf_le' x.isPrime).1 h
      have hPm : P ∈ I.minimalPrimes := (Set.Finite.mem_toFinset hfin).1 (Finset.mem_of_mem_erase hPS)
      have hne : P ≠ x.asIdeal := Finset.ne_of_mem_erase hPS
      exact hne (le_antisymm hPx (hx.2 hPm.1 hPx))
    obtain ⟨c, hcJ, hcx⟩ := Set.not_subset.1 hJ
    have hgc : g * c ∈ I := by
      rw [hI, PrimeSpectrum.mem_vanishingIdeal]
      intro q hq
      obtain ⟨P, hPm, hPq⟩ := Ideal.exists_minimalPrimes_le (hIle q hq)
      by_cases hPx : P = x.asIdeal
      · by_cases hgq : g ∈ q.asIdeal
        · exact q.asIdeal.mul_mem_right c hgq
        · exact absurd (hgU q (show x.asIdeal ≤ q.asIdeal by rw [← hPx]; exact hPq) hgq) hq
      · have hPS : P ∈ S := Finset.mem_erase.2 ⟨hPx, (Set.Finite.mem_toFinset hfin).2 hPm⟩
        have : S.inf id ≤ P := Finset.inf_le (f := id) hPS
        exact q.asIdeal.mul_mem_left g (hPq (this hcJ))
    rcases x.isPrime.mem_or_mem (hx.1.2 hgc) with h | h
    · exact hg h
    · exact hcx h
  have hcl : IsClosed (Uᶜ) := by
    rw [← closure_subset_iff_isClosed, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    intro q hq
    have hIq : I ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).1 hq
    obtain ⟨P, hPm, hPq⟩ := Ideal.exists_minimalPrimes_le hIq
    intro hqU
    exact key ⟨P, hPm.1.1⟩ hPm (hgen _ _ hPq hqU)
  exact isClosed_compl_iff.1 hcl

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_locally_open : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (U : Set (PrimeSpectrum B)), (∀ p q : PrimeSpectrum B, p ≤ q → q ∈ U → p ∈ U) → (∀ p ∈ U, ∃ g, g ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum B, p ≤ q → g ∉ q.asIdeal → q ∈ U) → IsOpen U := by
  atlas_forward_decl GlobalTheory.isOpen_of_stableUnderGeneralization_of_locally_open_in_closure
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory.RegularAscent

open IsLocalRing TensorProduct in
private lemma spanFinrank_maximalIdeal_le_add (A : Type) [CommRing A] [IsLocalRing A]
    (J : Ideal A) [IsLocalRing (A ⧸ J)] (hJ : J.FG) (hm : (maximalIdeal (A ⧸ J)).FG) :
    (maximalIdeal A).spanFinrank ≤ J.spanFinrank + (maximalIdeal (A ⧸ J)).spanFinrank := by
  classical
  obtain ⟨T, hTc, hT⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hJ
  obtain ⟨U, hUc, hU⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hm
  let L : Finset A := U.image Quotient.out
  have hJm : J ≤ maximalIdeal A := by
    refine le_maximalIdeal fun h => ?_
    have : Subsingleton (A ⧸ J) := Ideal.Quotient.subsingleton_iff.mpr h
    exact not_subsingleton (A ⧸ J) this
  have hL : ∀ l ∈ L, l ∈ maximalIdeal A := by
    intro l hl
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hl
    have hu' : u ∈ maximalIdeal (A ⧸ J) := hU ▸ Ideal.subset_span hu
    intro hunit
    apply hu'
    have := hunit.map (Ideal.Quotient.mk J)
    rwa [Ideal.Quotient.mk_out] at this
  have hspan : maximalIdeal A = Ideal.span (↑(T ∪ L) : Set A) := by
    apply le_antisymm
    · intro x hx
      have hx' : Ideal.Quotient.mk J x ∈ Ideal.span (Ideal.Quotient.mk J '' (L : Set A)) := by
        have e : Ideal.Quotient.mk J '' (L : Set A) = (U : Set (A ⧸ J)) := by
          ext u; simp [L, Ideal.Quotient.mk_out]
        rw [e]
        change _ ∈ Submodule.span (A ⧸ J) _
        rw [hU]
        intro hunit
        obtain ⟨y, hy⟩ := hunit.exists_right_inv
        obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
        have h1 : x * y' - 1 ∈ J := Ideal.Quotient.eq.mp (by simpa using hy)
        apply (maximalIdeal.isMaximal A).ne_top
        rw [Ideal.eq_top_iff_one]
        simpa using Ideal.sub_mem _ (Ideal.mul_mem_right y' _ hx) (hJm h1)
      rw [← Ideal.map_span] at hx'
      obtain ⟨y, hy, hyx⟩ := Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective |>.mp hx'
      have hxy : x - y ∈ J := by
        rw [← Ideal.Quotient.eq]; exact hyx.symm
      rw [← hT] at hxy
      rw [Finset.coe_union, Ideal.span_union]
      have := Submodule.add_mem_sup hxy hy
      simpa using this
    · rw [Ideal.span_le]
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hJm (hT ▸ Ideal.subset_span hx)
      · exact hL x hx
  calc (maximalIdeal A).spanFinrank ≤ (T ∪ L).card := hspan ▸ _root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_span_finset_le _
    _ ≤ T.card + L.card := Finset.card_union_le _ _
    _ ≤ J.spanFinrank + (maximalIdeal (A ⧸ J)).spanFinrank := by
        rw [hTc, ← hUc]; gcongr; exact Finset.card_image_le

open IsLocalRing TensorProduct in
private lemma height_add_ringKrullDim_quotient_le' (A : Type) [CommRing A] (I : Ideal A)
    [I.IsPrime] : (I.height : WithBot ℕ∞) + ringKrullDim (A ⧸ I) ≤ ringKrullDim A := by
  let P : PrimeSpectrum A := ⟨I, inferInstance⟩
  have h1 : I.height = Order.height P := PrimeSpectrum.height_eq_orderHeight P
  have h2 : ringKrullDim (A ⧸ I) = (Order.coheight P : WithBot ℕ∞) := by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
    rfl
  have : Nonempty (PrimeSpectrum A) := ⟨P⟩
  rw [h1, h2, ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  norm_cast
  exact le_iSup (fun a : PrimeSpectrum A => Order.height a + Order.coheight a) P

open IsLocalRing TensorProduct in

theorem _root_.GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient (B : Type) [CommRing B]
    [IsNoetherianRing B] (p : Ideal B) [p.IsPrime]
    (hp : IsRegularLocalRing (Localization.AtPrime p)) :
    ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q →
      IsRegularLocalRing
        (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) →
      IsRegularLocalRing (Localization.AtPrime q) := by
  classical
  have hmfg : (maximalIdeal (Localization.AtPrime p)).FG := IsNoetherian.noetherian _
  obtain ⟨U, hUc, hU⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hmfg
  choose f hf using fun u : Localization.AtPrime p => IsLocalization.surj p.primeCompl u
  let T : Finset B := U.image fun u => (f u).1
  have hTp : ∀ t ∈ T, t ∈ p := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p, ← hf u]
    exact Ideal.mul_mem_right _ _ (hU ▸ Ideal.subset_span hu)
  have hTspan : p.map (algebraMap B (Localization.AtPrime p)) =
      Ideal.span (algebraMap B (Localization.AtPrime p) '' T) := by
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [← hU]
      change Ideal.span _ ≤ _
      rw [Ideal.span_le]
      intro u hu
      have hunit := IsLocalization.map_units (Localization.AtPrime p) (f u).2
      have e : u = algebraMap B _ (f u).1 * ↑hunit.unit⁻¹ := by
        rw [Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec]; exact hf u
      rw [e]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨(f u).1, Finset.mem_image_of_mem _ hu, rfl⟩)
    · rw [Ideal.span_le]
      rintro _ ⟨t, ht, rfl⟩
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ (hTp t ht)
  obtain ⟨V, hV⟩ := (IsNoetherian.noetherian p : p.FG)
  have hc : ∀ v ∈ V, ∃ c ∈ p.primeCompl, c * v ∈ Ideal.span (T : Set B) := by
    intro v hv
    rw [← IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl (Localization.AtPrime p),
      Ideal.map_span, ← hTspan]
    exact Ideal.mem_map_of_mem _ (hV ▸ Ideal.subset_span hv)
  choose! c hcp hcT using hc
  have hg : ∀ x ∈ p, (∏ v ∈ V, c v) * x ∈ Ideal.span (T : Set B) := by
    have : Ideal.span {∏ v ∈ V, c v} * p ≤ Ideal.span (T : Set B) := by
      rw [← hV, Ideal.span_mul_span', Ideal.span_le]
      rintro _ ⟨a, ha, v, hv, rfl⟩
      rw [Set.mem_singleton_iff.mp ha, ← Finset.prod_erase_mul V c hv]
      change (∏ x ∈ V.erase v, c x) * c v * v ∈ Ideal.span (T : Set B)
      rw [mul_assoc]
      exact Ideal.mul_mem_left _ _ (hcT v hv)
    exact Ideal.span_singleton_mul_le_iff.mp this
  refine ⟨∏ v ∈ V, c v, p.primeCompl.prod_mem fun v hv => hcp v hv, ?_⟩
  intro q _ hpq hgq hreg
  have hdisj : Disjoint (q.primeCompl : Set B) p :=
    Set.disjoint_left.mpr fun x hxq hxp => hxq (hpq hxp)
  have hI : p.map (algebraMap B (Localization.AtPrime q)) =
      Ideal.span (algebraMap B (Localization.AtPrime q) '' T) := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have hu : IsUnit (algebraMap B (Localization.AtPrime q) (∏ v ∈ V, c v)) :=
        IsLocalization.map_units (Localization.AtPrime q) (⟨_, hgq⟩ : q.primeCompl)
      have h2 : algebraMap B (Localization.AtPrime q) ((∏ v ∈ V, c v) * x) ∈
          Ideal.span (algebraMap B (Localization.AtPrime q) '' T) := by
        rw [← Ideal.map_span]; exact Ideal.mem_map_of_mem _ (hg x hx)
      rw [map_mul] at h2
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h2
    · rw [← Ideal.map_span]
      exact Ideal.map_mono (Ideal.span_le.mpr fun t ht => hTp t ht)
  have hIprime : (p.map (algebraMap B (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hdisj
  have hIcard : (p.map (algebraMap B (Localization.AtPrime q))).spanFinrank ≤ T.card := by
    rw [hI, ← Finset.coe_image]
    exact (_root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_span_finset_le _).trans Finset.card_image_le
  have hTcard : (T.card : WithBot ℕ∞) ≤ (p.map (algebraMap B (Localization.AtPrime q))).height := by
    have h1 : (p.map (algebraMap B (Localization.AtPrime q))).height = p.height := by
      rw [← IsLocalization.height_under q.primeCompl,
        IsLocalization.comap_map_of_isPrime_disjoint q.primeCompl _ ‹_› hdisj]
    have h2 : (p.height : WithBot ℕ∞) = (maximalIdeal (Localization.AtPrime p)).spanFinrank := by
      rw [← IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
        hp.spanFinrank_maximalIdeal]
    rw [h1, h2]
    exact_mod_cast (Finset.card_image_le.trans hUc.le)
  have := hreg.toIsLocalRing
  have hA := spanFinrank_maximalIdeal_le_add (Localization.AtPrime q)
    (p.map (algebraMap B (Localization.AtPrime q))) (IsNoetherian.noetherian _)
    (IsNoetherian.noetherian _)
  have hd := hreg.spanFinrank_maximalIdeal
  have hdim := height_add_ringKrullDim_quotient_le' (Localization.AtPrime q)
    (p.map (algebraMap B (Localization.AtPrime q)))
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc ((maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞)
      ≤ ((T.card + (maximalIdeal (Localization.AtPrime q ⧸
          p.map (algebraMap B (Localization.AtPrime q)))).spanFinrank : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast hA.trans (by omega)
    _ = (T.card : WithBot ℕ∞) + ringKrullDim (Localization.AtPrime q ⧸
          p.map (algebraMap B (Localization.AtPrime q))) := by
        push_cast; rw [hd]
    _ ≤ (p.map (algebraMap B (Localization.AtPrime q))).height + ringKrullDim
          (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) := by
        gcongr
    _ ≤ ringKrullDim (Localization.AtPrime q) := hdim

end GlobalTheory.RegularAscent
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_near_of_regular_quotient_prime : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (p : Ideal B) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p) → ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) → IsRegularLocalRing (Localization.AtPrime q) := by
  atlas_forward_decl GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isRegularLocalRing_atPrime_of_le {B : Type} [CommRing B] (p q : Ideal B) [p.IsPrime]
    [q.IsPrime] (hpq : p ≤ q) (hq : IsRegularLocalRing (Localization.AtPrime q)) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  have hd : Disjoint (q.primeCompl : Set B) (p : Set B) := by
    rw [Set.disjoint_left]
    intro x hx hxp
    exact hx (hpq hxp)
  let P' : Ideal (Localization.AtPrime q) := p.map (algebraMap B _)
  haveI hP' : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hd
  have hc : P'.comap (algebraMap B (Localization.AtPrime q)) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint q.primeCompl _ ‹p.IsPrime› hd
  have hsub : (P'.comap (algebraMap B (Localization.AtPrime q))).primeCompl = p.primeCompl := by
    ext x
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hc]
  haveI : IsRegularRing (Localization.AtPrime q) := isRegularRing_of_isRegularLocalRing _
  have hreg : IsRegularLocalRing (Localization.AtPrime P') :=
    IsRegularRing.isRegularLocalRing_localization P'
  haveI : IsLocalization p.primeCompl (Localization.AtPrime P') := by
    rw [← hsub]
    exact IsLocalization.isLocalization_atPrime_localization_atPrime q.primeCompl P'
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime P')
      (Localization.AtPrime p)).toRingEquiv

theorem isOpen_regularLocus_of_nagata : ∀ (B : Type) [CommRing B] [IsNoetherianRing B], (∀ (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q)))) → IsOpen {Q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime Q.asIdeal)} := by
  intro B _ _ hyp
  apply GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_locally_open B
  · intro p q hpq hq
    exact isRegularLocalRing_atPrime_of_le p.asIdeal q.asIdeal hpq hq
  · intro p hp
    obtain ⟨g₁, hg₁p, hg₁⟩ := hyp p.asIdeal
    obtain ⟨g₂, hg₂p, hg₂⟩ := GlobalTheory.T.exists_regular_near_of_regular_quotient_prime B p.asIdeal hp
    refine ⟨g₁ * g₂, fun h => (p.isPrime.mem_or_mem h).elim hg₁p hg₂p, ?_⟩
    intro q hpq hq
    have hq₁ : g₁ ∉ q.asIdeal := fun h => hq (q.asIdeal.mul_mem_right _ h)
    have hq₂ : g₂ ∉ q.asIdeal := fun h => hq (q.asIdeal.mul_mem_left _ h)
    exact hg₂ q.asIdeal hpq hq₂ (hg₁ q.asIdeal hpq hq₁)

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_regularLocus_of_nagata' : ∀ (B : Type) [CommRing B] [IsNoetherianRing B], (∀ (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q)))) → IsOpen {Q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime Q.asIdeal)} := by
  atlas_forward_decl GlobalTheory.isOpen_regularLocus_of_nagata
end

section
open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem qeRing_of_finiteType_int : ∀ (A : Type) [CommRing A] [Algebra.FiniteType ℤ A], FinalTheorems.QERing A := by
  intro A _ _
  have hN : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  refine ⟨hN, fun P _ => ⟨?_, ?_⟩, fun B _ _ _ => ?_⟩
  · exact AdicCompletion.flat_of_isNoetherian _
  · apply GlobalTheory.T.geomRegFib_of_isRegularRing_tensor_essFiniteType
    intro K _ _ _
    haveI : Algebra.EssFiniteType A (Localization.AtPrime P) :=
      Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
    haveI : Algebra.EssFiniteType ℤ (Localization.AtPrime P) :=
      Algebra.EssFiniteType.comp ℤ A (Localization.AtPrime P)
    have hZ : @Algebra.EssFiniteType ℤ (Localization.AtPrime P) _ _ (Ring.toIntAlgebra _) := by
      convert this
      exact Subsingleton.elim _ _
    exact @GlobalTheory.T.formalFibre_isRegularRing_essFiniteType_int (Localization.AtPrime P) K _ _ hZ _ _ _
  · haveI : Algebra.FiniteType ℤ B := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ A) ‹_›
    haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
    exact GlobalTheory.T.isOpen_regularLocus_of_nagata' B (fun p _ => GlobalTheory.T.exists_regular_quotient_near_prime_finiteType_int B p)

end GlobalTheory
end

section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory.EtaleCompletionRadical

theorem isRadical_map_of_flat {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Module.Flat A B] (I : Ideal A) (hI : I.IsRadical)
    (hfib : ∀ (P : Ideal A) [P.IsPrime], _root_.IsReduced (B ⊗[A] P.ResidueField)) :
    (I.map (algebraMap A B)).IsRadical := by
  classical
  haveI : Finite I.minimalPrimes := (Ideal.finite_minimalPrimes_of_isNoetherianRing A I).to_subtype
  haveI : Fintype I.minimalPrimes := Fintype.ofFinite _
  haveI hpr : ∀ P : I.minimalPrimes, P.1.IsPrime := fun P => P.2.1.1
  have hle : ∀ P : I.minimalPrimes, I ≤ P.1 := fun P => P.2.1.2
  let g : ∀ P : I.minimalPrimes, (A ⧸ I) →ₐ[A] P.1.ResidueField := fun P =>
    Ideal.Quotient.liftₐ I (IsScalarTower.toAlgHom A A P.1.ResidueField) (fun a ha => by
      change algebraMap A P.1.ResidueField a = 0
      exact Ideal.algebraMap_residueField_eq_zero.2 (hle P ha))
  let f : (A ⧸ I) →ₗ[A] ∀ P : I.minimalPrimes, P.1.ResidueField := LinearMap.pi fun P => (g P).toLinearMap
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine hI (Ideal.sInf_minimalPrimes (I := I) ▸ ?_)
    refine Ideal.mem_sInf.2 fun P hP => ?_
    have h0 := congrFun hy ⟨P, hP⟩
    haveI : P.IsPrime := hP.1.1
    exact Ideal.algebraMap_residueField_eq_zero.1 h0
  have hfB := Module.Flat.lTensor_preserves_injective_linearMap (M := B) f hf
  intro x ⟨n, hn⟩

  have hz : (x ⊗ₜ[A] (1 : A ⧸ I) : B ⊗[A] (A ⧸ I)) = 0 := by
    apply hfB
    rw [map_zero]
    apply (TensorProduct.piRight A A B fun P : I.minimalPrimes => P.1.ResidueField).injective
    rw [map_zero]
    funext P
    simp only [LinearMap.lTensor_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, Pi.zero_apply]
    change x ⊗ₜ[A] (g P 1) = 0
    rw [map_one]
    have hnil : IsNilpotent (x ⊗ₜ[A] (1 : P.1.ResidueField) : B ⊗[A] P.1.ResidueField) := by
      refine ⟨n, ?_⟩
      rw [Algebra.TensorProduct.tmul_pow, one_pow]
      change Algebra.TensorProduct.includeLeft (S := A) (x ^ n) = 0
      have hk : I.map (algebraMap A B) ≤ RingHom.ker
          (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := P.1.ResidueField)).toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeLeft_apply]
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
          Ideal.algebraMap_residueField_eq_zero.2 (hle P ha), TensorProduct.tmul_zero]
      exact hk hn
    exact hnil.eq_zero
  have := congrArg (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm hz
  rw [← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, AlgEquiv.symm_apply_apply, map_zero,
    Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

end GlobalTheory.EtaleCompletionRadical

namespace GlobalTheory.EtaleCompletionRadical

set_option synthInstance.maxHeartbeats 400000 in

theorem isReduced_adicCompletion_tensor_residueField (A : Type) [CommRing A] [IsLocalRing A]
    [Algebra.EssFiniteType ℤ A] (P : Ideal A) [P.IsPrime] :
    _root_.IsReduced (AdicCompletion (maximalIdeal A) A ⊗[A] P.ResidueField) := by
  have h := GlobalTheory.GeomRegFibTransport.geomRegFib_adicCompletion_of_essFiniteType_int
    GlobalTheory.qeRing_of_finiteType_int A P P.ResidueField (IntermediateField.fg_of_noetherian _)
  obtain ⟨-, hreg⟩ := h
  refine isReduced_ofLocalizationMaximal _ fun Q hQ => ?_
  haveI := hreg Q
  infer_instance

theorem isRadical_map_of_isEtaleCompletion : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (φ : A →+* R), IsAdicComplete (maximalIdeal R) R →
    IsEtaleCompletion φ → ((residue R).comp φ).FormallyUnramified → ∀ I : Ideal A, I.IsRadical →
    (I.map φ).IsRadical := by
  intro A R _ _ _ _ _ _ φ hc het hfu I hI
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  haveI := hc
  letI : Algebra A R := φ.toAlgebra
  obtain ⟨g, hg, het'⟩ := GlobalTheory.NormalBaseChange.exists_etale_of_isEtaleCompletion A R het hfu
  letI : Algebra (AdicCompletion (maximalIdeal A) A) R := g.toAlgebra
  have h1 : (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))).IsRadical :=
    isRadical_map_of_flat I hI fun P _ => isReduced_adicCompletion_tensor_residueField A P
  have h2 := GlobalTheory.EtaleReducedEq.isRadical_map_of_etale (C := R) _ h1
  rw [Ideal.map_map] at h2
  change (I.map (g.comp _)).IsRadical at h2
  rwa [hg] at h2

end GlobalTheory.EtaleCompletionRadical
end
