import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalRingMapIndEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingOfMonicPolynomialsHaveRoo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsolutelyIntegrallyClosedDomainTateTwistAcyclicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveEtaleCohomologicalDimensionLeOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyIndEtaleBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIffIntegrallyClosedAlgCStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatMapMaximalIdealIsSeparable

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem acyc_polynomial_of_isAlgClosed : ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [IsAlgClosed K],
    IsUnit (q : K) → Acyc q (sp (Polynomial K)) := by
  intro q _ K _ _ hq n i hn
  have hqA : IsUnit (q : Polynomial K) := by
    simpa using hq.map (Polynomial.C : K →+* Polynomial K)
  by_cases h2 : 2 ≤ n
  · exact GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one q K (Polynomial K) hq n i h2
  · have hn1 : n = 1 := by omega
    subst hn1
    have hζ : ∃ ζ : Polynomial K, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
      have hdeg : (Polynomial.cyclotomic q K).degree ≠ 0 := by
        rw [Polynomial.degree_cyclotomic]
        have := Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
        exact_mod_cast this.ne'
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
      refine ⟨Polynomial.C z, ?_⟩
      have hz' : Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
        exact hz
      have hC : Polynomial.C z = algebraMap K (Polynomial K) z := rfl
      rw [hC, Polynomial.aeval_algebraMap_apply, hz', map_zero]
    obtain ⟨e⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q (Polynomial K) hqA hζ 1 i 1
    have hs : Subsingleton (Ht q (sp (Polynomial K)) 1 1) := by
      refine GlobalTheory.T.kummer_etale_vanishing q (Polynomial K) hqA ?_ ?_
      · intro u
        obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 u.isUnit
        obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq r (Nat.pos_of_ne_zero (NeZero.ne q))
        have hv0 : v ≠ 0 := by
          rintro rfl
          rw [zero_pow (NeZero.ne q)] at hv
          exact hr.ne_zero hv.symm
        refine ⟨Units.map (Polynomial.C : K →+* Polynomial K).toMonoidHom (Units.mk0 v hv0), ?_⟩
        ext
        simp [← hru, ← hv]
      · intro c _
        exact Subsingleton.elim _ _
    exact e.toEquiv.subsingleton

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistAcyclic_spectrum_polynomial_of_isAlgClosed : ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [IsAlgClosed K], IsUnit (q : K) → Acyc q (sp (Polynomial K)) := by
  first | (exact @GlobalTheory.EtC.acyc_polynomial_of_isAlgClosed) | (exact GlobalTheory.EtC.acyc_polynomial_of_isAlgClosed) | (intros; apply GlobalTheory.EtC.acyc_polynomial_of_isAlgClosed  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.HtpyLine

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap]
  rw [← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]

theorem pull_bijective_of_ringEquiv {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (F : Shv R) (n : ℤ) : Function.Bijective (pull R (spMap (e : A →+* B)) F n) := by
  have h1 : spMap (e.symm : B →+* A) ≫ spMap (e : A →+* B) = 𝟙 _ := by
    rw [← spMap_comp, ← spMap_id]
    congr 1
    ext x
    simp
  have h2 : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 _ := by
    rw [← spMap_comp, ← spMap_id]
    congr 1
    ext x
    simp
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (spMap (e.symm : B →+* A)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, h1, pull_id]
  · rw [← pull_comp, h2, pull_id]

theorem bijective_of_subsingleton {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Subsingleton M] [Subsingleton N]
    (f : M →+ N) : Function.Bijective f :=
  ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

end GlobalTheory.EtC.HtpyLine

namespace GlobalTheory.EtC.HtpyLine

open Polynomial

theorem exists_cyclotomic_root_of_AIC (q : ℕ) [NeZero q] (T : Type) [CommRing T] [Nontrivial T] (hA : AIC T) :
    ∃ ζ : T, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  obtain ⟨a, ha⟩ := hA (cyclotomic q T) (cyclotomic.monic q T)
    (by rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q))
  refine ⟨a, ?_⟩
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
  exact ha

theorem htpy_AIC : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
    ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : T →+* Polynomial T)) (tw q i) := by
  intro q _ T _ _ _ hA hq i n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · haveI := (GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)).1 (sp T) n hn
    haveI := (GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)).1 (sp (Polynomial T)) n hn
    exact bijective_of_subsingleton _
  · exact GlobalTheory.T.h_zero_pullback_twist_bijective q T (Polynomial T) Polynomial.C hq (exists_cyclotomic_root_of_AIC q T hA) inferInstance
      (fun e he => IsIdempotentElem.iff_eq_zero_or_one.mp he) (fun e he => IsIdempotentElem.iff_eq_zero_or_one.mp he) i
  · haveI hT : Subsingleton (Ht q (sp T) n i) := GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic q T hA hq n i hn
    haveI : IsAlgClosed (FractionRing T) := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hA
    have hqK : IsUnit (q : FractionRing T) := by simpa using hq.map (algebraMap T (FractionRing T))
    haveI hKt : Subsingleton (Ht q (sp (Polynomial (FractionRing T))) n i) := GlobalTheory.T.tateTwistAcyclic_spectrum_polynomial_of_isAlgClosed q (FractionRing T) hqK n i hn
    let e : TensorProduct T (FractionRing T) (Polynomial T) ≃+* Polynomial (FractionRing T) :=
      (polyEquivTensor T (FractionRing T)).symm.toRingEquiv
    haveI hTens : Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) (Polynomial T))) n i) :=
      (pull_bijective_of_ringEquiv e (tw q i) n).1.subsingleton
    have hC3 := GlobalTheory.T.etale_cohomology_ind_etale_base_change q T hA hq (Polynomial T) i n
    haveI : Subsingleton (Ht q (sp (Polynomial T)) n i) := hC3.1.subsingleton
    exact bijective_of_subsingleton _

end GlobalTheory.EtC.HtpyLine
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariance_absIntClosedLocalDomain : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : T →+* Polynomial T)) (tw q i) := by
  first | (exact @GlobalTheory.EtC.HtpyLine.htpy_AIC) | (exact GlobalTheory.EtC.HtpyLine.htpy_AIC) | (intros; apply GlobalTheory.EtC.HtpyLine.htpy_AIC  <;> assumption)
end

section
open GlobalTheory.EtC

open TensorProduct

namespace GlobalTheory

theorem isAlgClosed_fractionRing_atPrime_of_etale : ∀ (T E : Type) [CommRing T] [IsDomain T]
    [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime]
    [IsDomain (Localization.AtPrime P)],
    IsAlgClosed (FractionRing T) → IsAlgClosed (FractionRing (Localization.AtPrime P)) := by
  intro T E _ _ _ _ _ P _ _ hK
  haveI : Module.Flat T (Localization.AtPrime P) := Module.Flat.trans T E (Localization.AtPrime P)
  have hTEp : Function.Injective (algebraMap T (Localization.AtPrime P)) := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    by_contra h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := (Localization.AtPrime P))
      (mem_nonZeroDivisors_of_ne_zero h0)
    apply one_ne_zero (α := (Localization.AtPrime P))
    apply hreg
    simp [Algebra.smul_def, ht]
  have hTL : Function.Injective (algebraMap T (FractionRing (Localization.AtPrime P))) := by
    rw [IsScalarTower.algebraMap_eq T (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))]
    exact (IsFractionRing.injective (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))).comp hTEp
  haveI : FaithfulSMul T (FractionRing (Localization.AtPrime P)) := (faithfulSMul_iff_algebraMap_injective T (FractionRing (Localization.AtPrime P))).2 hTL
  letI : Algebra (FractionRing T) (FractionRing (Localization.AtPrime P)) := FractionRing.liftAlgebra T (FractionRing (Localization.AtPrime P))
  haveI : IsScalarTower T (FractionRing T) (FractionRing (Localization.AtPrime P)) := FractionRing.isScalarTower_liftAlgebra T (FractionRing (Localization.AtPrime P))
  haveI : Module.Finite (FractionRing T) ((FractionRing T) ⊗[T] E) := Algebra.FormallyUnramified.finite_of_free (FractionRing T) ((FractionRing T) ⊗[T] E)
  let φ : (FractionRing T) ⊗[T] E →ₐ[(FractionRing T)] (FractionRing (Localization.AtPrime P)) := Algebra.TensorProduct.lift (Algebra.ofId (FractionRing T) (FractionRing (Localization.AtPrime P)))
    (IsScalarTower.toAlgHom T E (FractionRing (Localization.AtPrime P))) (fun _ _ => Commute.all _ _)
  have hE : ∀ e : E, IsIntegral (FractionRing T) (algebraMap E (FractionRing (Localization.AtPrime P)) e) := by
    intro e
    have h1 : IsIntegral (FractionRing T) ((1 : (FractionRing T)) ⊗ₜ[T] e) := Algebra.IsIntegral.isIntegral _
    have h2 := h1.map φ
    simpa [φ] using h2
  have hEp : ∀ x : (Localization.AtPrime P), algebraMap (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) x ∈ algebraicClosure (FractionRing T) (FractionRing (Localization.AtPrime P)) := by
    intro x
    obtain ⟨⟨e, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    have hs : algebraMap E (FractionRing (Localization.AtPrime P)) s ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)))).2
        (IsLocalization.map_units (Localization.AtPrime P) s).ne_zero
    have heq : algebraMap (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) (IsLocalization.mk' (Localization.AtPrime P) e s) =
        algebraMap E (FractionRing (Localization.AtPrime P)) e / algebraMap E (FractionRing (Localization.AtPrime P)) s := by
      rw [eq_div_iff hs, IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) e,
        IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) (s : E), ← map_mul, IsLocalization.mk'_spec]
    simp only at heq ⊢
    rw [heq]
    exact div_mem (mem_algebraicClosure_iff.2 (hE e).isAlgebraic)
      (mem_algebraicClosure_iff.2 (hE s).isAlgebraic)
  have hL : (algebraMap (FractionRing T) (FractionRing (Localization.AtPrime P))).IsIntegral := by
    intro z
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (Localization.AtPrime P) z
    exact (mem_algebraicClosure_iff.1 (div_mem (hEp x) (hEp y))).isIntegral
  haveI := hK
  exact IsAlgClosed.of_ringEquiv (FractionRing T) (FractionRing (Localization.AtPrime P))
    (RingEquiv.ofBijective (algebraMap (FractionRing T) (FractionRing (Localization.AtPrime P))) (IsAlgClosed.ringHom_bijective_of_isIntegral _ hL))

end GlobalTheory
end

section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgClosed_fractionRing_atPrime_of_etale' : ∀ (T E : Type) [CommRing T] [IsDomain T] [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime] [IsDomain (Localization.AtPrime P)], IsAlgClosed (FractionRing T) → IsAlgClosed (FractionRing (Localization.AtPrime P)) := by
  first | (exact @GlobalTheory.isAlgClosed_fractionRing_atPrime_of_etale) | (exact GlobalTheory.isAlgClosed_fractionRing_atPrime_of_etale) | (intros; apply GlobalTheory.isAlgClosed_fractionRing_atPrime_of_etale  <;> assumption)
end

section
open GlobalTheory.EtC

namespace GlobalTheory.LocalIndEtAIC

open Polynomial IsLocalRing

theorem lift_atComap {W O : Type} [CommRing W] [CommRing O] [IsLocalRing O] (v : W →+* O) :
    ∃ φ : Localization.AtPrime ((maximalIdeal O).comap v) →+* O,
      ∀ w, φ (algebraMap W _ w) = v w := by
  have hu : ∀ y : ((maximalIdeal O).comap v).primeCompl, IsUnit (v y) := fun y => by
    by_contra hy
    exact y.2 hy
  exact ⟨IsLocalization.lift hu, fun w => IsLocalization.lift_eq hu w⟩

theorem isDomain_aic_of_indEt : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O],
    IndEt T O → (∀ (E : Type) [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime],
      IsDomain (Localization.AtPrime P) ∧ AIC (Localization.AtPrime P)) → IsDomain O ∧ AIC O := by
  intro T O _ _ _ _ h hE
  have hdom : IsDomain O := by
    refine @NoZeroDivisors.to_isDomain O _ _ ⟨fun {x y} hxy => ?_⟩
    let I : Ideal (MvPolynomial (Fin 2) T) := Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
    haveI : Algebra.FinitePresentation T (MvPolynomial (Fin 2) T ⧸ I) :=
      Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
    let g : (MvPolynomial (Fin 2) T ⧸ I) →ₐ[T] O :=
      Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![x, y]) (by
        intro a ha
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        simp [hxy])
    obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h g
    let w : Fin 2 → W := fun i => u (Ideal.Quotient.mkₐ T I (MvPolynomial.X i))
    have hw : ∀ i, v (w i) = ![x, y] i := fun i => by
      have := DFunLike.congr_fun huv (Ideal.Quotient.mkₐ T I (MvPolynomial.X i))
      exact this.trans (MvPolynomial.aeval_X _ i)
    have h0 : w 0 * w 1 = 0 := by
      have : Ideal.Quotient.mkₐ T I (MvPolynomial.X 0) * Ideal.Quotient.mkₐ T I (MvPolynomial.X 1) = 0 := by
        rw [← map_mul]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      simp only [w, ← map_mul, this, map_zero]
    obtain ⟨φ, hφ⟩ := lift_atComap (v : W →+* O)
    haveI := (hE W ((maximalIdeal O).comap (v : W →+* O))).1
    have hm : algebraMap W (Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))) (w 0) *
        algebraMap W _ (w 1) = 0 := by rw [← map_mul, h0, map_zero]
    rcases mul_eq_zero.mp hm with h1 | h1
    · left
      have e := hφ (w 0)
      rw [h1, map_zero] at e
      have := hw 0
      simp only [AlgHom.coe_toRingHom] at e
      rw [← e] at this
      simpa using this.symm
    · right
      have e := hφ (w 1)
      rw [h1, map_zero] at e
      have := hw 1
      simp only [AlgHom.coe_toRingHom] at e
      rw [← e] at this
      simpa using this.symm
  refine ⟨hdom, ?_⟩
  intro p hpm hdeg
  set n := p.natDegree with hn
  let g : MvPolynomial (Fin n) T →ₐ[T] O := MvPolynomial.aeval (fun i => p.coeff i)
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h g
  let c : Fin n → W := fun i => u (MvPolynomial.X i)
  have hc : ∀ i, v (c i) = p.coeff i := fun i => by
    have := DFunLike.congr_fun huv (MvPolynomial.X i)
    exact this.trans (MvPolynomial.aeval_X _ i)
  let p' : W[X] := X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)
  have hp'm : p'.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hp' : p'.map (v : W →+* O) = p := by
    conv_rhs => rw [hpm.as_sum]
    simp only [p', Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C]
    rw [← Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]
    simp [hc]
    rfl
  have hp'd : p'.natDegree = n := by
    have e1 := hp'm.natDegree_map (v : W →+* O)
    rw [hp'] at e1
    rw [← e1]
  obtain ⟨φ, hφ⟩ := lift_atComap (v : W →+* O)
  set L := Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))
  haveI := (hE W ((maximalIdeal O).comap (v : W →+* O))).1
  have hL := (hE W ((maximalIdeal O).comap (v : W →+* O))).2
  have hmL : (p'.map (algebraMap W L)).Monic := hp'm.map _
  have hdL : 0 < (p'.map (algebraMap W L)).natDegree := by
    rw [hp'm.natDegree_map, hp'd]; exact hdeg
  obtain ⟨r, hr⟩ := hL _ hmL hdL
  refine ⟨φ r, ?_⟩
  have hcomp : φ.comp (algebraMap W L) = (v : W →+* O) := RingHom.ext hφ
  have hpL : p = (p'.map (algebraMap W L)).map φ := by rw [Polynomial.map_map, hcomp, hp']
  rw [hpL, Polynomial.eval_map, Polynomial.eval₂_at_apply, hr, map_zero]

end GlobalTheory.LocalIndEtAIC
end

section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_monicRoots_of_isIndEtale_local : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O], IndEt T O → (∀ (E : Type) [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ AIC (Localization.AtPrime P)) → IsDomain O ∧ AIC O := by
  first | (exact @GlobalTheory.LocalIndEtAIC.isDomain_aic_of_indEt) | (exact GlobalTheory.LocalIndEtAIC.isDomain_aic_of_indEt) | (intros; apply GlobalTheory.LocalIndEtAIC.isDomain_aic_of_indEt  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.HInvAic

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap]
  rw [← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]

theorem eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : _ → _) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [this]
  exact (hf n).comp (hg n)

theorem eqv_spMap_equiv {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (F : Shv R) :
    Eqv R (spMap (e : A →+* B)) F := by
  intro n
  have h1 : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 _ := by
    rw [← spMap_comp]; convert spMap_id B; ext x; simp
  have h2 : spMap (e.symm : B →+* A) ≫ spMap (e : A →+* B) = 𝟙 _ := by
    rw [← spMap_comp]; convert spMap_id A; ext x; simp
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (spMap (e.symm : B →+* A)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, h2, pull_id]
  · rw [← pull_comp, h1, pull_id]

end GlobalTheory.HInvAic

namespace GlobalTheory.HInvAic

theorem alg (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O] :
    AIC T → SH O → IndEt T O → IsDomain O ∧ AIC O := by
  intro hT hSH hInd
  obtain ⟨hH, -⟩ := hSH
  obtain ⟨-, hac⟩ := (GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed T).1 hT
  haveI : IsIntegrallyClosed T := ((GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed T).1 hT).1
  refine GlobalTheory.T.isDomain_monicRoots_of_isIndEtale_local T O hInd ?_
  intro E _ _ _ P _
  obtain ⟨hd, hc⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale T P (Localization.AtPrime P)
  exact ⟨hd, (GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed _).2 ⟨hc, GlobalTheory.T.isAlgClosed_fractionRing_atPrime_of_etale' T E P hac⟩⟩
end GlobalTheory.HInvAic

namespace GlobalTheory.HInvAic

theorem tensor_map_eq (T O : Type) [CommRing T] [CommRing O] [Algebra T O] :
    (Algebra.TensorProduct.map (AlgHom.id T O) (Algebra.ofId T (Polynomial T))).toRingHom =
      (((polyEquivTensor T O).toRingEquiv : Polynomial O →+* O ⊗[T] Polynomial T).comp Polynomial.C).comp
        ((Algebra.TensorProduct.rid T T O).toRingEquiv : O ⊗[T] T →+* O) := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o t =>
    simp only [RingHom.comp_apply, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv,
      Algebra.TensorProduct.rid_tmul, polyEquivTensor_apply, Polynomial.eval₂_C]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.ofId_apply, Polynomial.algebraMap_eq]
    rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one, Polynomial.algebraMap_eq]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem main : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T], AIC T → IsUnit (q : T) → HInv q T := by
  intro q _ T _ _ hT hq i
  have hφ : ((Algebra.ofId T (Polynomial T)).toRingHom : T →+* Polynomial T) = Polynomial.C := by
    ext x <;> simp [Algebra.ofId_apply]
  rw [← hφ]
  refine GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) T T (Polynomial T) (Algebra.ofId T (Polynomial T)) ?_
  intro O _ _ hSH hInd
  obtain ⟨hdom, haic⟩ := alg T O hT hSH hInd
  obtain ⟨hH, -⟩ := hSH
  have hqO : IsUnit (q : O) := by simpa using hq.map (algebraMap T O)
  have hC := GlobalTheory.T.etaleHomotopyInvariance_absIntClosedLocalDomain q O haic hqO i
  rw [tensor_map_eq, spMap_comp, spMap_comp]
  exact eqv_comp _ _ _ (eqv_comp _ _ _ (eqv_spMap_equiv _ _) hC) (eqv_spMap_equiv _ _)

end GlobalTheory.HInvAic
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariance_absolutelyIntegrallyClosed : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T], AIC T → IsUnit (q : T) → HInv q T := by
  first | (exact @GlobalTheory.HInvAic.main) | (exact GlobalTheory.HInvAic.main) | (intros; apply GlobalTheory.HInvAic.main  <;> assumption)
end
