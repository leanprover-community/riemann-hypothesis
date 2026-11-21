import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NcardEqIffStabilizer
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberSetSubsetRayFieldStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberSetSubsetRayField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PrincipalRayPrimesSplitCompletelyWeberValuesStatement

section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.RayExistCurve

section Quadratic

variable {K : Type} [Field K] [NumberField K] {d : ℕ}

theorem norm_int_eq (h2 : Module.finrank ℚ K = 2) (hD : discr K = -d) (φ : K →+* ℂ) (a : 𝓞 K) :
    ((Algebra.norm ℤ a : ℤ) : ℝ) = ‖φ a‖ ^ 2 := by
  rw [← GlobalTheory.QuadraticZeta.norm_eq_sq h2 hD φ, ← Algebra.coe_norm_int, Rat.cast_intCast]


theorem span_isPrime (h2 : Module.finrank ℚ K = 2) (hD : discr K = -d) (φ : K →+* ℂ) {p : ℕ} (hp : p.Prime)
    {a : 𝓞 K} (ha : ‖φ a‖ ^ 2 = p) : (Ideal.span {a}).IsPrime := by
  refine Ideal.isPrime_of_irreducible_absNorm ?_
  have : Algebra.norm ℤ a = p := by
    have := (norm_int_eq h2 hD φ a).trans ha
    exact_mod_cast this
  rw [Ideal.absNorm_span_singleton, this, Int.natAbs_natCast]
  exact hp



end Quadratic

theorem ncard_congr {M R : Type} [Field M] [Field R] [NumberField M] [NumberField R] (e : M ≃+* R) (p : ℕ) :
    {v : HeightOneSpectrum (𝓞 M) | ((p : ℕ) : 𝓞 M) ∈ v.asIdeal}.ncard =
      {v : HeightOneSpectrum (𝓞 R) | ((p : ℕ) : 𝓞 R) ∈ v.asIdeal}.ncard := by
  refine Set.ncard_congr' (Equiv.subtypeEquiv
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)) fun Q => ?_)
  simp [HeightOneSpectrum.equivOfRingEquiv, HeightOneSpectrum.comap, Ideal.mem_comap]

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField in

theorem _root_.GlobalTheory.FieldSize.RayExistCurve.finrank_adjoin {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) :
    FiniteDimensional ℚ ℚ⟮r⟯ ∧ Module.finrank ℚ ℚ⟮r⟯ = 2 := by
  have hroot : aeval r (X ^ 2 + C (d : ℚ)) = 0 := by simp [hr]
  have hmon : (X ^ 2 + C (d : ℚ)).Monic := monic_X_pow_add_C _ (by norm_num)
  have hint : IsIntegral ℚ r := ⟨_, hmon, by simpa [aeval_def] using hroot⟩
  have hdeg : (X ^ 2 + C (d : ℚ)).natDegree = 2 := natDegree_X_pow_add_C
  have hirr : Irreducible (X ^ 2 + C (d : ℚ)) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]; decide
    · intro x hx
      have hx' : x ^ 2 + (d : ℚ) = 0 := by simpa using hx
      have hd' : (0 : ℚ) < d := by exact_mod_cast hd
      nlinarith [sq_nonneg x]
  have hmin : minpoly ℚ r = X ^ 2 + C (d : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmon).symm
  refine ⟨IntermediateField.adjoin.finiteDimensional hint, ?_⟩
  rw [IntermediateField.adjoin.finrank hint, hmin, hdeg]

theorem conj_eq_neg {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) : starRingEnd ℂ r = -r := by
  have h1 := congrArg Complex.re hr
  have h2 := congrArg Complex.im hr
  simp [sq] at h1 h2
  have h3 : (0 : ℝ) < d := by exact_mod_cast hd
  have h4 : r.re = 0 := by
    by_contra h
    have : r.im = 0 := mul_left_cancel₀ h (by linarith)
    rw [this] at h1
    nlinarith [mul_self_nonneg r.re]
  apply Complex.ext <;> simp [h4]

end GlobalTheory.FieldSize.RayExistCurve
end

section
set_option autoImplicit false

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.InRayAny

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField in
private theorem weberSet_subset_of_isRay_span_natCast :
    ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
      discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) →
      ∀ n : ℕ, 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R],
      _root_.GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 K)}) → _root_.GlobalTheory.FieldSize.weberSet L n ⊆ R := by
  intro K _ _ h2 hd L hL n hn R _ _ hR
  obtain ⟨hM, S, hS⟩ := _root_.GlobalTheory.WeberSplitAny.splits_completely_of_three_le K h2 hd L hL n hn
  have hn0 : 0 < n := by omega
  have hN : Ideal.absNorm (Ideal.span {(n : 𝓞 K)}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn0.ne'
  have hMR : IntermediateField.adjoin (↥K) (_root_.GlobalTheory.FieldSize.weberSet L n) ≤ R := by
    apply _root_.GlobalTheory.Bauer.le_of_finite_split_not_split (↥K) ℂ R _
    refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K)
      (S.sup id + Ideal.absNorm (Ideal.span {(n : 𝓞 K)}))).preimage
      (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro 𝔭 ⟨hp, hsplit, hnot⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    by_cases hpS : Ideal.absNorm 𝔭.asIdeal ∈ S
    · exact le_add_right (Finset.le_sup (f := id) hpS)
    by_cases hn𝔭 : (n : 𝓞 K) ∈ 𝔭.asIdeal
    · refine le_add_left (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) ?_)
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hn𝔭)
    · exfalso
      obtain ⟨π, hπ, hπ1⟩ :=
        (_root_.GlobalTheory.FieldSize.RaySplit.ncard_eq_finrank_iff (↥K) (↥R) n hn0 hR 𝔭 hn𝔭).mp hsplit
      apply hnot
      rw [hπ] at hp hpS ⊢
      exact hS π _ hp hpS rfl hπ1
  exact fun x hx => hMR (IntermediateField.subset_adjoin _ _ hx)

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField in

theorem _root_.GlobalTheory.FieldSize.InRayAny.weberSet_subset :
    ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
      discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) →
      ∀ n : ℕ, 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R],
      _root_.GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 K)}) → _root_.GlobalTheory.FieldSize.weberSet L n ⊆ R :=
  weberSet_subset_of_isRay_span_natCast

end GlobalTheory.FieldSize.InRayAny
end

section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weberInvariantTorsionValues_subset_rayClassField : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R], IsRay R (Ideal.span {(n : 𝓞 K)}) → weberSet L n ⊆ R := by
  first | exact @GlobalTheory.FieldSize.InRayAny.weberSet_subset | exact GlobalTheory.FieldSize.InRayAny.weberSet_subset | (intros; apply GlobalTheory.FieldSize.InRayAny.weberSet_subset <;> assumption)
end

section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize GlobalTheory.FieldSize.RayExistCurve
open scoped IntermediateField

namespace GlobalTheory.FieldSize.RayExistCurveAny


end GlobalTheory.FieldSize.RayExistCurveAny
end
